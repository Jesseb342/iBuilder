/* The signing engine's adapter: zsign (https://github.com/zhlynn/zsign, MIT), through its own C++ API.
 *
 * This is the only file that knows zsign. It compiles to a real signer only when NXPOCKET_WITH_ZSIGN is defined,
 * which is what tools/build_zsign.sh does once it has built the library; without it the app imports and verifies
 * games and refuses to sign one, rather than leaving behind a framework iOS would reject.
 *
 * Written against zsign's own headers rather than against a wrapper. LiveContainer's ZSign/ directory implements the
 * same API, but that repository is AGPL-3.0, so none of it is used here (see NOTICE).
 */
#include "inapp_shim.h"

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>
#include <set>
#include <string>

#if defined(NXPOCKET_WITH_ZSIGN)

#include "common/sha.h"
#include "common/fs.h"
#include "macho.h"
#include "openssl.h"

#include <openssl/evp.h>
#include <openssl/pkcs12.h>
#include <openssl/provider.h>
#include <openssl/x509.h>
#include <openssl/cms.h>
#include <CoreFoundation/CoreFoundation.h>

namespace {

void fail(char *error, int length, const char *message) {
    if (error && length > 0) snprintf(error, static_cast<size_t>(length), "%s", message);
}

bool present(const char *value) { return value && *value; }

std::string cfString(CFTypeRef value) {
    if (!value || CFGetTypeID(value) != CFStringGetTypeID()) return {};
    CFStringRef string = static_cast<CFStringRef>(value);
    CFIndex length = CFStringGetLength(string);
    CFIndex capacity = CFStringGetMaximumSizeForEncoding(length, kCFStringEncodingUTF8) + 1;
    if (capacity <= 1 || capacity > 4096) return {};
    std::string result(static_cast<size_t>(capacity), '\0');
    if (!CFStringGetCString(string, &result[0], capacity, kCFStringEncodingUTF8)) return {};
    result.resize(strlen(result.c_str()));
    return result;
}

bool appIdentifierMatches(const std::string &profileIdentifier, const std::string &team,
                          const std::string &bundleIdentifier) {
    const std::string prefix = team + ".";
    if (profileIdentifier.compare(0, prefix.size(), prefix) != 0) return false;
    const std::string pattern = profileIdentifier.substr(prefix.size());
    const size_t wildcard = pattern.find('*');
    if (wildcard == std::string::npos) return pattern == bundleIdentifier;
    if (wildcard != pattern.size() - 1) return false;
    return bundleIdentifier.compare(0, wildcard, pattern, 0, wildcard) == 0;
}

// Validate the exact identity/profile pair before asking zsign to produce a signature. A successful zsign return
// only means that it wrote a signature; iOS still rejects it if the leaf certificate is not authorized by this
// app's embedded profile. No certificate, key, password, Team ID, or profile contents are logged.
bool validateIdentityProfile(const std::string &p12Bytes, const char *passphrase,
                             const std::string &provisionBytes, const char *bundleIdentifier,
                             std::string &reason) {
    static OSSL_PROVIDER *defaultProvider = OSSL_PROVIDER_load(NULL, "default");
    static OSSL_PROVIDER *legacyProvider = OSSL_PROVIDER_load(NULL, "legacy");
    (void)defaultProvider; (void)legacyProvider;

    const unsigned char *p12Cursor = reinterpret_cast<const unsigned char *>(p12Bytes.data());
    PKCS12 *p12 = d2i_PKCS12(NULL, &p12Cursor, static_cast<long>(p12Bytes.size()));
    if (!p12) { reason = "certificate/profile check: the stored .p12 could not be decoded"; return false; }
    EVP_PKEY *privateKey = NULL;
    X509 *leaf = NULL;
    STACK_OF(X509) *chain = NULL;
    const bool parsed = PKCS12_parse(p12, passphrase ? passphrase : "", &privateKey, &leaf, &chain) == 1;
    PKCS12_free(p12);
    if (!parsed || !privateKey || !leaf) {
        EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
        reason = "certificate/profile check: the .p12 did not yield a certificate and private key";
        return false;
    }
    if (X509_check_private_key(leaf, privateKey) != 1) {
        EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
        reason = "certificate/profile check: the .p12 certificate does not match its private key";
        return false;
    }
    const int notBefore = X509_cmp_current_time(X509_get0_notBefore(leaf));
    const int notAfter = X509_cmp_current_time(X509_get0_notAfter(leaf));
    if (notBefore == 0 || notAfter == 0 || notBefore > 0 || notAfter < 0) {
        EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
        reason = "certificate/profile check: the signing certificate is not currently valid";
        return false;
    }

    BIO *bio = BIO_new_mem_buf(provisionBytes.data(), static_cast<int>(provisionBytes.size()));
    CMS_ContentInfo *cms = bio ? d2i_CMS_bio(bio, NULL) : NULL;
    BIO_free(bio);
    ASN1_OCTET_STRING **content = cms ? CMS_get0_content(cms) : NULL;
    if (!content || !*content || ASN1_STRING_length(*content) <= 0) {
        CMS_ContentInfo_free(cms);
        EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
        reason = "certificate/profile check: embedded.mobileprovision is not a readable CMS profile";
        return false;
    }
    CFDataRef plistData = CFDataCreate(kCFAllocatorDefault, ASN1_STRING_get0_data(*content),
                                       ASN1_STRING_length(*content));
    CMS_ContentInfo_free(cms);
    CFPropertyListRef plist = plistData ? CFPropertyListCreateWithData(kCFAllocatorDefault, plistData,
        kCFPropertyListImmutable, NULL, NULL) : NULL;
    if (plistData) CFRelease(plistData);
    if (!plist || CFGetTypeID(plist) != CFDictionaryGetTypeID()) {
        if (plist) CFRelease(plist);
        EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
        reason = "certificate/profile check: the provisioning profile payload is not a property list";
        return false;
    }
    CFDictionaryRef profile = static_cast<CFDictionaryRef>(plist);
    CFArrayRef developerCertificates = static_cast<CFArrayRef>(CFDictionaryGetValue(profile, CFSTR("DeveloperCertificates")));
    int leafLength = i2d_X509(leaf, NULL);
    std::string leafDER;
    if (leafLength > 0) {
        leafDER.resize(static_cast<size_t>(leafLength));
        unsigned char *out = reinterpret_cast<unsigned char *>(&leafDER[0]);
        i2d_X509(leaf, &out);
    }
    bool certificateAuthorized = false;
    if (developerCertificates && CFGetTypeID(developerCertificates) == CFArrayGetTypeID()) {
        for (CFIndex i = 0; i < CFArrayGetCount(developerCertificates); ++i) {
            CFTypeRef item = CFArrayGetValueAtIndex(developerCertificates, i);
            if (item && CFGetTypeID(item) == CFDataGetTypeID()) {
                CFDataRef candidate = static_cast<CFDataRef>(item);
                if (static_cast<size_t>(CFDataGetLength(candidate)) == leafDER.size() &&
                    memcmp(CFDataGetBytePtr(candidate), leafDER.data(), leafDER.size()) == 0) {
                    certificateAuthorized = true;
                    break;
                }
            }
        }
    }
    if (!certificateAuthorized) {
        CFRelease(plist);
        EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
        reason = "certificate/profile check: this .p12 certificate is not listed in the app's embedded provisioning profile";
        return false;
    }

    CFDateRef expiration = static_cast<CFDateRef>(CFDictionaryGetValue(profile, CFSTR("ExpirationDate")));
    if (!expiration || CFGetTypeID(expiration) != CFDateGetTypeID() ||
        CFDateGetAbsoluteTime(expiration) <= CFAbsoluteTimeGetCurrent()) {
        CFRelease(plist);
        EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
        reason = "certificate/profile check: the embedded provisioning profile is expired or has no expiration date";
        return false;
    }

    CFArrayRef teams = static_cast<CFArrayRef>(CFDictionaryGetValue(profile, CFSTR("TeamIdentifier")));
    std::string team;
    if (teams && CFGetTypeID(teams) == CFArrayGetTypeID() && CFArrayGetCount(teams) > 0)
        team = cfString(CFArrayGetValueAtIndex(teams, 0));
    CFDictionaryRef entitlements = static_cast<CFDictionaryRef>(CFDictionaryGetValue(profile, CFSTR("Entitlements")));
    CFTypeRef appIdentifierValue = (entitlements && CFGetTypeID(entitlements) == CFDictionaryGetTypeID())
        ? CFDictionaryGetValue(entitlements, CFSTR("application-identifier")) : NULL;
    const std::string appIdentifier = cfString(appIdentifierValue);
    if (team.empty() || !appIdentifierMatches(appIdentifier, team, bundleIdentifier ? bundleIdentifier : "")) {
        CFRelease(plist);
        EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
        reason = "certificate/profile check: the profile's Team ID or application-identifier does not authorize this iBuilder app";
        return false;
    }
    CFTypeRef entitlementTeam = (entitlements && CFGetTypeID(entitlements) == CFDictionaryGetTypeID())
        ? CFDictionaryGetValue(entitlements, CFSTR("com.apple.developer.team-identifier")) : NULL;
    if (entitlementTeam && cfString(entitlementTeam) != team) {
        CFRelease(plist);
        EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
        reason = "certificate/profile check: the profile's team entitlements disagree with its Team ID";
        return false;
    }

    CFRelease(plist);
    EVP_PKEY_free(privateKey); X509_free(leaf); sk_X509_pop_free(chain, X509_free);
    return true;
}

// Replaces `path` with a byte-identical copy written by write(2), under a new inode.
//
// zsign signs in place through a MAP_SHARED, PROT_WRITE mapping (ZMachO::OpenFile). The file on disk comes out
// valid, but its pages stay in the unified buffer cache marked as written through a mapping, and when the same
// process then maps the image to load it, iOS treats them as possibly altered: the second probe run had 5C's
// signature accepted by dlopen and the app killed a moment later in dyld's fixups with SIGKILL (CODESIGNING,
// "Invalid Page") on __LINKEDIT, while the very same file verified on a Mac. A fresh file never had a writable
// mapping, so the kernel validates its pages against the signature like any other.
bool rewriteAsFreshFile(const std::string &path, std::string &reason) {
    struct stat info;
    if (stat(path.c_str(), &info) != 0) {
        reason = "the signed binary is gone: " + std::string(strerror(errno));
        return false;
    }
    std::string bytes;
    if (!ZFile::ReadFile(path.c_str(), bytes) || bytes.size() != static_cast<size_t>(info.st_size)) {
        reason = "the signed binary could not be read back";
        return false;
    }
    const std::string fresh = path + ".nxpocket-fresh";
    unlink(fresh.c_str());
    int fd = open(fresh.c_str(), O_WRONLY | O_CREAT | O_EXCL, info.st_mode & 07777);
    if (fd < 0) {
        reason = "the fresh copy could not be created: " + std::string(strerror(errno));
        return false;
    }
    size_t written = 0;
    while (written < bytes.size()) {
        ssize_t n = write(fd, bytes.data() + written, bytes.size() - written);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) {
            reason = "the fresh copy could not be written: " + std::string(strerror(errno));
            close(fd);
            unlink(fresh.c_str());
            return false;
        }
        written += static_cast<size_t>(n);
    }
    if (fsync(fd) != 0 || close(fd) != 0) {
        reason = "the fresh copy could not be flushed: " + std::string(strerror(errno));
        unlink(fresh.c_str());
        return false;
    }
    if (rename(fresh.c_str(), path.c_str()) != 0) {
        reason = "the fresh copy could not replace the binary: " + std::string(strerror(errno));
        unlink(fresh.c_str());
        return false;
    }
    return true;
}

// A plist <data> element. zsign keeps digests as strings prefixed with "data:" and its plist writer turns that
// prefix into the element; writing <string>data:...</string> instead makes codesign answer "the sealed resource
// directory is invalid".
std::string data(const std::string &base64) { return "<data>" + base64 + "</data>"; }

std::string escape(const std::string &text) {
    std::string out;
    out.reserve(text.size());
    for (char c : text) {
        switch (c) {
            case '&': out += "&amp;"; break;
            case '<': out += "&lt;"; break;
            case '>': out += "&gt;"; break;
            default: out += c;
        }
    }
    return out;
}

// zsign's own rule tables, copied from ZBundle::GenerateCodeResources. A rule value of <true/> means the file must
// be sealed, a weight below 1000 means it may be left out, and 1000 or more means the path is a directory to
// descend into. They have to be written as reals: integers make codesign answer "invalid resource specification
// rule(s)", and flattening the optional/omit flags into bare numbers makes it answer the same.
const char *const kRules =
    "<key>^.*</key><true/>"
    "<key>^.*\\.lproj/</key><dict><key>optional</key><true/><key>weight</key><real>1000</real></dict>"
    "<key>^.*\\.lproj/locversion.plist$</key><dict><key>omit</key><true/><key>weight</key><real>1100</real></dict>"
    "<key>^Base\\.lproj/</key><dict><key>weight</key><real>1010</real></dict>"
    "<key>^version\\.plist$</key><true/>";

const char *const kRules2 =
    "<key>^.*</key><true/>"
    "<key>.*\\.dSYM($|/)</key><dict><key>weight</key><real>11</real></dict>"
    "<key>^(.*/)?\\.DS_Store$</key><dict><key>omit</key><true/><key>weight</key><real>2000</real></dict>"
    "<key>^.*\\.lproj/</key><dict><key>optional</key><true/><key>weight</key><real>1000</real></dict>"
    "<key>^.*\\.lproj/locversion.plist$</key><dict><key>omit</key><true/><key>weight</key><real>1100</real></dict>"
    "<key>^Base\\.lproj/</key><dict><key>weight</key><real>1010</real></dict>"
    "<key>^Info\\.plist$</key><dict><key>omit</key><true/><key>weight</key><real>20</real></dict>"
    "<key>^PkgInfo$</key><dict><key>omit</key><true/><key>weight</key><real>20</real></dict>"
    "<key>^embedded\\.provisionprofile$</key><dict><key>weight</key><real>20</real></dict>"
    "<key>^version\\.plist$</key><dict><key>weight</key><real>20</real></dict>";

bool endsWith(const std::string &text, const std::string &suffix) {
    return text.size() >= suffix.size() && text.compare(text.size() - suffix.size(), suffix.size(), suffix) == 0;
}

// Writes <framework>/_CodeSignature/CodeResources and returns the bytes it ended up with, because that is what the
// signature's resource slot covers. zsign only generates a seal for an app (GenerateCodeResources is private), yet
// codesign rejects a bundle whose signature carries a resources slot but which has no seal on disk, and a framework
// Apple signed always has one. Every file is sealed except the ones a more specific rule omits, the main executable
// (covered by the Mach-O signature) and the seal itself, which cannot cover its own hash.
bool writeCodeResources(const std::string &framework, const std::string &executableName, std::string &seal,
                        std::string &reason) {
    std::set<std::string> files;
    ZFile::EnumFolder(framework.c_str(), true, NULL, [&](bool isFolder, const std::string &path) {
        if (!isFolder) files.insert(path.substr(framework.size() + 1));
        return false;
    });
    files.erase("_CodeSignature/CodeResources");
    files.erase(executableName);

    std::string first = "<dict>";
    std::string second = "<dict>";
    for (const std::string &name : files) {
        std::string sha1, sha256;
        const std::string full = framework + "/" + name;
        if (!ZSHA::SHABase64File(full.c_str(), sha1, sha256)) {
            reason = "a framework file could not be hashed";
            return false;
        }
        const bool nested = name.find(".lproj/") != std::string::npos;
        const bool omitFirst = endsWith(name, ".lproj/locversion.plist");
        const bool omitSecond = omitFirst || endsWith(name, ".DS_Store") || name == "Info.plist" || name == "PkgInfo";
        const std::string key = "<key>" + escape(name) + "</key>";
        if (!omitFirst) {
            if (nested) {
                first += key + "<dict><key>hash</key>" + data(sha1) + "<key>optional</key><true/></dict>";
            } else {
                first += key + data(sha1);
            }
        }
        if (!omitSecond) {
            second += key + "<dict><key>hash</key>" + data(sha1) + "<key>hash2</key>" + data(sha256);
            if (nested) second += "<key>optional</key><true/>";
            second += "</dict>";
        }
    }
    first += "</dict>";
    second += "</dict>";

    const std::string plist =
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
        "<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n"
        "<plist version=\"1.0\"><dict>"
        "<key>files</key>" + first + "<key>files2</key>" + second +
        "<key>rules</key><dict>" + kRules + "</dict>"
        "<key>rules2</key><dict>" + kRules2 + "</dict>"
        "</dict></plist>\n";

    const std::string folder = framework + "/_CodeSignature";
    if (mkdir(folder.c_str(), 0755) != 0) {
        struct stat status;
        if (stat(folder.c_str(), &status) != 0 || !S_ISDIR(status.st_mode)) {
            reason = "the _CodeSignature folder could not be created";
            return false;
        }
    }
    const std::string path = folder + "/CodeResources";
    if (!ZFile::WriteFile(path.c_str(), plist)) {
        reason = "the resource seal could not be written";
        return false;
    }
    if (!ZFile::ReadFile(path.c_str(), seal) || seal.empty()) {
        reason = "the resource seal could not be read back";
        return false;
    }
    return true;
}

}  // namespace

int nxpocket_zsign_sign(const char *p12Path, const char *passphrase,
                        const char *provisionPath, const char *entitlementsPath,
                        const char *frameworkPath, const char *executableName, const char *identifier,
                        char *error, int errorLength) {
    if (!present(p12Path) || !present(provisionPath) || !present(frameworkPath)
        || !present(executableName) || !present(identifier)) {
        fail(error, errorLength, "the signing request is incomplete");
        return 1;
    }

    ZSignAsset asset;
    // A .p12 holds both the certificate and the key, and Init reads it from the *key* argument: it tries a PEM key,
    // then a DER key, then d2i_PKCS12_bio. The certificate argument is left empty because PKCS12_parse already
    // yields the certificate. bAdhoc would return before loading anything and produce an image that carries no
    // certificate at all, so it is off.
    //
    // bSHA256Only is ON, and that is not a detail. Left off, zsign writes the SHA-1 CodeDirectory in slot 0 and the
    // SHA-256 one as the alternate, which is the 32-bit layout; codesign computes the SHA-256 hash for a 64-bit
    // image and rejects the result with "code or signature have been modified". Every arm64 binary wants the
    // SHA-256 directory in slot 0.
    //
    // entitlementsPath decides what the framework's signature carries: a file replaces the profile's Entitlements
    // dict (an empty dict for none), and no file keeps the profile's, which is what iOS wants outside the bundle.
    if (!asset.Init("", p12Path, provisionPath, present(entitlementsPath) ? entitlementsPath : "",
                    passphrase ? passphrase : "",
                    /* bAdhoc */ false, /* bSHA256Only */ true, /* bSingleBinary */ false)) {
        fail(error, errorLength, "zsign refused the certificate or the provisioning profile");
        return 1;
    }
    // No entitlements file means the caller asked for the profile's own (probe 5C, DeviceSigner's .appProfile).
    // Stock zsign would still write an empty dict into a dylib, so the request needs the patched flag to mean
    // anything: patches/zsign/0001-dylib-entitlements.patch. With a file, a dylib keeps zsign's own behaviour.
    asset.m_bDylibEntitlements = !present(entitlementsPath);

    const std::string framework(frameworkPath);
    const std::string binary = framework + "/" + executableName;

    ZMachO macho;
    if (!macho.Init(binary.c_str())) {
        fail(error, errorLength, "the framework binary could not be read as a Mach-O");
        return 1;
    }

    // What zsign's own SignNode does for a bundle: hash the Info.plist on disk into the signature's info slot.
    // Empty strings make zsign fall back to the plist embedded in the Mach-O's __info_plist section.
    std::string infoSHA1;
    std::string infoSHA256;
    std::string infoPlist;
    if (ZFile::ReadFile((framework + "/Info.plist").c_str(), infoPlist) && !infoPlist.empty()) {
        ZSHA::SHA(infoPlist, infoSHA1, infoSHA256);
    }

    std::string seal;
    std::string reason;
    if (!writeCodeResources(framework, executableName, seal, reason)) {
        fail(error, errorLength, reason.c_str());
        return 1;
    }

    // Identifier: the app's own. That is the point of the whole design — the probe found iOS rejects an image
    // carrying a different signature identifier. bForce re-signs a binary that already carries a signature, which
    // is what happens after a certificate renewal.
    if (!macho.Sign(&asset, /* bForce */ true, identifier, infoSHA1, infoSHA256, seal)) {
        fail(error, errorLength, "zsign could not sign the framework binary");
        return 1;
    }
    // Sign() ends with CloseFile(), so the writable mapping is gone by now; what is left is its mark on the pages.
    if (!rewriteAsFreshFile(binary, reason)) {
        fail(error, errorLength, reason.c_str());
        return 1;
    }
    return 0;
}

int nxpocket_zsign_sign_memory(const unsigned char *p12, int p12Length, const char *passphrase,
                               const unsigned char *provision, int provisionLength,
                               const unsigned char *entitlements, int entitlementsLength,
                               const char *frameworkPath, const char *executableName, const char *identifier,
                               char *error, int errorLength) {
    if (!p12 || p12Length <= 0 || !provision || provisionLength <= 0
        || !present(frameworkPath) || !present(executableName) || !present(identifier)) {
        fail(error, errorLength, "the signing request is incomplete");
        return 1;
    }

    // Everything the signer needs is here, in memory. Nothing below writes the .p12 or the password anywhere.
    const std::string p12Data(reinterpret_cast<const char *>(p12), static_cast<size_t>(p12Length));
    const std::string provData(reinterpret_cast<const char *>(provision), static_cast<size_t>(provisionLength));
    const std::string entitleData = (entitlements && entitlementsLength > 0)
        ? std::string(reinterpret_cast<const char *>(entitlements), static_cast<size_t>(entitlementsLength))
        : std::string();

    std::string validationError;
    if (!validateIdentityProfile(p12Data, passphrase, provData, identifier, validationError)) {
        fail(error, errorLength, validationError.c_str());
        return 1;
    }

    ZSignAsset asset;
    // bSHA256Only on: an arm64 image wants the SHA-256 CodeDirectory in slot 0 (docs/SIGNING.md).
    if (!asset.InitFromMemory(p12Data, passphrase ? passphrase : "", provData, entitleData,
                              /* bSHA256Only */ true)) {
        fail(error, errorLength, "zsign refused the certificate or the provisioning profile");
        return 1;
    }
    // No entitlements buffer means the profile's own go into the framework (probe 5C, DeviceSigner's .appProfile).
    // Stock zsign still writes an empty dict into a dylib, so the request needs patches/zsign/0001's flag.
    asset.m_bDylibEntitlements = (entitlements == NULL || entitlementsLength <= 0);

    const std::string framework(frameworkPath);
    const std::string binary = framework + "/" + executableName;

    ZMachO macho;
    if (!macho.Init(binary.c_str())) {
        fail(error, errorLength, "the framework binary could not be read as a Mach-O");
        return 1;
    }

    std::string infoSHA1;
    std::string infoSHA256;
    std::string infoPlist;
    if (ZFile::ReadFile((framework + "/Info.plist").c_str(), infoPlist) && !infoPlist.empty()) {
        ZSHA::SHA(infoPlist, infoSHA1, infoSHA256);
    }

    std::string seal;
    std::string reason;
    if (!writeCodeResources(framework, executableName, seal, reason)) {
        fail(error, errorLength, reason.c_str());
        return 1;
    }

    // The app's own identifier, so iOS accepts an image outside the bundle (probe 5C).
    if (!macho.Sign(&asset, /* bForce */ true, identifier, infoSHA1, infoSHA256, seal)) {
        fail(error, errorLength, "zsign could not sign the framework binary");
        return 1;
    }
    if (!rewriteAsFreshFile(binary, reason)) {
        fail(error, errorLength, reason.c_str());
        return 1;
    }
    return 0;
}

int nxpocket_p12_certificate(const unsigned char *p12Bytes, int p12Length, const char *passphrase,
                             unsigned char *der, int derCapacity, int *derLength,
                             char *error, int errorLength) {
    if (derLength) *derLength = 0;
    if (!p12Bytes || p12Length <= 0 || !der || derCapacity <= 0 || !derLength) {
        fail(error, errorLength, "the .p12 request is incomplete");
        return NXPOCKET_P12_UNREADABLE;
    }
    // The same providers zsign's Init relies on: legacy for the RC2 and 3DES that older exports use, and default,
    // which an explicit load of any provider stops OpenSSL from loading on its own.
    static OSSL_PROVIDER *defaultProvider = OSSL_PROVIDER_load(NULL, "default");
    static OSSL_PROVIDER *legacyProvider = OSSL_PROVIDER_load(NULL, "legacy");
    (void)defaultProvider; (void)legacyProvider;

    const unsigned char *cursor = p12Bytes;
    PKCS12 *p12 = d2i_PKCS12(NULL, &cursor, p12Length);
    if (!p12) {
        fail(error, errorLength, "this file is not a .p12 the signer can decode");
        return NXPOCKET_P12_UNREADABLE;
    }
    const char *password = passphrase ? passphrase : "";
    // The MAC is checked only when there is one, as PKCS12_parse does. SideStore's export carries none: checking it
    // regardless called every password wrong, and it is also what made iOS's SecPKCS12Import answer errSecDecode.
    // An export with no password may have been made with an empty one or with none at all; try both.
    const bool hasMAC = PKCS12_mac_present(p12);
    if (hasMAC && !PKCS12_verify_mac(p12, password, -1) && !(*password == 0 && PKCS12_verify_mac(p12, NULL, 0))) {
        PKCS12_free(p12);
        fail(error, errorLength, "that password does not open this .p12");
        return NXPOCKET_P12_WRONG_PASSWORD;
    }
    EVP_PKEY *key = NULL;
    X509 *certificate = NULL;
    STACK_OF(X509) *chain = NULL;
    int parsed = PKCS12_parse(p12, password, &key, &certificate, &chain);
    PKCS12_free(p12);
    if (!parsed) {
        // Without a MAC nothing tells a wrong password from a damaged file but the decryption failing; the password
        // is by far the likelier of the two.
        if (!hasMAC) {
            fail(error, errorLength, "that password does not open this .p12 (it carries no integrity check, so a "
                                     "damaged file would look the same)");
            return NXPOCKET_P12_WRONG_PASSWORD;
        }
        fail(error, errorLength, "the .p12 opened but its contents could not be decrypted");
        return NXPOCKET_P12_UNREADABLE;
    }
    int status = 0;
    if (!certificate || !key) {
        fail(error, errorLength, "the .p12 holds no certificate with its key");
        status = NXPOCKET_P12_NO_CERTIFICATE;
    } else {
        int length = i2d_X509(certificate, NULL);
        if (length <= 0) {
            fail(error, errorLength, "the certificate could not be encoded");
            status = NXPOCKET_P12_UNREADABLE;
        } else if (length > derCapacity) {
            fail(error, errorLength, "the certificate is larger than expected");
            status = NXPOCKET_P12_TOO_LARGE;
        } else {
            unsigned char *out = der;
            i2d_X509(certificate, &out);
            *derLength = length;
        }
    }
    EVP_PKEY_free(key);
    X509_free(certificate);
    sk_X509_pop_free(chain, X509_free);
    return status;
}

int nxpocket_sign_adhoc(const char *frameworkPath, const char *executableName, const char *identifier,
                        char *error, int errorLength) {
    if (!present(frameworkPath) || !present(executableName) || !present(identifier)) {
        fail(error, errorLength, "the ad-hoc signing request is incomplete");
        return 1;
    }

    ZSignAsset asset;
    // Ad-hoc: no certificate and no provisioning profile. ZSignAsset::Init returns as soon as it sees bAdhoc, so
    // the simulator — which has neither — can still run the whole signer in this process. bSHA256Only is on for
    // the same reason it is on for the certified path: an arm64 image wants the SHA-256 CodeDirectory in slot 0.
    // m_strSubjectCN stays empty, which makes SlotBuildRequirements emit the empty requirement set (ldid's shape).
    if (!asset.Init("", "", "", "", "", /* bAdhoc */ true, /* bSHA256Only */ true, /* bSingleBinary */ false)) {
        fail(error, errorLength, "zsign refused the ad-hoc request");
        return 1;
    }

    const std::string framework(frameworkPath);
    const std::string binary = framework + "/" + executableName;

    ZMachO macho;
    if (!macho.Init(binary.c_str())) {
        fail(error, errorLength, "the framework binary could not be read as a Mach-O");
        return 1;
    }

    // The Info.plist, hashed into the signature's info slot, exactly as the certified path and zsign's own SignNode.
    std::string infoSHA1;
    std::string infoSHA256;
    std::string infoPlist;
    if (ZFile::ReadFile((framework + "/Info.plist").c_str(), infoPlist) && !infoPlist.empty()) {
        ZSHA::SHA(infoPlist, infoSHA1, infoSHA256);
    }

    // The resource seal: a framework carries one, and codesign/the kernel expect it whenever the signature
    // carries a resources slot. Same writer the certified path uses.
    std::string seal;
    std::string reason;
    if (!writeCodeResources(framework, executableName, seal, reason)) {
        fail(error, errorLength, reason.c_str());
        return 1;
    }

    // The identifier is the running app's own (the caller read it out of its own signature). bForce re-signs a
    // binary that already carries a signature, so the same call works on a fresh or an already-signed framework.
    if (!macho.Sign(&asset, /* bForce */ true, identifier, infoSHA1, infoSHA256, seal)) {
        fail(error, errorLength, "zsign could not sign the framework binary");
        return 1;
    }
    // zsign signs through a writable mapping; a fresh file with the same bytes is what the kernel will validate
    // against the signature when this same process later dlopen()s it (docs/SIGNING.md's "invalid page" trap).
    if (!rewriteAsFreshFile(binary, reason)) {
        fail(error, errorLength, reason.c_str());
        return 1;
    }
    return 0;
}

#else

/* A build without the signing engine: the app compiles, imports and verifies, and refuses to sign. */
int nxpocket_zsign_sign(const char *p12Path, const char *passphrase,
                        const char *provisionPath, const char *entitlementsPath,
                        const char *frameworkPath, const char *executableName, const char *identifier,
                        char *error, int errorLength) {
    (void)p12Path; (void)passphrase; (void)provisionPath; (void)entitlementsPath;
    (void)frameworkPath; (void)executableName; (void)identifier;
    if (error && errorLength > 0) {
        snprintf(error, static_cast<size_t>(errorLength),
                 "this build has no signing engine: run tools/build_zsign.sh and rebuild");
    }
    return 1;
}

int nxpocket_p12_certificate(const unsigned char *p12, int p12Length, const char *passphrase,
                             unsigned char *der, int derCapacity, int *derLength,
                             char *error, int errorLength) {
    (void)p12; (void)p12Length; (void)passphrase; (void)der; (void)derCapacity;
    if (derLength) *derLength = 0;
    if (error && errorLength > 0) {
        snprintf(error, static_cast<size_t>(errorLength), "this build has no signing engine to read a .p12 with");
    }
    return NXPOCKET_P12_UNREADABLE;
}

/* A build without the signing engine: the in-memory certified path refuses too. */
int nxpocket_zsign_sign_memory(const unsigned char *p12, int p12Length, const char *passphrase,
                               const unsigned char *provision, int provisionLength,
                               const unsigned char *entitlements, int entitlementsLength,
                               const char *frameworkPath, const char *executableName, const char *identifier,
                               char *error, int errorLength) {
    (void)p12; (void)p12Length; (void)passphrase; (void)provision; (void)provisionLength;
    (void)entitlements; (void)entitlementsLength; (void)frameworkPath; (void)executableName; (void)identifier;
    if (error && errorLength > 0) {
        snprintf(error, static_cast<size_t>(errorLength),
                 "this build has no signing engine: run sign/build_sign_app.sh and rebuild");
    }
    return 1;
}

/* A build without the signing engine: the ad-hoc path refuses, the same way the certified one does. */
int nxpocket_sign_adhoc(const char *frameworkPath, const char *executableName, const char *identifier,
                        char *error, int errorLength) {
    (void)frameworkPath; (void)executableName; (void)identifier;
    if (error && errorLength > 0) {
        snprintf(error, static_cast<size_t>(errorLength),
                 "this build has no signing engine: run sign/build_sign_app.sh and rebuild");
    }
    return 1;
}

#endif
