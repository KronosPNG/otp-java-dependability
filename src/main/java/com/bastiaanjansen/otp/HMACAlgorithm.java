package com.bastiaanjansen.otp;

/**
 * HMAC algorithm enum
 * @author Bastiaan Jansen
 */
public enum HMACAlgorithm {

    @Deprecated
    SHA1("HmacSHA1"),
    SHA224("HmacSHA224"),
    SHA256("HmacSHA256"),
    SHA384("HmacSHA384"),
    SHA512("HmacSHA512");

    private final /*@ spec_public @*/ String algorithmName;

    //@ private invariant algorithmName != null && algorithmName.length() > 0;
    //@ ensures this.algorithmName == algorithmName;
    HMACAlgorithm(String algorithmName) {
        this.algorithmName = algorithmName;
    }

    //@ ensures \result != null;
    //@ ensures \result.equals(algorithmName);
    //@ ensures \result.length() > 0;
    //@ assignable \nothing;
    //@ pure
    public String getHMACName() {
        return algorithmName;
    }
}
