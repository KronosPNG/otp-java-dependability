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

    //@ public invariant name != null;
    //@ public invariant !name.isEmpty();
    private final String name;

    //@ requires name != null;
    //@ requires !name.isEmpty();
    //@ ensures this.name.equals(name);
    HMACAlgorithm(String name) {
        this.name = name;
    }

    //@ ensures \result != null;
    //@ ensures \result.equals(name);
    //@ pure
    public String getHMACName() {
        return name;
    }
}
