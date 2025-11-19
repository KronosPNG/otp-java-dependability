package com.bastiaanjansen.otp.server.dto;

public class HOTPGenerateRequest {
    private byte[] secret;
    private long counter;
    private String algorithm;
    private int passwordLength;
    
    public HOTPGenerateRequest() {}
    
    public byte[] getSecret() {
        return secret;
    }
    
    public void setSecret(byte[] secret) {
        this.secret = secret;
    }
    
    public long getCounter() {
        return counter;
    }
    
    public void setCounter(long counter) {
        this.counter = counter;
    }
    
    public String getAlgorithm() {
        return algorithm;
    }
    
    public void setAlgorithm(String algorithm) {
        this.algorithm = algorithm;
    }
    
    public int getPasswordLength() {
        return passwordLength;
    }
    
    public void setPasswordLength(int passwordLength) {
        this.passwordLength = passwordLength;
    }
}
