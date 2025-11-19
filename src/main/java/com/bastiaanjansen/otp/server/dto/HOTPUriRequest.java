package com.bastiaanjansen.otp.server.dto;

public class HOTPUriRequest {
    private byte[] secret;
    private String issuer;
    private String account;
    private long initialCounter;
    private String algorithm;
    private int passwordLength;
    
    public HOTPUriRequest() {}
    
    public byte[] getSecret() {
        return secret;
    }
    
    public void setSecret(byte[] secret) {
        this.secret = secret;
    }
    
    public String getIssuer() {
        return issuer;
    }
    
    public void setIssuer(String issuer) {
        this.issuer = issuer;
    }
    
    public String getAccount() {
        return account;
    }
    
    public void setAccount(String account) {
        this.account = account;
    }
    
    public long getInitialCounter() {
        return initialCounter;
    }
    
    public void setInitialCounter(long initialCounter) {
        this.initialCounter = initialCounter;
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
