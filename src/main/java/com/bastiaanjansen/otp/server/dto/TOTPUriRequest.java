package com.bastiaanjansen.otp.server.dto;

public class TOTPUriRequest {
    private byte[] secret;
    private String issuer;
    private String account;
    private String algorithm;
    private int passwordLength;
    private int period;
    
    public TOTPUriRequest() {}
    
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
    
    public int getPeriod() {
        return period;
    }
    
    public void setPeriod(int period) {
        this.period = period;
    }
}
