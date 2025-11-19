package com.bastiaanjansen.otp.server.dto;

public class TOTPVerifyRequest {
    private byte[] secret;
    private String code;
    private String algorithm;
    private int passwordLength;
    private int period;
    private int delay;
    
    public TOTPVerifyRequest() {}
    
    public byte[] getSecret() {
        return secret;
    }
    
    public void setSecret(byte[] secret) {
        this.secret = secret;
    }
    
    public String getCode() {
        return code;
    }
    
    public void setCode(String code) {
        this.code = code;
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
    
    public int getDelay() {
        return delay;
    }
    
    public void setDelay(int delay) {
        this.delay = delay;
    }
}
