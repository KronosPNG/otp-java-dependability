package com.bastiaanjansen.otp.server.dto;

import org.apache.commons.codec.binary.Base32;

public class SecretResponse {
    private String secret;
    private String secretBase32;
    
    public SecretResponse() {}
    
    public SecretResponse(byte[] secret) {
        Base32 base32 = new Base32();
        this.secret = bytesToHex(secret);
        this.secretBase32 = base32.encodeToString(secret);
    }
    
    public String getSecret() {
        return secret;
    }
    
    public void setSecret(String secret) {
        this.secret = secret;
    }
    
    public String getSecretBase32() {
        return secretBase32;
    }
    
    public void setSecretBase32(String secretBase32) {
        this.secretBase32 = secretBase32;
    }
    
    private static String bytesToHex(byte[] bytes) {
        StringBuilder sb = new StringBuilder();
        for (byte b : bytes) {
            sb.append(String.format("%02x", b));
        }
        return sb.toString();
    }
}
