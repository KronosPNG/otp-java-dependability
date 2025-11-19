package com.bastiaanjansen.otp.server.dto;

public class OTPResponse {
    private String code;
    
    public OTPResponse() {}
    
    public OTPResponse(String code) {
        this.code = code;
    }
    
    public String getCode() {
        return code;
    }
    
    public void setCode(String code) {
        this.code = code;
    }
}
