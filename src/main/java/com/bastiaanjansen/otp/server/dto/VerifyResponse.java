package com.bastiaanjansen.otp.server.dto;

public class VerifyResponse {
    private boolean valid;
    
    public VerifyResponse() {}
    
    public VerifyResponse(boolean valid) {
        this.valid = valid;
    }
    
    public boolean isValid() {
        return valid;
    }
    
    public void setValid(boolean valid) {
        this.valid = valid;
    }
}
