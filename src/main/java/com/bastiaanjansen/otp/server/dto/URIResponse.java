package com.bastiaanjansen.otp.server.dto;

public class URIResponse {
    private String uri;
    
    public URIResponse() {}
    
    public URIResponse(String uri) {
        this.uri = uri;
    }
    
    public String getUri() {
        return uri;
    }
    
    public void setUri(String uri) {
        this.uri = uri;
    }
}
