package com.bastiaanjansen.otp.server;

import com.bastiaanjansen.otp.HMACAlgorithm;
import com.bastiaanjansen.otp.HOTPGenerator;
import com.bastiaanjansen.otp.SecretGenerator;
import com.bastiaanjansen.otp.TOTPGenerator;
import com.bastiaanjansen.otp.server.dto.*;
import io.javalin.Javalin;
import io.javalin.http.Context;

import java.net.URI;
import java.time.Duration;

/**
 * Lightweight REST API server for OTP generation and verification.
 * 
 * Endpoints:
 * - POST /api/secret/generate - Generate a new secret
 * - POST /api/totp/generate - Generate TOTP code
 * - POST /api/totp/verify - Verify TOTP code
 * - POST /api/hotp/generate - Generate HOTP code
 * - POST /api/hotp/verify - Verify HOTP code
 * - POST /api/uri/totp - Generate TOTP QR code URI
 * - POST /api/uri/hotp - Generate HOTP QR code URI
 */
public class OTPServer {
    
    private static final int DEFAULT_PORT = 7000;
    
    public static void main(String[] args) {
        int port = args.length > 0 ? Integer.parseInt(args[0]) : DEFAULT_PORT;
        
        Javalin app = Javalin.create(config -> {
            config.showJavalinBanner = false;
            config.http.defaultContentType = "application/json";
            config.staticFiles.add("/public");
        }).start(port);
        
        System.out.println("OTP Server started on port " + port);
        System.out.println("Web UI available at http://localhost:" + port);
        
        // Secret generation endpoint
        app.post("/api/secret/generate", OTPServer::generateSecret);
        
        // TOTP endpoints
        app.post("/api/totp/generate", OTPServer::generateTOTP);
        app.post("/api/totp/verify", OTPServer::verifyTOTP);
        app.post("/api/uri/totp", OTPServer::generateTOTPUri);
        
        // HOTP endpoints
        app.post("/api/hotp/generate", OTPServer::generateHOTP);
        app.post("/api/hotp/verify", OTPServer::verifyHOTP);
        app.post("/api/uri/hotp", OTPServer::generateHOTPUri);
        
        // Health check
        app.get("/health", ctx -> ctx.json(new HealthResponse("OK")));
    }
    
    private static void generateSecret(Context ctx) {
        try {
            SecretRequest request = ctx.bodyAsClass(SecretRequest.class);
            byte[] secret;
            
            if (request.getLength() > 0) {
                secret = SecretGenerator.generate(request.getLength());
            } else {
                secret = SecretGenerator.generate();
            }
            
            ctx.json(new SecretResponse(secret));
        } catch (Exception e) {
            ctx.status(400).json(new ErrorResponse(e.getMessage()));
        }
    }
    
    private static void generateTOTP(Context ctx) {
        try {
            TOTPGenerateRequest request = ctx.bodyAsClass(TOTPGenerateRequest.class);
            
            TOTPGenerator.Builder builder = new TOTPGenerator.Builder(request.getSecret());
            
            if (request.getAlgorithm() != null) {
                builder.withHOTPGenerator(b -> b.withAlgorithm(HMACAlgorithm.valueOf(request.getAlgorithm())));
            }
            if (request.getPasswordLength() > 0) {
                builder.withHOTPGenerator(b -> b.withPasswordLength(request.getPasswordLength()));
            }
            if (request.getPeriod() > 0) {
                builder.withPeriod(Duration.ofSeconds(request.getPeriod()));
            }
            
            TOTPGenerator generator = builder.build();
            String code = generator.now();
            
            ctx.json(new OTPResponse(code));
        } catch (Exception e) {
            ctx.status(400).json(new ErrorResponse(e.getMessage()));
        }
    }
    
    private static void verifyTOTP(Context ctx) {
        try {
            TOTPVerifyRequest request = ctx.bodyAsClass(TOTPVerifyRequest.class);
            
            TOTPGenerator.Builder builder = new TOTPGenerator.Builder(request.getSecret());
            
            if (request.getAlgorithm() != null) {
                builder.withHOTPGenerator(b -> b.withAlgorithm(HMACAlgorithm.valueOf(request.getAlgorithm())));
            }
            if (request.getPasswordLength() > 0) {
                builder.withHOTPGenerator(b -> b.withPasswordLength(request.getPasswordLength()));
            }
            if (request.getPeriod() > 0) {
                builder.withPeriod(Duration.ofSeconds(request.getPeriod()));
            }
            
            TOTPGenerator generator = builder.build();
            boolean valid = generator.verify(request.getCode(), request.getDelay());
            
            ctx.json(new VerifyResponse(valid));
        } catch (Exception e) {
            ctx.status(400).json(new ErrorResponse(e.getMessage()));
        }
    }
    
    private static void generateHOTP(Context ctx) {
        try {
            HOTPGenerateRequest request = ctx.bodyAsClass(HOTPGenerateRequest.class);
            
            HOTPGenerator.Builder builder = new HOTPGenerator.Builder(request.getSecret());
            
            if (request.getAlgorithm() != null) {
                builder.withAlgorithm(HMACAlgorithm.valueOf(request.getAlgorithm()));
            }
            if (request.getPasswordLength() > 0) {
                builder.withPasswordLength(request.getPasswordLength());
            }
            
            HOTPGenerator generator = builder.build();
            String code = generator.generate(request.getCounter());
            
            ctx.json(new OTPResponse(code));
        } catch (Exception e) {
            ctx.status(400).json(new ErrorResponse(e.getMessage()));
        }
    }
    
    private static void verifyHOTP(Context ctx) {
        try {
            HOTPVerifyRequest request = ctx.bodyAsClass(HOTPVerifyRequest.class);
            
            HOTPGenerator.Builder builder = new HOTPGenerator.Builder(request.getSecret());
            
            if (request.getAlgorithm() != null) {
                builder.withAlgorithm(HMACAlgorithm.valueOf(request.getAlgorithm()));
            }
            if (request.getPasswordLength() > 0) {
                builder.withPasswordLength(request.getPasswordLength());
            }
            
            HOTPGenerator generator = builder.build();
            boolean valid = generator.verify(request.getCode(), request.getCounter());
            
            ctx.json(new VerifyResponse(valid));
        } catch (Exception e) {
            ctx.status(400).json(new ErrorResponse(e.getMessage()));
        }
    }
    
    private static void generateTOTPUri(Context ctx) {
        try {
            TOTPUriRequest request = ctx.bodyAsClass(TOTPUriRequest.class);
            
            TOTPGenerator.Builder builder = new TOTPGenerator.Builder(request.getSecret());
            
            if (request.getAlgorithm() != null) {
                builder.withHOTPGenerator(b -> b.withAlgorithm(HMACAlgorithm.valueOf(request.getAlgorithm())));
            }
            if (request.getPasswordLength() > 0) {
                builder.withHOTPGenerator(b -> b.withPasswordLength(request.getPasswordLength()));
            }
            if (request.getPeriod() > 0) {
                builder.withPeriod(Duration.ofSeconds(request.getPeriod()));
            }
            
            TOTPGenerator generator = builder.build();
            URI uri = generator.getURI(request.getIssuer(), request.getAccount());
            
            ctx.json(new URIResponse(uri.toString()));
        } catch (Exception e) {
            ctx.status(400).json(new ErrorResponse(e.getMessage()));
        }
    }
    
    private static void generateHOTPUri(Context ctx) {
        try {
            HOTPUriRequest request = ctx.bodyAsClass(HOTPUriRequest.class);
            
            HOTPGenerator.Builder builder = new HOTPGenerator.Builder(request.getSecret());
            
            if (request.getAlgorithm() != null) {
                builder.withAlgorithm(HMACAlgorithm.valueOf(request.getAlgorithm()));
            }
            if (request.getPasswordLength() > 0) {
                builder.withPasswordLength(request.getPasswordLength());
            }
            
            HOTPGenerator generator = builder.build();
            URI uri = generator.getURI(request.getIssuer(), request.getAccount(), String.valueOf(request.getInitialCounter()), java.util.Collections.emptyMap());
            
            ctx.json(new URIResponse(uri.toString()));
        } catch (Exception e) {
            ctx.status(400).json(new ErrorResponse(e.getMessage()));
        }
    }
}
