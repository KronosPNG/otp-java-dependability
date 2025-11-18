package com.bastiaanjansen.otp;

import com.bastiaanjansen.otp.helpers.URIHelper;
import org.apache.commons.codec.binary.Base32;

import javax.crypto.Mac;
import javax.crypto.spec.SecretKeySpec;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.ByteBuffer;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import static java.nio.charset.StandardCharsets.UTF_8;

public final class HOTPGenerator {

    private static final String URL_SCHEME = "otpauth";
    //@ public static invariant DEFAULT_PASSWORD_LENGTH >= 6 && DEFAULT_PASSWORD_LENGTH <= 8;
    private static final /*@ spec_public @*/ int DEFAULT_PASSWORD_LENGTH = 6;
    private static final /*@ spec_public @*/ HMACAlgorithm DEFAULT_HMAC_ALGORITHM = HMACAlgorithm.SHA1;
    private static final String OTP_TYPE = "hotp";

    //@ private invariant passwordLength >= 6 && passwordLength <= 8;
    //@ private invariant algorithm != null;
    //@ private invariant secret != null;
    //@ private invariant secret.length > 0;
    private final /*@ spec_public @*/ int passwordLength;

    private final /*@ spec_public @*/ HMACAlgorithm algorithm;

    private final /*@ spec_public @*/ byte[] secret;

    //@ requires builder != null;
    //@ requires builder.passwordLength >= 6 && builder.passwordLength <= 8;
    //@ requires builder.algorithm != null;
    //@ requires builder.secret != null && builder.secret.length > 0;
    private HOTPGenerator(final Builder builder) {
        this.passwordLength = builder.passwordLength;
        this.algorithm = builder.algorithm;
        this.secret = builder.secret;
    }

    //@ requires uri != null;
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ signals (URISyntaxException e) true;
    //@ signals (IllegalArgumentException e) true;
    //@ signals_only URISyntaxException, IllegalArgumentException;
    public static HOTPGenerator fromURI(final URI uri) throws URISyntaxException {
        Map<String, String> query = URIHelper.queryItems(uri);

        byte[] secret = Optional.ofNullable(query.get(URIHelper.SECRET))
                .map(s -> s.getBytes(UTF_8))
                .orElseThrow(() -> new IllegalArgumentException("Secret query parameter must be set"));

        Builder builder = new Builder(secret);

        try {
            Optional.ofNullable(query.get(URIHelper.DIGITS))
                    .map(Integer::valueOf)
                    .ifPresent(builder::withPasswordLength);
            Optional.ofNullable(query.get(URIHelper.ALGORITHM))
                    .map(String::toUpperCase)
                    .map(HMACAlgorithm::valueOf)
                    .ifPresent(builder::withAlgorithm);
        } catch (Exception e) {
            throw new URISyntaxException(uri.toString(), "URI could not be parsed");
        }

        return builder.build();
    }

    //@ requires secret != null;
    //@ requires secret.length > 0;
    //@ ensures \result != null;
    //@ assignable \nothing;
    public static HOTPGenerator withDefaultValues(final byte[] secret) {
        return new HOTPGenerator.Builder(secret).build();
    }

    //@ requires counter >= 0;
    //@ requires issuer != null;
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ signals (URISyntaxException e) true;
    public URI getURI(final int counter, final String issuer) throws URISyntaxException {
        return getURI(counter, issuer, "");
    }

    //@ requires counter >= 0;
    //@ requires issuer != null;
    //@ requires account != null;
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ signals (URISyntaxException e) true;
    public URI getURI(final int counter, final String issuer, final String account) throws URISyntaxException {
        Map<String, String> query = new HashMap<>();
        query.put(URIHelper.COUNTER, String.valueOf(counter));

        return getURI(OTP_TYPE, issuer, account, query);
    }

    //@ ensures \result >= 6 && \result <= 8;
    //@ ensures \result == passwordLength;
    //@ assignable \nothing;
    //@ pure
    public int getPasswordLength() {
        return passwordLength;
    }

    //@ ensures \result != null;
    //@ ensures \result == algorithm;
    //@ assignable \nothing;
    //@ pure
    public HMACAlgorithm getAlgorithm() {
        return algorithm;
    }

    //@ requires code != null;
    //@ requires counter >= 0;
    //@ assignable \nothing;
    //@ pure
    public boolean verify(final String code, final long counter) {
        return verify(code, counter, 0);
    }

    //@ requires code != null;
    //@ requires counter >= 0;
    //@ requires delayWindow >= 0;
    //@ assignable \nothing;
    //@ pure
    public boolean verify(final String code, final long counter, final int delayWindow) {
        if (code.length() != passwordLength) return false;

        for (int i = -delayWindow; i <= delayWindow; i++) {
            String currentCode = generate(counter + i);
            if (code.equals(currentCode)) return true;
        }

        return false;
    }

    //@ requires counter >= 0;
    //@ ensures \result != null;
    //@ ensures \result.length() == passwordLength;
    //@ assignable \nothing;
    //@ signals (IllegalStateException e) true;
    //@ signals_only IllegalArgumentException, IllegalStateException;
    public String generate(final long counter) throws IllegalStateException {
        if (counter < 0)
            throw new IllegalArgumentException("Counter must be greater than or equal to 0");

        byte[] secretBytes = decodeBase32(secret);
        byte[] counterBytes = longToBytes(counter);

        byte[] hash;

        try {
            hash = generateHash(secretBytes, counterBytes);
        } catch (NoSuchAlgorithmException | InvalidKeyException e) {
            throw new IllegalStateException();
        }

        return getCodeFromHash(hash);
    }

    //@ requires type != null;
    //@ requires issuer != null;
    //@ requires account != null;
    //@ requires query != null;
    //@ ensures \result != null;
    //@ assignable query.*;
    //@ signals (URISyntaxException e) true;
    public URI getURI(final String type, final String issuer, final String account, final Map<String, String> query) throws URISyntaxException {
        query.put(URIHelper.DIGITS, String.valueOf(passwordLength));
        query.put(URIHelper.ALGORITHM, algorithm.name());
        query.put(URIHelper.SECRET, new String(secret, UTF_8));
        query.put(URIHelper.ISSUER, issuer);

        String path = account.isEmpty() ? URIHelper.encode(issuer) : String.format("%s:%s", URIHelper.encode(issuer), URIHelper.encode(account));

        return URIHelper.createURI(URL_SCHEME, type, path, query);
    }

    /**
     * Decode a base32 value to bytes array
     *
     * @param value base32 value
     * @return bytes array
     */
    //@ requires value != null;
    //@ ensures \result != null;
    //@ assignable \nothing;
    private byte[] decodeBase32(final byte[] value) {
        Base32 codec = new Base32();
        return codec.decode(value);
    }

    //@ requires value >= 0;
    //@ ensures \result != null;
    //@ ensures \result.length == Long.BYTES;
    //@ assignable \nothing;
    private byte[] longToBytes(final long value) {
        return ByteBuffer.allocate(Long.BYTES).putLong(value).array();
    }

    //@ requires secret != null;
    //@ requires data != null;
    //@ ensures \result != null;
    //@ ensures \result.length >= 20 && \result.length <= 64;
    //@ assignable \nothing;
    //@ signals (InvalidKeyException e) true;
    //@ signals (NoSuchAlgorithmException e) true;
    private byte[] generateHash(final byte[] secret, final byte[] data) throws InvalidKeyException, NoSuchAlgorithmException {
        // Create a secret key with correct SHA algorithm
        SecretKeySpec signKey = new SecretKeySpec(secret, "RAW");
        // Mac is 'message authentication code' algorithm (RFC 2104)
        Mac mac = Mac.getInstance(algorithm.getHMACName());
        mac.init(signKey);
        // Hash data with generated sign key
        return mac.doFinal(data);
    }

    //@ requires hash != null;
    //@ requires hash.length >= 20;
    //@ ensures \result != null;
    //@ ensures \result.length() == passwordLength;
    //@ assignable \nothing;
    //@ pure
    private String getCodeFromHash(final byte[] hash) {
        /* Find mask to get last 4 digits:
        1. Set all bits to 1: ~0 -> 11111111 -> 255 decimal -> 0xFF
        2. Shift n (in this case 4, because we want the last 4 bits) bits to left with <<
        3. Negate the result: 1111 1100 -> 0000 0011
         */
        int mask = ~(~0 << 4);

        /* Get last 4 bits of hash as offset:
        Use the bitwise AND (&) operator to select last 4 bits
        Mask should be 00001111 = 15 = 0xF
        Last byte of hash & 0xF = last 4 bits:
        Example:
        Input: decimal 219 as binary: 11011011 &
        Mask: decimal 15 as binary:   00001111
        -----------------------------------------
        Output: decimal 11 as binary: 00001011
         */
        byte lastByte = hash[hash.length - 1];
        int offset = lastByte & mask;

        // Get 4 bytes from hash from offset to offset + 3
        byte[] truncatedHashInBytes = { hash[offset], hash[offset + 1], hash[offset + 2], hash[offset + 3] };

        // Wrap in ByteBuffer to convert bytes to long
        ByteBuffer byteBuffer = ByteBuffer.wrap(truncatedHashInBytes);
        long truncatedHash = byteBuffer.getInt();

        // Mask most significant bit
        truncatedHash &= 0x7FFFFFFF;

        // Modulo (%) truncatedHash by 10^passwordLength
        truncatedHash %= Math.pow(10, passwordLength);

        // Left pad with 0s for an n-digit code
        return String.format("%0" + passwordLength + "d", truncatedHash);
    }

    public static final class Builder {
        //@ public invariant passwordLength >= 6 && passwordLength <= 8;
        private /*@ spec_public @*/ int passwordLength;

        private /*@ spec_public @*/ HMACAlgorithm algorithm;

        /**
         * Base32 encoded secret
         */
        private final /*@ spec_public @*/ byte[] secret;

        /**
         * Creates a new builder.
         * <p>
         * Use {@link SecretGenerator#generate()} to create a secret.
         * <p>
         * If you are using a shared secret from another generator, you would likely need to encode it using
         * {@link org.apache.commons.codec.binary.Base32#encode(byte[])}}
         *
         * @param secret Base32 encoded secret
         */
        //@ requires secret != null;
        //@ requires secret.length > 0;
        //@ ensures this.secret == secret;
        //@ ensures this.passwordLength == DEFAULT_PASSWORD_LENGTH;
        //@ ensures this.algorithm == DEFAULT_HMAC_ALGORITHM;
        public Builder(final byte[] secret) {
            if (secret.length == 0)
                throw new IllegalArgumentException("Secret must not be empty");

            this.secret = secret;
            this.passwordLength = DEFAULT_PASSWORD_LENGTH;
            //@ assert DEFAULT_PASSWORD_LENGTH >= 6 && DEFAULT_PASSWORD_LENGTH <= 8;
            this.algorithm = DEFAULT_HMAC_ALGORITHM;
        }

        /**
         * @param secret Base32 encoded secret
         */
        //@ requires secret != null;
        //@ requires secret.length() > 0;
        public Builder(String secret) {
            this(secret.getBytes(UTF_8));
        }

        //@ requires passwordLength >= 6 && passwordLength <= 8;
        //@ ensures this.passwordLength == passwordLength;
        //@ ensures \result == this;
        //@ assignable this.passwordLength;
        public Builder withPasswordLength(final int passwordLength) {
            if (!passwordLengthIsValid(passwordLength))
                throw new IllegalArgumentException("Password length must be between 6 and 8");

            this.passwordLength = passwordLength;
            return this;
        }

        //@ requires algorithm != null;
        //@ ensures this.algorithm == algorithm;
        //@ ensures \result == this;
        //@ assignable this.algorithm;
        public Builder withAlgorithm(final HMACAlgorithm algorithm) {
            this.algorithm = algorithm;
            return this;
        }

        //@ ensures \result != null;
        //@ assignable \nothing;
        public HOTPGenerator build() {
            return new HOTPGenerator(this);
        }

        //@ ensures \result == (passwordLength >= 6 && passwordLength <= 8);
        //@ assignable \nothing;
        //@ pure
        private boolean passwordLengthIsValid(final int passwordLength) {
            return passwordLength >= 6 && passwordLength <= 8;
        }
    }
}
