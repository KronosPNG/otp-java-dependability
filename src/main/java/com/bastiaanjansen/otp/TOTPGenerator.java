package com.bastiaanjansen.otp;

import com.bastiaanjansen.otp.helpers.URIHelper;

import java.net.URI;
import java.net.URISyntaxException;
import java.time.*;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;

import static java.nio.charset.StandardCharsets.UTF_8;

public final class TOTPGenerator {
    private static final String OTP_TYPE = "totp";
    private static final /*@ spec_public @*/ Duration DEFAULT_PERIOD = Duration.ofSeconds(30);
    private static final /*@ spec_public @*/ Clock DEFAULT_CLOCK = Clock.system(ZoneId.systemDefault());

    //@ private invariant period != null;
    //@ private invariant period.getSeconds() >= 1;
    //@ private invariant clock != null;
    //@ private invariant hotpGenerator != null;
    private final /*@ spec_public @*/ Duration period;

    private final /*@ spec_public @*/ Clock clock;

    private final /*@ spec_public @*/ HOTPGenerator hotpGenerator;

    //@ requires builder != null;
    //@ requires builder.period != null && builder.period.getSeconds() >= 1;
    //@ requires builder.clock != null;
    //@ requires builder.hotpBuilder != null;
    private TOTPGenerator(final Builder builder) {
        this.period = builder.period;
        this.clock = builder.clock;
        this.hotpGenerator = builder.hotpBuilder.build();
    }

    //@ requires uri != null;
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ signals (URISyntaxException e) true;
    //@ signals (IllegalArgumentException e) true;
    //@ signals_only URISyntaxException, IllegalArgumentException;
    public static TOTPGenerator fromURI(URI uri) throws URISyntaxException {
        Map<String, String> query = URIHelper.queryItems(uri);

        String secret = Optional.ofNullable(query.get(URIHelper.SECRET))
                .orElseThrow(() -> new IllegalArgumentException("Secret query parameter must be set"));

        Builder builder = new Builder(secret);

        try {
            Optional.ofNullable(query.get(URIHelper.PERIOD))
                    .map(s -> Duration.ofSeconds(Long.parseLong(s)))
                    .ifPresent(builder::withPeriod);
            Optional.ofNullable(query.get(URIHelper.DIGITS))
                    .map(Integer::valueOf)
                    .ifPresent(builder.hotpBuilder::withPasswordLength);
            Optional.ofNullable(query.get(URIHelper.ALGORITHM))
                    .map(String::toUpperCase)
                    .map(HMACAlgorithm::valueOf)
                    .ifPresent(builder.hotpBuilder::withAlgorithm);
        } catch (Exception e) {
            throw new URISyntaxException(uri.toString(), "URI could not be parsed");
        }

        return builder.build();
    }

    //@ requires secret != null;
    //@ requires secret.length > 0;
    //@ ensures \result != null;
    //@ assignable \nothing;
    public static TOTPGenerator withDefaultValues(final byte[] secret) {
        return new TOTPGenerator.Builder(secret).build();
    }

    //@ ensures \result != null;
    //@ ensures \result.length() == getPasswordLength();
    //@ assignable \nothing;
    //@ signals (IllegalStateException e) true;
    public String now() throws IllegalStateException {
        long counter = calculateCounter(clock, period);
        return hotpGenerator.generate(counter);
    }

    //@ requires clock != null;
    //@ ensures \result != null;
    //@ ensures \result.length() == getPasswordLength();
    //@ assignable \nothing;
    //@ signals (IllegalStateException e) true;
    public String now(Clock clock) throws IllegalStateException {
        long counter = calculateCounter(clock, period);
        return hotpGenerator.generate(counter);
    }

    //@ requires instant != null;
    //@ ensures \result != null;
    //@ ensures \result.length() == getPasswordLength();
    //@ assignable \nothing;
    //@ signals (IllegalStateException e) true;
    public String at(final Instant instant) throws IllegalStateException {
        return at(instant.getEpochSecond());
    }

    //@ requires date != null;
    //@ ensures \result != null;
    //@ ensures \result.length() == getPasswordLength();
    //@ assignable \nothing;
    //@ signals (IllegalStateException e) true;
    public String at(final Date date) throws IllegalStateException {
        long secondsSince1970 = TimeUnit.MILLISECONDS.toSeconds(date.getTime());
        return at(secondsSince1970);
    }

    //@ requires date != null;
    //@ ensures \result != null;
    //@ ensures \result.length() == getPasswordLength();
    //@ assignable \nothing;
    //@ signals (IllegalStateException e) true;
    public String at(final LocalDate date) throws IllegalStateException {
        long secondsSince1970 = date.atStartOfDay(clock.getZone()).toEpochSecond();
        return at(secondsSince1970);
    }

    //@ requires secondsPast1970 > 0;
    //@ ensures \result != null;
    //@ ensures \result.length() == getPasswordLength();
    //@ assignable \nothing;
    //@ signals (IllegalArgumentException e) secondsPast1970 <= 0;
    //@ signals_only IllegalArgumentException;
    public String at(final long secondsPast1970) throws IllegalArgumentException {
        if (!validateTime(secondsPast1970))
            throw new IllegalArgumentException("Time must be above zero");

        long counter = calculateCounter(secondsPast1970, period);
        return hotpGenerator.generate(counter);
    }

    //@ requires code != null;
    //@ assignable \nothing;
    //@ pure
    public boolean verify(final String code) {
        long counter = calculateCounter(clock, period);
        return hotpGenerator.verify(code, counter);
    }

    /**
     * Checks whether a code is valid for a specific counter taking a delay window into account
     *
     * @param code an OTP code
     * @param delayWindow window in which a code can still be deemed valid
     * @return a boolean, true if code is valid, otherwise false
     */
    //@ requires code != null;
    //@ requires delayWindow >= 0;
    //@ assignable \nothing;
    //@ pure
    public boolean verify(final String code, final int delayWindow) {
        long counter = calculateCounter(clock, period);
        return hotpGenerator.verify(code, counter, delayWindow);
    }

    //@ requires issuer != null;
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ signals (URISyntaxException e) true;
    public URI getURI(final String issuer) throws URISyntaxException {
        return getURI(issuer, "");
    }

    //@ requires issuer != null;
    //@ requires account != null;
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ signals (URISyntaxException e) true;
    public URI getURI(final String issuer, final String account) throws URISyntaxException {
        Map<String, String> query = new HashMap<>();
        query.put(URIHelper.PERIOD, String.valueOf(period.getSeconds()));

        return hotpGenerator.getURI(OTP_TYPE, issuer, account, query);
    }

    /**
     * Calculates time until next time window will be reached and a new totp should be generated
     *
     * @return a duration object with duration until next time window
     */
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ pure
    public Duration durationUntilNextTimeWindow() {
        return durationUntilNextTimeWindow(clock);
    }

    //@ requires clock != null;
    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ pure
    public Duration durationUntilNextTimeWindow(Clock clock) {
        long timeInterval = period.toMillis();
        return Duration.ofMillis(timeInterval - clock.millis() % timeInterval);
    }

    //@ ensures \result != null;
    //@ ensures \result == period;
    //@ assignable \nothing;
    //@ pure
    public Duration getPeriod() {
        return period;
    }

    //@ ensures \result != null;
    //@ ensures \result == clock;
    //@ assignable \nothing;
    //@ pure
    public Clock getClock() {
        return clock;
    }

    //@ ensures \result != null;
    //@ assignable \nothing;
    //@ pure
    public HMACAlgorithm getAlgorithm() {
        return hotpGenerator.getAlgorithm();
    }

    //@ ensures \result >= 6 && \result <= 8;
    //@ assignable \nothing;
    //@ pure
    public int getPasswordLength() {
        return hotpGenerator.getPasswordLength();
    }

    //@ requires secondsPast1970 > 0;
    //@ requires period != null;
    //@ ensures \result >= 0;
    //@ assignable \nothing;
    //@ pure
    private long calculateCounter(final long secondsPast1970, final Duration period) {
        return TimeUnit.SECONDS.toMillis(secondsPast1970) / period.toMillis();
    }

    //@ requires clock != null;
    //@ requires period != null;
    //@ ensures \result >= 0;
    //@ assignable \nothing;
    //@ pure
    private long calculateCounter(final Clock clock, final Duration period) {
        return clock.millis() / period.toMillis();
    }

    //@ ensures \result == (time > 0);
    //@ assignable \nothing;
    //@ pure
    private boolean validateTime(final long time) {
        return time > 0;
    }

    public static final class Builder {

        private /*@ spec_public @*/ Duration period;

        private /*@ spec_public @*/ Clock clock;

        private final /*@ spec_public @*/ HOTPGenerator.Builder hotpBuilder;

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
        //@ ensures this.period == DEFAULT_PERIOD;
        //@ ensures this.clock == DEFAULT_CLOCK;
        //@ ensures this.hotpBuilder != null;
        public Builder(byte[] secret) {
            this.period = DEFAULT_PERIOD;
            this.clock = DEFAULT_CLOCK;
            this.hotpBuilder = new HOTPGenerator.Builder(secret);
        }

        /**
         * @param secret Base32 encoded secret
         */
        //@ requires secret != null;
        //@ requires secret.length() > 0;
        //@ ensures this.hotpBuilder != null;
        public Builder(String secret) {
            this(secret.getBytes(UTF_8));
        }

        //@ requires builder != null;
        //@ ensures \result == this;
        //@ assignable hotpBuilder.*;
        public Builder withHOTPGenerator(Consumer<HOTPGenerator.Builder> builder) {
            builder.accept(hotpBuilder);
            return this;
        }

        //@ requires clock != null;
        //@ ensures this.clock == clock;
        //@ ensures \result == this;
        //@ assignable this.clock;
        public Builder withClock(Clock clock) {
            this.clock = clock;
            return this;
        }

        //@ requires period != null;
        //@ requires period.getSeconds() >= 1;
        //@ ensures this.period == period;
        //@ ensures \result == this;
        //@ assignable this.period;
        public Builder withPeriod(Duration period) {
            if (period.getSeconds() < 1) throw new IllegalArgumentException("Period must be at least 1 second");
            this.period = period;
            return this;
        }

        //@ ensures \result != null;
        //@ assignable \nothing;
        public TOTPGenerator build() {
            return new TOTPGenerator(this);
        }
    }
}
