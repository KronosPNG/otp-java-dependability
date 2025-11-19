package com.bastiaanjansen.otp.benchmarks;

import com.bastiaanjansen.otp.HOTPGenerator;
import com.bastiaanjansen.otp.HMACAlgorithm;
import com.bastiaanjansen.otp.SecretGenerator;
import com.bastiaanjansen.otp.TOTPGenerator;
import org.openjdk.jmh.annotations.*;

import java.time.Duration;
import java.util.concurrent.TimeUnit;

@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Thread)
@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
public class OTPBenchmark {

    private byte[] secret;
    private HOTPGenerator hotpGenerator;
    private TOTPGenerator totpGenerator;

    @Setup
    public void setup() {
        // Generate a secret for benchmarking
        secret = SecretGenerator.generate();
        
        // Initialize HOTP generator
        hotpGenerator = new HOTPGenerator.Builder(secret)
                .withAlgorithm(HMACAlgorithm.SHA512)
                .withPasswordLength(6)
                .build();
        
        // Initialize TOTP generator
        totpGenerator = new TOTPGenerator.Builder(secret)
                .withHOTPGenerator(builder -> builder
                    .withAlgorithm(HMACAlgorithm.SHA512)
                    .withPasswordLength(6))
                .withPeriod(Duration.ofSeconds(30))
                .build();
    }

    @Benchmark
    public String benchmarkHOTPGeneration() {
        return hotpGenerator.generate(0);
    }

    @Benchmark
    public String benchmarkTOTPGeneration() {
        return totpGenerator.now();
    }

    @Benchmark
    public byte[] benchmarkSecretGeneration() {
        return SecretGenerator.generate();
    }

    @Benchmark
    public byte[] benchmarkSecretGenerationWithLength() {
        return SecretGenerator.generate(64);
    }
}
