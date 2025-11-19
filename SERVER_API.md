# OTP Server API

A lightweight REST API server for OTP (One-Time Password) generation and verification using Javalin.

## Running the Server

### Using Maven:
```bash
# PowerShell
mvn clean compile exec:java "-Dexec.mainClass=com.bastiaanjansen.otp.server.OTPServer"

# Bash/Linux
mvn clean compile exec:java -Dexec.mainClass="com.bastiaanjansen.otp.server.OTPServer"
```

### Build and run JAR:
```bash
mvn clean package
java -cp target/otp-java-2.1.0.jar com.bastiaanjansen.otp.server.OTPServer
```

### Custom Port:
```bash
java -cp target/otp-java-2.1.0.jar com.bastiaanjansen.otp.server.OTPServer 8080
```

Default port: **7000**

## API Endpoints

### Health Check
- **GET** `/health`
- Response: `{"status": "OK"}`

### Generate Secret
- **POST** `/api/secret/generate`
- Request Body (optional):
```json
{
  "length": 32
}
```
- Response:
```json
{
  "secret": "3a4f5b...",
  "secretBase32": "HI5FYLST..."
}
```

### TOTP Endpoints

#### Generate TOTP Code
- **POST** `/api/totp/generate`
- Request Body:
```json
{
  "secret": [72, 101, 108, 108, 111],
  "algorithm": "SHA1",
  "passwordLength": 6,
  "period": 30
}
```
- Response:
```json
{
  "code": "123456"
}
```

#### Verify TOTP Code
- **POST** `/api/totp/verify`
- Request Body:
```json
{
  "secret": [72, 101, 108, 108, 111],
  "code": "123456",
  "algorithm": "SHA1",
  "passwordLength": 6,
  "period": 30,
  "delay": 0
}
```
- Response:
```json
{
  "valid": true
}
```

#### Generate TOTP URI (for QR codes)
- **POST** `/api/uri/totp`
- Request Body:
```json
{
  "secret": [72, 101, 108, 108, 111],
  "issuer": "MyApp",
  "account": "user@example.com",
  "algorithm": "SHA1",
  "passwordLength": 6,
  "period": 30
}
```
- Response:
```json
{
  "uri": "otpauth://totp/MyApp:user@example.com?secret=..."
}
```

### HOTP Endpoints

#### Generate HOTP Code
- **POST** `/api/hotp/generate`
- Request Body:
```json
{
  "secret": [72, 101, 108, 108, 111],
  "counter": 0,
  "algorithm": "SHA1",
  "passwordLength": 6
}
```
- Response:
```json
{
  "code": "123456"
}
```

#### Verify HOTP Code
- **POST** `/api/hotp/verify`
- Request Body:
```json
{
  "secret": [72, 101, 108, 108, 111],
  "code": "123456",
  "counter": 0,
  "algorithm": "SHA1",
  "passwordLength": 6
}
```
- Response:
```json
{
  "valid": true
}
```

#### Generate HOTP URI (for QR codes)
- **POST** `/api/uri/hotp`
- Request Body:
```json
{
  "secret": [72, 101, 108, 108, 111],
  "issuer": "MyApp",
  "account": "user@example.com",
  "initialCounter": 0,
  "algorithm": "SHA1",
  "passwordLength": 6
}
```
- Response:
```json
{
  "uri": "otpauth://hotp/MyApp:user@example.com?secret=..."
}
```

## Parameters

### Algorithms
- `SHA1` (default)
- `SHA256`
- `SHA512`

### Optional Parameters
- All `algorithm`, `passwordLength`, and `period`/`counter` fields are optional
- If not provided, defaults from the OTP library will be used

## Example Usage with curl

### Generate a secret:
```bash
curl -X POST http://localhost:7000/api/secret/generate \
  -H "Content-Type: application/json" \
  -d '{}'
```

### Generate TOTP:
```bash
curl -X POST http://localhost:7000/api/totp/generate \
  -H "Content-Type: application/json" \
  -d '{"secret":[72,101,108,108,111]}'
```

### Verify TOTP:
```bash
curl -X POST http://localhost:7000/api/totp/verify \
  -H "Content-Type: application/json" \
  -d '{"secret":[72,101,108,108,111],"code":"123456","delay":0}'
```

## Error Handling

All endpoints return error responses in the format:
```json
{
  "error": "Error message"
}
```

HTTP Status Codes:
- `200` - Success
- `400` - Bad Request (invalid parameters)
- `500` - Internal Server Error
