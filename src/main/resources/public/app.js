const API_BASE_URL = 'http://localhost:7000/api';

let currentSecret = null;
let countdownInterval = null;

// Tab switching
function showTab(tabName) {
    document.querySelectorAll('.tab-content').forEach(tab => {
        tab.classList.remove('active');
    });
    document.querySelectorAll('.tab-btn').forEach(btn => {
        btn.classList.remove('active');
    });

    document.getElementById(`${tabName}-tab`).classList.add('active');
    event.target.classList.add('active');

    // Don't clear countdown - let it keep running in background
}

// Toggle counter field for HOTP
function toggleCounterField() {
    const isHOTP = document.querySelector('input[name="otp-type"]:checked').value === 'hotp';
    document.getElementById('counter-group').style.display = isHOTP ? 'block' : 'none';
    document.getElementById('period-group').style.display = isHOTP ? 'none' : 'block';
}

function toggleVerifyCounterField() {
    const isHOTP = document.querySelector('input[name="verify-otp-type"]:checked').value === 'hotp';
    document.getElementById('verify-counter-group').style.display = isHOTP ? 'block' : 'none';
    document.getElementById('verify-period-group').style.display = isHOTP ? 'none' : 'block';
    document.getElementById('verify-delay-group').style.display = isHOTP ? 'none' : 'block';
}

// Convert hex string to byte array
function hexToBytes(hex) {
    const bytes = [];
    for (let i = 0; i < hex.length; i += 2) {
        bytes.push(Number.parseInt(hex.substr(i, 2), 16));
    }
    return bytes;
}

// Convert Base32 to byte array
function base32ToBytes(base32) {
    const alphabet = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567';
    base32 = base32.toUpperCase().replace(/=+$/, '');
    let bits = '';
    
    for (let i = 0; i < base32.length; i++) {
        const val = alphabet.indexOf(base32[i]);
        if (val === -1) throw new Error('Invalid Base32 character');
        bits += val.toString(2).padStart(5, '0');
    }
    
    const bytes = [];
    for (let i = 0; i + 8 <= bits.length; i += 8) {
        bytes.push(Number.parseInt(bits.substr(i, 8), 2));
    }
    
    return bytes;
}

// Parse secret (auto-detect hex or base32)
function parseSecret(secret) {
    secret = secret.trim().replaceAll(/\s+/g, '');
    
    // Try hex first (even length, only hex chars)
    if (/^[0-9A-Fa-f]+$/.test(secret) && secret.length % 2 === 0) {
        return hexToBytes(secret);
    }
    
    // Try base32
    if (/^[A-Z2-7]+=*$/.test(secret.toUpperCase())) {
        return base32ToBytes(secret);
    }
    
    throw new Error('Invalid secret format. Use hex or Base32.');
}

// Generate Secret
async function generateSecret() {
    const length = Number.parseInt(document.getElementById('secret-length').value);
    
    try {
        const response = await fetch(`${API_BASE_URL}/secret/generate`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ length })
        });

        const data = await response.json();
        
        if (response.ok) {
            currentSecret = data.secretBase32;
            document.getElementById('secret-base32').textContent = data.secretBase32;
            document.getElementById('secret-hex').textContent = data.secret;
            document.getElementById('secret-result').classList.remove('hidden');
        } else {
            showError(data.error || 'Failed to generate secret');
        }
    } catch (error) {
        showError('Network error: ' + error.message);
    }
}

// Use generated secret in OTP generation
function useSecretForOTP() {
    if (currentSecret) {
        document.getElementById('gen-secret-input').value = currentSecret;
        showTab('generate');
        document.querySelector('.tab-btn:first-child').classList.add('active');
    }
}

// Generate OTP
async function generateOTP() {
    const type = document.querySelector('input[name="otp-type"]:checked').value;
    const secretInput = document.getElementById('gen-secret-input').value;
    const algorithm = document.getElementById('gen-algorithm').value;
    const passwordLength = Number.parseInt(document.getElementById('gen-length').value);
    
    if (!secretInput) {
        showError('Please enter a secret');
        return;
    }

    try {
        const secret = parseSecret(secretInput);
        const endpoint = type === 'totp' ? '/totp/generate' : '/hotp/generate';
        
        const body = {
            secret,
            algorithm,
            passwordLength
        };

        if (type === 'totp') {
            body.period = Number.parseInt(document.getElementById('gen-period').value);
        } else {
            body.counter = Number.parseInt(document.getElementById('gen-counter').value);
        }

        const response = await fetch(`${API_BASE_URL}${endpoint}`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(body)
        });

        const data = await response.json();
        
        if (response.ok) {
            document.getElementById('otp-code').textContent = data.code;
            document.getElementById('otp-result').classList.remove('hidden');
            
            // Start countdown for TOTP
            if (type === 'totp') {
                startCountdown(Number.parseInt(document.getElementById('gen-period').value));
            } else {
                document.getElementById('countdown-container').classList.add('hidden');
            }
        } else {
            showError(data.error || 'Failed to generate OTP');
        }
    } catch (error) {
        showError(error.message);
    }
}

// Start countdown timer for TOTP
function startCountdown(period) {
    const countdownEl = document.getElementById('countdown');
    const containerEl = document.getElementById('countdown-container');
    containerEl.classList.remove('hidden');
    
    if (countdownInterval) {
        clearInterval(countdownInterval);
    }
    
    let lastRemaining = -1;
    
    function updateCountdown() {
        const now = Math.floor(Date.now() / 1000);
        const remaining = period - (now % period);
        countdownEl.textContent = remaining;
        
        // When countdown resets to period, regenerate the code
        if (lastRemaining !== -1 && remaining > lastRemaining) {
            generateOTP();
        }
        
        lastRemaining = remaining;
    }
    
    updateCountdown();
    countdownInterval = setInterval(updateCountdown, 1000);
}

// Generate URI
async function generateURI() {
    const type = document.querySelector('input[name="otp-type"]:checked').value;
    const secretInput = document.getElementById('gen-secret-input').value;
    const issuer = document.getElementById('uri-issuer').value;
    const account = document.getElementById('uri-account').value;
    const algorithm = document.getElementById('gen-algorithm').value;
    const passwordLength = Number.parseInt(document.getElementById('gen-length').value);
    
    if (!secretInput || !issuer || !account) {
        showError('Please fill in secret, issuer, and account fields');
        return;
    }

    try {
        const secret = parseSecret(secretInput);
        const endpoint = type === 'totp' ? '/uri/totp' : '/uri/hotp';
        
        const body = {
            secret,
            issuer,
            account,
            algorithm,
            passwordLength
        };

        if (type === 'totp') {
            body.period = Number.parseInt(document.getElementById('gen-period').value);
        } else {
            body.initialCounter = Number.parseInt(document.getElementById('gen-counter').value);
        }

        const response = await fetch(`${API_BASE_URL}${endpoint}`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(body)
        });

        const data = await response.json();
        
        if (response.ok) {
            document.getElementById('uri-text').textContent = data.uri;
            document.getElementById('uri-result').classList.remove('hidden');
        } else {
            showError(data.error || 'Failed to generate URI');
        }
    } catch (error) {
        showError(error.message);
    }
}

// Verify OTP
async function verifyOTP() {
    const type = document.querySelector('input[name="verify-otp-type"]:checked').value;
    const secretInput = document.getElementById('verify-secret').value;
    const code = document.getElementById('verify-code').value;
    const algorithm = document.getElementById('verify-algorithm').value;
    const passwordLength = Number.parseInt(document.getElementById('verify-length').value);
    
    if (!secretInput || !code) {
        showError('Please enter both secret and code');
        return;
    }

    try {
        const secret = parseSecret(secretInput);
        const endpoint = type === 'totp' ? '/totp/verify' : '/hotp/verify';
        
        const body = {
            secret,
            code,
            algorithm,
            passwordLength
        };

        if (type === 'totp') {
            body.period = Number.parseInt(document.getElementById('verify-period').value);
            body.delay = Number.parseInt(document.getElementById('verify-delay').value);
        } else {
            body.counter = Number.parseInt(document.getElementById('verify-counter').value);
        }

        const response = await fetch(`${API_BASE_URL}${endpoint}`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify(body)
        });

        const data = await response.json();
        
        if (response.ok) {
            const resultDiv = document.getElementById('verify-result');
            const statusDiv = resultDiv.querySelector('.verify-status');
            
            if (data.valid) {
                statusDiv.textContent = '✅ Valid Code';
                statusDiv.className = 'verify-status success';
            } else {
                statusDiv.textContent = '❌ Invalid Code';
                statusDiv.className = 'verify-status error';
            }
            
            resultDiv.classList.remove('hidden');
        } else {
            showError(data.error || 'Failed to verify OTP');
        }
    } catch (error) {
        showError(error.message);
    }
}

// Copy to clipboard
function copyToClipboard(elementId, event) {
    const element = document.getElementById(elementId);
    const text = element.textContent;
    
    navigator.clipboard.writeText(text).then(() => {
        // Visual feedback
        const btn = event ? event.target : document.activeElement;
        const originalText = btn.textContent;
        btn.textContent = 'Copied!';
        btn.style.background = '#2196F3';
        
        setTimeout(() => {
            btn.textContent = originalText;
            btn.style.background = '';
        }, 2000);
    }).catch(err => {
        showError('Failed to copy: ' + err.message);
    });
}

// Show error message
function showError(message) {
    // Remove existing error messages
    document.querySelectorAll('.error-message').forEach(el => el.remove());
    
    const errorDiv = document.createElement('div');
    errorDiv.className = 'error-message';
    errorDiv.textContent = message;
    
    const activeTab = document.querySelector('.tab-content.active .card');
    activeTab.appendChild(errorDiv);
    
    setTimeout(() => errorDiv.remove(), 5000);
}
