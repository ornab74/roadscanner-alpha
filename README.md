# RoadScanner Alpha

RoadScanner Alpha is a Flask web platform for road-scan risk analysis with:
- user auth and account tiers,
- admin operations and feature flags,
- API-key based signed API access,
- weather and geocode intelligence,
- billing via Stripe,
- optional Google OAuth login,
- optional CAPTCHA protection,
- optional SMTP/DKIM/PQ mail protections.

The app entrypoint is `main.py`.

---

## 1) What the program does

At a high level, the application provides:

1. **Interactive web app**
   - Register/login, dashboard, scans, reports, settings, billing, corporate invite flow.

2. **Admin controls**
   - Admin pages for operational controls (feature flags, backups, local LLM controls, etc.).

3. **Signed API access**
   - HMAC-protected API requests using API keys + nonce + timestamp signature headers.

4. **Security-by-default middleware**
   - CSP/security headers, HTTPS enforcement option, CSRF/origin checks, ban/rate-limit gates.

5. **Optional integrations**
   - Stripe billing, Google OAuth, CAPTCHA, SMTP + DKIM/PQ mail, OpenAI/Grok/local-LLM hooks.

---

## 2) Hard-required environment variables

The app **will not start** without these:

- `INVITE_CODE_SECRET_KEY`
  - Use a long, random value (recommended: at least 32 bytes entropy).
- `admin_username`
- `admin_pass` (must satisfy password-strength checks)

Example:

```bash
export INVITE_CODE_SECRET_KEY='replace-with-very-long-random-secret'
export admin_username='admin'
export admin_pass='VeryStrongPassword123!'
```

---

## 3) Quick local startup (minimal)

```bash
pip install -r requirements.txt

export INVITE_CODE_SECRET_KEY='replace-with-very-long-random-secret'
export admin_username='admin'
export admin_pass='VeryStrongPassword123!'

# Keep optional native PQ disabled locally unless liboqs is ready
export ENABLE_OQS_IMPORT=0
export STRICT_PQ2_ONLY=0

# Optional providers off for initial bring-up
export GOOGLE_OAUTH_ENABLED=false
export CAPTCHA_ENABLED=false
export STRIPE_ENABLED=false
export EMAIL_ENABLED=false

python main.py
```

Default bind in current app path is `http://127.0.0.1:3000`.

---

## 4) Setup guide: Stripe payments (recommended flow)

### Step A: Create Stripe products/prices
In Stripe dashboard create prices for plans, then capture IDs.

### Step B: Set env vars

```bash
export STRIPE_ENABLED=true
export STRIPE_SECRET_KEY='sk_live_or_test_...'
export STRIPE_WEBHOOK_SECRET='whsec_...'
export STRIPE_PRICE_PRO_MONTHLY='price_...'
export STRIPE_PRICE_CORP_MONTHLY='price_...'
# optional credits packs as JSON mapping
export STRIPE_CREDIT_PACKS_JSON='{"starter":"price_123","pro":"price_456"}'
```

### Step C: Configure webhook endpoint
Point Stripe webhook to your app webhook route and subscribe to required billing events in dashboard.

### Step D: Validate
- Visit billing page.
- Start checkout flow.
- Confirm webhook delivery in Stripe dashboard.

---

## 5) Setup guide: Google OAuth

### Step A: Create Google OAuth credentials
- Create OAuth client in Google Cloud.
- Add authorized redirect URI matching your deployment.

### Step B: Set env vars

```bash
export GOOGLE_OAUTH_ENABLED=true
export GOOGLE_CLIENT_ID='...apps.googleusercontent.com'
export GOOGLE_CLIENT_SECRET='...'
export GOOGLE_OAUTH_REDIRECT_URI='https://your-domain.com/auth/google/callback'
```

### Step C: Validate
- Open `/auth/google/start`.
- Complete Google consent.
- Confirm callback and account/session creation.

---

## 6) Setup guide: CAPTCHA (Turnstile/hCaptcha)

### Step A: Choose provider
Supported via `CAPTCHA_PROVIDER`.

### Step B: Set keys

```bash
export CAPTCHA_ENABLED=true
export CAPTCHA_PROVIDER='turnstile'   # or hcaptcha
export CAPTCHA_SITE_KEY='site_key_here'
export CAPTCHA_SECRET_KEY='secret_key_here'
```

### Step C: Validate
- Confirm CAPTCHA renders on protected forms.
- Submit valid and invalid tokens to verify enforcement.

---

## 7) Setup guide: SMTP and DKIM (optional)

```bash
export EMAIL_ENABLED=true
export EMAIL_FROM='noreply@your-domain.com'
export EMAIL_SMTP_HOST='smtp.your-provider.com'
export EMAIL_SMTP_PORT='587'
export EMAIL_SMTP_USER='smtp-user'
export EMAIL_SMTP_PASS='smtp-pass'

export DKIM_ENABLED=true
export DKIM_DOMAIN='your-domain.com'
export DKIM_SELECTOR='selector1'
export DKIM_PRIVATE_KEY_PATH='/secure/path/dkim_private.pem'
```

Optional alternative SMTP env aliases are also supported (`SMTP_HOST`, `SMTP_PORT`, etc.).

---

## 8) Security hardening controls (important)

Recommended production settings:

```bash
export ENFORCE_HTTPS=true
export SESSION_COOKIE_SECURE=true
export SESSION_COOKIE_SAMESITE='Lax'
# Strongly recommended in prod: set allowed hosts exactly
export ALLOWED_HOSTS='your-domain.com,.your-domain.com'
# Optional explicit browser mutation origin allowlist
export ALLOWED_ORIGINS='https://your-domain.com,https://app.your-domain.com'
```

Additional controls:
- `MAX_CONTENT_LENGTH_BYTES`
- `CSP_STRICT_REPORT_ONLY`
- `PROXYFIX_ENABLED`
- `QRS_ROTATE_SESSION_KEY`

---

## 9) API guide (HMAC API v1)

### Endpoints
- `POST /api/v1/keys/create` – create API key/secret (username/password auth, captcha depending on config).
- `POST /api/v1/scan` – authenticated scan request (HMAC headers required).
- `GET /api/v1/weather` – authenticated weather data (plan checks apply).
- `GET /api/v1/weather/report` – authenticated weather report (plan checks apply).

### Authentication headers
Every signed request must include:
- `X-API-Key-Id`
- `X-API-Timestamp` (unix seconds)
- `X-API-Nonce` (random unique string)
- `X-API-Signature` (hex HMAC-SHA3-256)

Canonical message used for signature:

```text
{METHOD}
{PATH}
{TIMESTAMP}
{NONCE}
{SHA3_256_HEX_OF_REQUEST_BODY}
```

Signature:

```text
HMAC_SHA3_256(secret, canonical_bytes)
```

### Example: create key
```bash
curl -X POST http://127.0.0.1:3000/api/v1/keys/create \
  -H 'Content-Type: application/json' \
  -d '{"username":"admin","password":"Admin123!Strong"}'
```

### Example request body (`/api/v1/scan`)
```json
{
  "latitude": "37.7749",
  "longitude": "-122.4194",
  "vehicle_type": "sedan",
  "destination": "downtown",
  "model_selection": "openai"
}
```

### Python example
```python
import time, json, uuid, hmac, hashlib, requests

BASE = "http://127.0.0.1:3000"
KEY_ID = "your_key_id"
SECRET = "your_api_secret"

body = {
    "latitude": "37.7749",
    "longitude": "-122.4194",
    "vehicle_type": "sedan",
    "destination": "downtown",
    "model_selection": "openai",
}
body_bytes = json.dumps(body, separators=(",", ":")).encode()

method = "POST"
path = "/api/v1/scan"
ts = str(int(time.time()))
nonce = uuid.uuid4().hex
body_hash = hashlib.sha3_256(body_bytes).hexdigest()
canonical = f"{method}\n{path}\n{ts}\n{nonce}\n{body_hash}".encode()
sig = hmac.new(SECRET.encode(), canonical, hashlib.sha3_256).hexdigest()

r = requests.post(
    BASE + path,
    data=body_bytes,
    headers={
        "Content-Type": "application/json",
        "X-API-Key-Id": KEY_ID,
        "X-API-Timestamp": ts,
        "X-API-Nonce": nonce,
        "X-API-Signature": sig,
    },
    timeout=20,
)
print(r.status_code, r.text)
```

### TypeScript (Node.js) example
```ts
import crypto from "crypto";

const BASE = "http://127.0.0.1:3000";
const KEY_ID = "your_key_id";
const SECRET = "your_api_secret";

const body = {
  latitude: "37.7749",
  longitude: "-122.4194",
  vehicle_type: "sedan",
  destination: "downtown",
  model_selection: "openai",
};
const bodyStr = JSON.stringify(body);
const method = "POST";
const path = "/api/v1/scan";
const ts = Math.floor(Date.now() / 1000).toString();
const nonce = crypto.randomUUID().replace(/-/g, "");
const bodyHash = crypto.createHash("sha3-256").update(bodyStr).digest("hex");
const canonical = `${method}
${path}
${ts}
${nonce}
${bodyHash}`;
const sig = crypto.createHmac("sha3-256", SECRET).update(canonical).digest("hex");

const res = await fetch(BASE + path, {
  method,
  headers: {
    "Content-Type": "application/json",
    "X-API-Key-Id": KEY_ID,
    "X-API-Timestamp": ts,
    "X-API-Nonce": nonce,
    "X-API-Signature": sig,
  },
  body: bodyStr,
});
console.log(res.status, await res.text());
```

### Rust example
```rust
use sha3::{Digest, Sha3_256};
use hmac::{Hmac, Mac};
use reqwest::header::{HeaderMap, HeaderValue, CONTENT_TYPE};
use std::time::{SystemTime, UNIX_EPOCH};

type HmacSha3 = Hmac<Sha3_256>;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let base = "http://127.0.0.1:3000";
    let path = "/api/v1/scan";
    let key_id = "your_key_id";
    let secret = "your_api_secret";
    let body = r#"{"latitude":"37.7749","longitude":"-122.4194","vehicle_type":"sedan","destination":"downtown","model_selection":"openai"}"#;

    let ts = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs().to_string();
    let nonce = uuid::Uuid::new_v4().simple().to_string();

    let mut hasher = Sha3_256::new();
    hasher.update(body.as_bytes());
    let body_hash = hex::encode(hasher.finalize());

    let canonical = format!("POST
{}
{}
{}
{}", path, ts, nonce, body_hash);
    let mut mac = HmacSha3::new_from_slice(secret.as_bytes())?;
    mac.update(canonical.as_bytes());
    let sig = hex::encode(mac.finalize().into_bytes());

    let mut headers = HeaderMap::new();
    headers.insert(CONTENT_TYPE, HeaderValue::from_static("application/json"));
    headers.insert("X-API-Key-Id", HeaderValue::from_str(key_id)?);
    headers.insert("X-API-Timestamp", HeaderValue::from_str(&ts)?);
    headers.insert("X-API-Nonce", HeaderValue::from_str(&nonce)?);
    headers.insert("X-API-Signature", HeaderValue::from_str(&sig)?);

    let client = reqwest::Client::new();
    let resp = client.post(format!("{}{}", base, path)).headers(headers).body(body.to_string()).send().await?;
    println!("{} {}", resp.status(), resp.text().await?);
    Ok(())
}
```

### Java example
```java
import java.net.URI;
import java.net.http.*;
import java.nio.charset.StandardCharsets;
import java.time.Instant;
import java.util.HexFormat;
import java.util.UUID;
import javax.crypto.Mac;
import javax.crypto.spec.SecretKeySpec;
import org.bouncycastle.jcajce.provider.digest.SHA3;

public class ApiScanExample {
  public static void main(String[] args) throws Exception {
    String base = "http://127.0.0.1:3000";
    String path = "/api/v1/scan";
    String keyId = "your_key_id";
    String secret = "your_api_secret";
    String body = "{"latitude":"37.7749","longitude":"-122.4194","vehicle_type":"sedan","destination":"downtown","model_selection":"openai"}";

    String ts = Long.toString(Instant.now().getEpochSecond());
    String nonce = UUID.randomUUID().toString().replace("-", "");

    byte[] bodyHashBytes = new SHA3.Digest256().digest(body.getBytes(StandardCharsets.UTF_8));
    String bodyHash = HexFormat.of().formatHex(bodyHashBytes);
    String canonical = "POST
" + path + "
" + ts + "
" + nonce + "
" + bodyHash;

    Mac mac = Mac.getInstance("HmacSHA3-256");
    mac.init(new SecretKeySpec(secret.getBytes(StandardCharsets.UTF_8), "HmacSHA3-256"));
    String sig = HexFormat.of().formatHex(mac.doFinal(canonical.getBytes(StandardCharsets.UTF_8)));

    HttpRequest req = HttpRequest.newBuilder(URI.create(base + path))
        .header("Content-Type", "application/json")
        .header("X-API-Key-Id", keyId)
        .header("X-API-Timestamp", ts)
        .header("X-API-Nonce", nonce)
        .header("X-API-Signature", sig)
        .POST(HttpRequest.BodyPublishers.ofString(body))
        .build();

    HttpClient client = HttpClient.newHttpClient();
    HttpResponse<String> resp = client.send(req, HttpResponse.BodyHandlers.ofString());
    System.out.println(resp.statusCode() + " " + resp.body());
  }
}
```

### Common API errors
- `401 Missing API auth headers` – required HMAC headers not sent.
- `401 Invalid API key` / `API key revoked` – key issue.
- `401 Timestamp outside allowed window` – clock skew too large.
- `401 Replay detected` – nonce reused.
- `429 Rate limit exceeded` – per-plan throttles.
- `402 paid_required` – endpoint requires paid plan.

### Best practices
- Keep server clock in sync (NTP).
- Never reuse a nonce.
- Rotate keys periodically and revoke compromised keys.
- Treat API secret like a password (do not log it).
- Use HTTPS in production.

## 10) Complete environment variable index (alphabetical)

`ADMIN_CRON_TOKEN`, `ALERTS_DISPATCH_MAX`, `ALERT_MIN_GAP_SECONDS`, `ALLOWED_HOSTS`, `ALLOWED_ORIGINS`, `ANOM_CORP_PER_HOUR`, `ANOM_CORP_THROTTLE_SECONDS`, `ANOM_FREE_PER_HOUR`, `ANOM_FREE_THROTTLE_SECONDS`, `ANOM_PRO_PER_HOUR`, `ANOM_PRO_THROTTLE_SECONDS`, `API_CACHE_TTL_SCAN_SECONDS`, `API_DAILY_QUOTA`, `API_FREE_CREDITS`, `API_NONCE_TTL_SECONDS`, `API_SIG_TTL_SECONDS`, `BLOG_BACKUP_PATH`, `CAPTCHA_ENABLED`, `CAPTCHA_PROVIDER`, `CAPTCHA_SECRET_KEY`, `CAPTCHA_SITE_KEY`, `CORP_DAILY_QUOTA`, `CORP_MONTHLY_CREDITS`, `CSP_STRICT_REPORT_ONLY`, `CTX_CORP_MAX_TOKENS`, `CTX_FREE_MAX_TOKENS`, `CTX_PRO_MAX_TOKENS`, `DB_TIMEOUT_SECONDS`, `DISABLE_NOMINATIM`, `DKIM_DOMAIN`, `DKIM_ENABLED`, `DKIM_PRIVATE_KEY`, `DKIM_PRIVATE_KEY_PATH`, `DKIM_ROTATE_DAYS`, `DKIM_SELECTOR`, `DKIM_SELECTORS`, `EMAIL_ENABLED`, `EMAIL_FROM`, `EMAIL_INTERNAL_SERVER`, `EMAIL_MIN_INTERVAL_PER_RECIPIENT_SECONDS`, `EMAIL_OUTBOUND_SMTP_PORT`, `EMAIL_OUTBOUND_TIMEOUT_SECONDS`, `EMAIL_SMTP_HOST`, `EMAIL_SMTP_PASS`, `EMAIL_SMTP_PORT`, `EMAIL_SMTP_USER`, `ENABLE_OQS_IMPORT`, `ENCRYPTION_PASSPHRASE`, `ENFORCE_HTTPS`, `GOOGLE_CLIENT_ID`, `GOOGLE_CLIENT_SECRET`, `GOOGLE_OAUTH_ENABLED`, `GOOGLE_OAUTH_REDIRECT_URI`, `GROK_API_KEY`, `GROK_MODEL`, `INVITE_CODE_SECRET_KEY`, `LLAMA_EXPECTED_SHA256`, `LLAMA_LOCAL_ENABLED`, `LLAMA_MODELS_DIR`, `LLAMA_MODEL_FILE`, `LLAMA_MODEL_REPO`, `LOCAL_LLM_ENABLED`, `MAX_CONTENT_LENGTH_BYTES`, `NOMINATIM_URL`, `NOMINATIM_USER_AGENT`, `OPENAI_API_KEY`, `OPENAI_MODEL`, `OPENAI_REASONING_EFFORT`, `PQE_MAILSIG_ENABLED`, `PQ_OQS_ENABLED`, `PQ_OQS_ENCRYPT_ENABLED`, `PQ_OQS_KEM_ALG`, `PQ_OQS_ROTATE_DAYS`, `PQ_OQS_SIG_ALG`, `PROXYFIX_ENABLED`, `PRO_DAILY_QUOTA`, `PRO_MONTHLY_CREDITS`, `QRS_BG_LOCK_PATH`, `QRS_BG_STARTED`, `QRS_BOOTSTRAP_SHOW`, `QRS_COMPRESS_MIN`, `QRS_ENABLE_SEALED`, `QRS_ENV_CAP_BYTES`, `QRS_KEYSTORE_DB_PATH`, `QRS_ROTATE_SESSION_KEY`, `QRS_SESSION_KEY_ROTATION_LOOKBACK`, `QRS_SESSION_KEY_ROTATION_PERIOD_SECONDS`, `RATE_CORP_PER_DAY`, `RATE_CORP_PER_MIN`, `RATE_FREE_PER_DAY`, `RATE_FREE_PER_MIN`, `RATE_PRO_PER_DAY`, `RATE_PRO_PER_MIN`, `REGISTRATION_ENABLED`, `REVGEOCODE_CACHE_TTL_S`, `SESSION_COOKIE_SAMESITE`, `SESSION_COOKIE_SECURE`, `SMTP_FROM`, `SMTP_HOST`, `SMTP_PASS`, `SMTP_PORT`, `SMTP_USER`, `STRICT_PQ2_ONLY`, `STRIPE_CREDIT_PACKS_JSON`, `STRIPE_ENABLED`, `STRIPE_PRICE_CORP_MONTHLY`, `STRIPE_PRICE_PRO_MONTHLY`, `STRIPE_SECRET_KEY`, `STRIPE_WEBHOOK_SECRET`, `WX_CACHE_TTL`, `admin_pass`, `admin_username`.

---

## 11) Core smoke test commands

```bash
python -m py_compile main.py

ENABLE_OQS_IMPORT=0 STRICT_PQ2_ONLY=0 \
INVITE_CODE_SECRET_KEY='replace-with-very-long-random-secret' \
admin_username='admin' admin_pass='VeryStrongPassword123!' \
python main.py

curl -m 6 -s -o /tmp/out -w '%{http_code}\n' http://127.0.0.1:3000/login
curl -m 6 -s -o /tmp/out -w '%{http_code}\n' http://127.0.0.1:3000/register
curl -m 6 -s -o /tmp/out -w '%{http_code}\n' http://127.0.0.1:3000/dashboard
curl -m 6 -s -o /tmp/out -w '%{http_code}\n' -X POST http://127.0.0.1:3000/start_scan
```
