# Security Review (latest hardening pass)

This document summarizes a focused security review of the recently merged `main.py` changes and what was hardened in this pass.

## Scope reviewed
- Request hardening middleware (`before_request` / `after_request`).
- Session/bootstrap secrets and startup requirements.
- Browser mutation origin checks.
- API signing and anti-replay flow.
- Integration surfaces (Stripe/Google/CAPTCHA/SMTP) as configuration boundaries.

## High-priority findings addressed

1. **Host header allowlist missing**
   - Risk: Host header poisoning issues (redirect, URL generation, cache poisoning in misconfigured upstreams).
   - Fix: added `ALLOWED_HOSTS` enforcement middleware with exact host and wildcard-suffix support.

2. **Short app secret accepted**
   - Risk: weak session/CSRF secret material if operator sets small `INVITE_CODE_SECRET_KEY`.
   - Fix: enforce minimum secret length (>=32 bytes) at startup.

3. **Origin matching used prefix check**
   - Risk: prefix-based checks can accept crafted strings beginning with allowed origins.
   - Fix: switched to strict scheme+host(+port) origin equality using URL parsing.

4. **Missing HSTS and sensitive-page cache policy**
   - Risk: weaker TLS downgrade resistance; auth/admin pages potentially cached.
   - Fix: add `Strict-Transport-Security` on secure requests and `Cache-Control: no-store` for auth/admin-sensitive routes.

## Additional existing controls observed
- CSP headers (+ optional strict report-only policy).
- `X-Content-Type-Options`, `X-Frame-Options`, `Referrer-Policy`, `Permissions-Policy`, COOP/CORP.
- Optional HTTPS redirect (`ENFORCE_HTTPS`) and `ProxyFix` support.
- Origin/Referer mutation checks.
- API auth with timestamp + nonce + HMAC + replay protection + compare_digest.
- User ban/rate-limit gates and API quota checks.

## Operational recommendations

1. **Production env baseline**
   - Set `ENFORCE_HTTPS=true`, `SESSION_COOKIE_SECURE=true`, `ALLOWED_HOSTS=...`, `ALLOWED_ORIGINS=...`.
2. **Secrets management**
   - Store all provider secrets in a secret manager, not shell history or repo files.
3. **CSP tightening path**
   - Migrate inline scripts/styles toward nonce-based CSP and remove `'unsafe-inline'` over time.
4. **Monitoring**
   - Monitor `/csp-report` ingestion and login/auth anomalies.
5. **Dependency hygiene**
   - Periodically run `pip-audit`/SCA scanning and pin/rotate vulnerable packages.

## Residual risks (cannot be fully eliminated in one pass)
- Large single-file architecture (`main.py`) increases review complexity and attack-surface comprehension burden.
- Third-party integrations (OAuth/Stripe/SMTP/LLM providers) remain security-sensitive and depend on operator configuration quality.
- Full penetration testing and threat modeling are still recommended before production exposure.
