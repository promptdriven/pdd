"""Pure OpenAI OAuth helpers. Source: chatgpt_oauth_python.prompt."""
from __future__ import annotations
import base64
import json
import math
import os
import secrets
import time
import urllib.error
import urllib.parse
import urllib.request
from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, padding, rsa
from cryptography.hazmat.primitives.asymmetric.utils import encode_dss_signature
from .chatgpt_credentials import CredentialError

ISSUER = 'https://auth.openai.com'
RESOURCE = 'https://api.openai.com/v1'
SCOPES = 'openid profile email offline_access resource.invoke chatgpt.tokens.use.direct'
_SAFE_PROVIDER_ERRORS = {'invalid_grant', 'invalid_client', 'invalid_refresh_token',
                         'token_expired', 'refresh_token_expired',
                         'refresh_token_invalidated', 'refresh_token_reused'}


def require_enabled() -> None:
    """Require explicit opt-in before any local or remote side effects."""
    if os.environ.get('PDD_CHATGPT_SIGN_IN') != '1':
        raise CredentialError('chatgpt_sign_in_disabled')



class _NoRedirect(urllib.request.HTTPRedirectHandler):
    """Refuse HTTP redirects that could forward an OAuth grant."""
    def redirect_request(self, *_args, **_kwargs):
        return None


def request_json(url: str, form: dict | None = None) -> dict:
    """Request the fixed provider endpoint without leaking errors or redirects."""
    data = None if form is None else urllib.parse.urlencode(form).encode()
    request = urllib.request.Request(url, data=data, headers={
        'Accept': 'application/json', 'Content-Type': 'application/x-www-form-urlencoded'})
    try:
        with urllib.request.build_opener(_NoRedirect).open(request, timeout=20) as response:
            result = json.loads(response.read(1024 * 1024))
        if not isinstance(result, dict):
            raise CredentialError('provider_response_invalid')
        return result
    except urllib.error.HTTPError as exc:
        try:
            code = json.loads(exc.read(8192)).get('error')
        except (ValueError, AttributeError):
            code = None
        raise CredentialError(code if isinstance(code, str) and code in _SAFE_PROVIDER_ERRORS
                              else 'provider_request_failed') from exc
    except (OSError, ValueError) as exc:
        raise CredentialError('provider_unavailable') from exc


def _decode(value: str) -> bytes:
    return base64.urlsafe_b64decode(value + '=' * (-len(value) % 4))


def _signature(header: dict, signed: bytes, signature: bytes, jwks: dict) -> None:
    if not isinstance(header.get('kid'), str) or header.get('crit') or header.get('b64') is False:
        raise ValueError('header')
    key = next(k for k in jwks['keys'] if k.get('kid') == header['kid'] and
               k.get('alg', header.get('alg')) == header.get('alg') and
               k.get('use', 'sig') == 'sig')
    if header.get('alg') == 'RS256' and key.get('kty') == 'RSA':
        public = rsa.RSAPublicNumbers(int.from_bytes(_decode(key['e']), 'big'),
                                      int.from_bytes(_decode(key['n']), 'big')).public_key()
        public.verify(signature, signed, padding.PKCS1v15(), hashes.SHA256())
    elif (header.get('alg') == 'ES256' and key.get('kty') == 'EC' and
          key.get('crv') == 'P-256' and len(signature) == 64):
        public = ec.EllipticCurvePublicNumbers(int.from_bytes(_decode(key['x']), 'big'),
                                               int.from_bytes(_decode(key['y']), 'big'),
                                               ec.SECP256R1()).public_key()
        der = encode_dss_signature(int.from_bytes(signature[:32], 'big'),
                                   int.from_bytes(signature[32:], 'big'))
        public.verify(der, signed, ec.ECDSA(hashes.SHA256()))
    else:
        raise ValueError('algorithm')


def _numeric(value) -> bool:
    return (isinstance(value, (int, float)) and not isinstance(value, bool)
            and math.isfinite(value))


def _claims_valid(claims: dict, client_id: str, nonce: str | None, now: float) -> bool:
    audience = claims.get('aud')
    audience_valid = audience == client_id or isinstance(audience, list) and client_id in audience
    if isinstance(audience, list) and len(audience) > 1:
        audience_valid = audience_valid and claims.get('azp') == client_id
    nonce_valid = nonce is None
    if nonce is not None and isinstance(claims.get('nonce'), str):
        nonce_valid = secrets.compare_digest(nonce, claims['nonce'])
    return all([
        claims.get('iss') == ISSUER, audience_valid, nonce_valid,
        _numeric(claims.get('exp')) and claims['exp'] > now,
        _numeric(claims.get('iat')) and claims['iat'] <= now + 5,
        'nbf' not in claims or _numeric(claims['nbf']) and claims['nbf'] <= now + 5,
        isinstance(claims.get('sub'), str) and bool(claims['sub']),
    ])


def verify_identity(token: str, client_id: str, nonce: str | None, *,
                    jwks: dict | None = None, now=time.time) -> dict:
    """Verify signature and OIDC claims, never trusting token-supplied key URLs."""
    try:
        header_part, body_part, signature_part = token.split('.')
        header = json.loads(_decode(header_part))
        claims = json.loads(_decode(body_part))
        keys = jwks if jwks is not None else request_json(ISSUER + '/.well-known/jwks.json')
        _signature(header, (header_part + '.' + body_part).encode(), _decode(signature_part), keys)
        if not _claims_valid(claims, client_id, nonce, now()):
            raise ValueError('claims')
        return claims
    except (InvalidSignature, ValueError, TypeError, KeyError, AttributeError,
            StopIteration, CredentialError) as exc:
        raise CredentialError('id_token_invalid') from exc
