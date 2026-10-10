"""Public OSS browser OAuth. Source: chatgpt_sign_in_python.prompt."""
from __future__ import annotations

import argparse
import base64
from dataclasses import dataclass
import hashlib
from http.server import BaseHTTPRequestHandler, HTTPServer
import json
import math
import secrets
import subprocess
import sys
import threading
import time
import urllib.parse

from .chatgpt_credentials import CredentialError, CredentialStore, label_of, timestamp

from .chatgpt_oauth import ISSUER, RESOURCE, SCOPES, require_enabled, request_json, verify_identity
from .chatgpt_runtime import app_server, transfer

_CALLBACK = '/auth/callback'


def open_system_browser(url: str) -> bool:
    """Open the provider URL without printing retained ID-token hints."""
    executable = '/usr/bin/open' if sys.platform == 'darwin' else 'xdg-open'
    return subprocess.run([executable, url], stdout=subprocess.DEVNULL,
                          stderr=subprocess.DEVNULL, timeout=10, check=False).returncode == 0


@dataclass
class _Ports:
    """Local side effects supplied by runtime or offline tests."""
    request: object = request_json
    verify: object = verify_identity
    browser: object = open_system_browser
    now: object = time.time
    timeout: float = 300


class SignIn:
    """A bounded local OAuth attempt with safe public state."""
    def __init__(self, store: CredentialStore | None = None, **ports):
        require_enabled()
        self.store = store or CredentialStore()
        self.ports = _Ports(**ports)
        self._mutex = threading.RLock()
        self._pending = None
        self._retry = None
        self._closed = False
        self._status = self._state('idle')

    @staticmethod
    def _state(state: str, error: str | None = None) -> dict:
        return {'method': 'chatgpt', 'state': state, 'accountKey': None,
                'label': None, 'errorCode': error, 'updatedAt': timestamp()}

    def status(self) -> dict:
        """Return only safe state; never return the browser URL."""
        with self._mutex:
            return dict(self._status)

    def start(self, account_key: str | None = None) -> dict:
        """Start listener before browser, leaving the active account untouched."""
        with self._mutex:
            if self._closed:
                raise CredentialError('sign_in_closed')
            if self._pending:
                return self.status()
            selected = self.store.read(account_key) if account_key else None
            retry = self._retry if self._retry and self._retry[0] == account_key else None
            client_id = selected['client_id'] if selected else (retry[1] if retry else None)
            handle_callback = self._callback

            class Handler(BaseHTTPRequestHandler):
                """Quiet loopback callback for this single attempt."""
                def log_message(self, *_args):
                    pass

                def do_GET(self):
                    """Handle the exact callback path, without logging its query."""
                    parsed = urllib.parse.urlsplit(self.path)
                    if parsed.path != _CALLBACK:
                        self.send_error(404)
                        return
                    query = urllib.parse.parse_qs(parsed.query, keep_blank_values=True)
                    result = handle_callback(attempt, query)
                    self.send_response(200 if result else 400)
                    self.send_header('Content-Type', 'text/plain; charset=utf-8')
                    self.send_header('Cache-Control', 'no-store')
                    self.send_header('Referrer-Policy', 'no-referrer')
                    self.end_headers()
                    message = b'You can return to PDD.' if result else b'Sign-in did not complete.'
                    self.wfile.write(message)

            server = HTTPServer(('127.0.0.1', 0), Handler)
            verifier = secrets.token_urlsafe(48)
            attempt = {'server': server, 'state': secrets.token_urlsafe(32),
                       'nonce': secrets.token_urlsafe(32), 'verifier': verifier,
                       'redirect_uri': f'http://127.0.0.1:{server.server_port}{_CALLBACK}',
                       'client_id': client_id, 'selected': selected,
                       'account_key': account_key, 'consumed': False,
                       'expires_at': self.ports.now() + self.ports.timeout}
            params = {'client_id': client_id or 'dynamic_agent_client',
                      'ext_agent_host_id': self.store.host_id(),
                      'response_type': 'code', 'redirect_uri': attempt['redirect_uri'],
                      'scope': SCOPES, 'resource': RESOURCE, 'state': attempt['state'],
                      'nonce': attempt['nonce'], 'code_challenge_method': 'S256',
                      'code_challenge': base64.urlsafe_b64encode(
                          hashlib.sha256(verifier.encode()).digest()).decode().rstrip('=')}
            if client_id is None:
                params['agent_name_hint'] = 'PDD'
            elif selected:
                if selected.get('id_token'):
                    params['id_token_hint'] = selected['id_token']
                if selected.get('email'):
                    params['login_hint'] = selected['email']
            self._pending = attempt
            self._status = self._state('pending')
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            timer = threading.Timer(self.ports.timeout, lambda: self._expire(attempt))
            timer.daemon = True
            attempt['timer'] = timer
            timer.start()
            try:
                url = ISSUER + '/api/accounts/authorize?' + urllib.parse.urlencode(params)
                if not self.ports.browser(url):
                    raise CredentialError('browser_open_failed')
            except (OSError, subprocess.TimeoutExpired, CredentialError):
                self._finish(attempt, 'failed', 'browser_open_failed')
            return self.status()

    def _finish(self, attempt: dict, state: str, error: str | None = None) -> None:
        with self._mutex:
            if self._pending is not attempt:
                return
            self._pending = None
            attempt['timer'].cancel()
            self._status = self._state(state, error)
            # shutdown must run outside the callback's server thread.
            def stop():
                attempt['server'].shutdown()
                attempt['server'].server_close()
            threading.Thread(target=stop, daemon=True).start()

    def _expire(self, attempt: dict) -> None:
        self._finish(attempt, 'expired', 'sign_in_expired')

    def _callback(self, attempt: dict, query: dict) -> bool:
        with self._mutex:
            valid = [self._pending is attempt, not attempt['consumed'],
                     self.ports.now() < attempt['expires_at'],
                     all(len(values) == 1 for values in query.values()),
                     secrets.compare_digest(query.get('state', [''])[0], attempt['state'])]
            if not all(valid):
                return False
            attempt['consumed'] = True
            if 'error' in query:
                denied = query['error'][0] == 'access_denied'
                self._finish(attempt, 'cancelled' if denied else 'failed',
                             'access_denied' if denied else 'authorization_failed')
                return False
            supplied = query.get('client_id', [None])[0]
            client_id = attempt['client_id'] or supplied
            if (not client_id or client_id == 'dynamic_agent_client' or
                    supplied is not None and supplied != client_id or
                    not query.get('code', [''])[0]):
                self._finish(attempt, 'failed', 'registration_incomplete')
                return False
            self._retry = (attempt['account_key'], client_id)
        try:
            tokens = self.ports.request(ISSUER + '/api/accounts/oauth/token', {
                'grant_type': 'authorization_code', 'client_id': client_id,
                'code': query['code'][0], 'code_verifier': attempt['verifier'],
                'redirect_uri': attempt['redirect_uri'], 'resource': RESOURCE})
            claims = self.ports.verify(tokens['id_token'], client_id, attempt['nonce'])
            selected = attempt['selected']
            if selected and claims['sub'] != selected['subject']:
                raise CredentialError('account_identity_mismatch')
            if (tokens.get('token_type', '').lower() != 'bearer' or
                    not all(isinstance(tokens.get(k), str) and tokens[k]
                            for k in ('access_token', 'refresh_token', 'id_token')) or
                    not isinstance(tokens.get('expires_in'), (int, float)) or
                    not math.isfinite(tokens['expires_in']) or tokens['expires_in'] <= 0):
                raise CredentialError('token_response_invalid')
            host = self.store.host_id()
            record = {'issuer': ISSUER, 'subject': claims['sub'], 'client_id': client_id,
                      'email': label_of(claims.get('email', '')), 'ext_agent_host_id': host,
                      'refresh_owner': host, 'scopes': tokens.get('scope', '').split(),
                      'saved_at': timestamp(),
                      'expires_at': self.ports.now() + tokens['expires_in'],
                      'earliest_refresh_at': tokens.get('earliest_refresh_at', 0),
                      **{k: tokens[k] for k in
                         ('access_token', 'refresh_token', 'id_token', 'token_type')}}
            with self._mutex:
                if self._pending is not attempt or self.ports.now() >= attempt['expires_at']:
                    return False
                key = self.store.key(record)
                with self.store.lock(key, blocking=False):
                    self.store.write(record)
                self._finish(attempt, 'connected')
                self._status = self.store.summary(key)
                self._retry = None
            return True
        except (CredentialError, KeyError, TypeError, ValueError, OSError,
                subprocess.TimeoutExpired) as exc:
            code = exc.code if isinstance(exc, CredentialError) else 'sign_in_failed'
            self._finish(attempt, 'failed', code)
            return False

    def cancel(self) -> dict:
        """Cancel an attempt, preventing a late token exchange from saving."""
        with self._mutex:
            if self._pending:
                self._finish(self._pending, 'cancelled')
            return self.status()

    def close(self) -> dict:
        """Close this helper without changing any saved account."""
        with self._mutex:
            self.cancel()
            self._closed = True
            self._status = self._state('closed')
            return self.status()


def serve() -> None:
    """A local control pipe; no OAuth values are serialized to its replies."""
    helper = SignIn()
    try:
        for line in sys.stdin:
            request_id = None
            try:
                command = json.loads(line)
                request_id = command['id']
                operation = command['operation']
                if operation not in {'start', 'status', 'cancel', 'close'}:
                    raise CredentialError('operation_invalid')
                result = (helper.start(command.get('accountKey')) if operation == 'start'
                          else getattr(helper, operation)())
                reply = {'id': request_id, 'result': result}
            except (CredentialError, KeyError, TypeError, ValueError, OSError,
                subprocess.TimeoutExpired) as exc:
                reply = {'id': request_id, 'errorCode': exc.code if isinstance(exc, CredentialError)
                         else 'request_invalid'}
            print(json.dumps(reply), flush=True)
            if helper.status()["state"] == "closed":
                break
    finally:
        helper.close()


def main() -> int:
    """Minimal local entry point; credential import is only over stdin."""
    parser = argparse.ArgumentParser(description='Local Continue with ChatGPT preview')
    parser.add_argument('operation',
                        choices=['serve', 'status', 'host-id', 'import', 'transfer', 'app-server'])
    parser.add_argument('--account')
    parser.add_argument('--destination')
    parser.add_argument('--codex-bin')
    parser.add_argument('--codex-home')
    args = parser.parse_args()
    try:
        require_enabled()
        if args.operation == 'serve':
            serve()
            return 0
        store = CredentialStore()
        if args.operation == 'host-id':
            result = {'ext_agent_host_id': store.host_id()}
        elif args.operation == 'import':
            result = {'accountKey': store.import_record(json.loads(sys.stdin.read(1024 * 1024)))}
        elif args.operation == 'status':
            result = store.summary(args.account) if args.account else SignIn(store).status()
        elif args.operation == 'transfer':
            result = transfer(store, args.account, args.destination or '')
        else:
            if not args.codex_bin or not args.codex_home:
                raise CredentialError('codex_configuration_missing')
            return app_server(store, args.account, args.codex_bin, args.codex_home)
        print(json.dumps(result))
        return 0
    except (CredentialError, KeyError, TypeError, ValueError, OSError,
                subprocess.TimeoutExpired) as exc:
        print(json.dumps({'errorCode': exc.code if isinstance(exc, CredentialError)
                          else 'chatgpt_operation_failed'}))
        return 1


if __name__ == '__main__':
    sys.exit(main())
