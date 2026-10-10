"""Offline OAuth proof. All identities, signing keys and tokens are generated fixtures."""
import base64
import json
import os
import select
import subprocess
import sys
import threading
import time
from types import SimpleNamespace
import urllib.error
import urllib.parse
import urllib.request

import pytest
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import padding, rsa

from pdd.chatgpt_credentials import CredentialError, CredentialStore
from pdd.chatgpt_sign_in import SignIn, verify_identity
from pdd.chatgpt_runtime import access_record, app_server, transfer


def b64(value):
    return base64.urlsafe_b64encode(value).decode().rstrip('=')


@pytest.fixture
def signing():
    private = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    public = private.public_key().public_numbers()
    jwks = {'keys': [{'kid': 'offline', 'alg': 'RS256', 'kty': 'RSA', 'use': 'sig',
                     'n': b64(public.n.to_bytes(256, 'big')), 'e': b64(public.e.to_bytes(3, 'big'))}]}
    def token(claims, header=None):
        h = {'alg': 'RS256', 'kid': 'offline'} if header is None else header
        message = b64(json.dumps(h).encode()) + '.' + b64(json.dumps(claims).encode())
        signature = private.sign(message.encode(), padding.PKCS1v15(), hashes.SHA256())
        return message + '.' + b64(signature)
    return jwks, token


def claims(client='oaiapp_offline', nonce='nonce', subject='offline-subject'):
    return {'iss': 'https://auth.openai.com', 'sub': subject, 'aud': client,
            'iat': time.time() - 1, 'exp': time.time() + 3600, 'nonce': nonce,
            'email': 'offline@example.invalid'}


def record(store, client='oaiapp_offline'):
    return {'issuer': 'https://auth.openai.com', 'subject': 'offline-subject',
            'client_id': client, 'email': 'offline@example.invalid', 'ext_agent_host_id': store.host_id(),
            'refresh_owner': store.host_id(), 'access_token': 'offline-access',
            'refresh_token': 'offline-refresh', 'id_token': 'offline-id', 'token_type': 'Bearer',
            'scopes': ['openid', 'chatgpt.tokens.use.direct'], 'expires_at': time.time() + 3600,
            'earliest_refresh_at': 0, 'saved_at': '2026-10-09T00:00:00+00:00'}


@pytest.fixture(autouse=True)
def enabled(monkeypatch):
    monkeypatch.setenv('PDD_CHATGPT_SIGN_IN', '1')


def setup_helper(tmp_path, signing, *, scope='chatgpt.tokens.use.direct openid', selected_subject=None, request_hook=None):
    jwks, token = signing
    browser_urls, forms = [], []
    def request(url, form):
        forms.append((url, form))
        if request_hook:
            request_hook()
        params = urllib.parse.parse_qs(urllib.parse.urlsplit(browser_urls[-1]).query)
        c = claims(form['client_id'], params['nonce'][0], selected_subject or 'offline-subject')
        return {'id_token': token(c), 'access_token': 'offline-access', 'refresh_token': 'offline-refresh',
                'scope': scope, 'token_type': 'Bearer', 'expires_in': 3600}
    helper = SignIn(CredentialStore(tmp_path / 'credentials'), request=request,
                    verify=lambda tok, client, nonce: verify_identity(tok, client, nonce, jwks=jwks),
                    browser=lambda url: browser_urls.append(url) or True)
    return helper, browser_urls, forms


def callback(url, changes=None):
    params = urllib.parse.parse_qs(urllib.parse.urlsplit(url).query)
    query = {'state': params['state'][0], 'code': 'offline-code', 'client_id': 'oaiapp_offline'}
    query.update(changes or {})
    query = {k: v for k, v in query.items() if v is not None}
    uri = params['redirect_uri'][0] + '?' + urllib.parse.urlencode(query)
    try:
        with urllib.request.urlopen(uri, timeout=3) as response:
            return response.status
    except urllib.error.HTTPError as exc:
        return exc.code


# Wrong: truthy feature strings can start local OAuth.
@pytest.mark.parametrize('value', ['0', 'true', 'yes', ''])
def test_default_off(tmp_path, monkeypatch, value):
    monkeypatch.setenv('PDD_CHATGPT_SIGN_IN', value)
    with pytest.raises(CredentialError, match='chatgpt_sign_in_disabled'):
        SignIn()


# Wrong: decode-only JWT validation accepts untrusted identity or claims.
@pytest.mark.parametrize('field,value', [('iss', 'https://evil.invalid'), ('aud', 'other'),
    ('exp', 1), ('iat', time.time()+600), ('nbf', time.time()+600), ('nonce', 'wrong'), ('sub', '')])
def test_oidc_rejects_invalid_claims(signing, field, value):
    jwks, token = signing
    c = claims(); c[field] = value
    with pytest.raises(CredentialError, match='id_token_invalid'):
        verify_identity(token(c), 'oaiapp_offline', 'nonce', jwks=jwks)


def test_oidc_rejects_wrong_signature_and_algorithm(signing):
    jwks, token = signing
    valid = token(claims())
    assert verify_identity(valid, 'oaiapp_offline', 'nonce', jwks=jwks)['sub'] == 'offline-subject'
    parts = valid.split('.'); parts[1] = b64(json.dumps(claims(subject='attacker')).encode())
    for invalid in ['.'.join(parts), token(claims(), {'alg': 'none', 'kid': 'offline'})]:
        with pytest.raises(CredentialError, match='id_token_invalid'):
            verify_identity(invalid, 'oaiapp_offline', 'nonce', jwks=jwks)


# Wrong: dynamic placeholder is exchanged/saved or tokens reach status.
def test_browser_pkce_registration_and_safe_status(tmp_path, signing, enabled):
    helper, urls, forms = setup_helper(tmp_path, signing)
    try:
        assert helper.start()['state'] == 'pending'
        params = urllib.parse.parse_qs(urllib.parse.urlsplit(urls[0]).query)
        assert params['client_id'] == ['dynamic_agent_client']
        assert params['agent_name_hint'] == ['PDD']
        assert params['redirect_uri'][0].startswith('http://127.0.0.1:')
        assert callback(urls[0]) == 200
        status = helper.status(); key = status['accountKey']
        assert status['state'] == 'connected'
        assert set(status) == {'method', 'state', 'accountKey', 'label', 'errorCode', 'updatedAt'}
        form = forms[0][1]
        assert form['client_id'] == 'oaiapp_offline'
        assert form['redirect_uri'] == params['redirect_uri'][0]
        import hashlib
        assert params['code_challenge'] == [b64(hashlib.sha256(form['code_verifier'].encode()).digest())]
        saved = helper.store.read(key)
        assert saved['subject'] == 'offline-subject'
        assert (helper.store.root / (key + '.json')).stat().st_mode & 0o777 == 0o600
        assert helper.store.root.stat().st_mode & 0o777 == 0o700
        helper.start(key)
        returning = urllib.parse.parse_qs(urllib.parse.urlsplit(urls[-1]).query)
        assert 'agent_name_hint' not in returning
        assert returning['client_id'] == ['oaiapp_offline']
        assert 'id_token_hint' in returning
        assert params['state'] != returning['state']
        assert params['ext_agent_host_id'] == returning['ext_agent_host_id']
        assert callback(urls[-1], {'client_id': None}) == 200
    finally:
        helper.close()


# Wrong: a callback with the wrong state can deny or exchange another attempt.
def test_wrong_state_denial_and_incomplete_registration(tmp_path, signing, enabled):
    helper, urls, forms = setup_helper(tmp_path, signing)
    try:
        helper.start()
        assert callback(urls[-1], {'state': 'wrong', 'error': 'access_denied'}) == 400
        assert helper.status()['state'] == 'pending'
        assert not forms
        assert callback(urls[-1], {'error': 'access_denied'}) == 400
        assert helper.status()['state'] == 'cancelled'
        assert not forms
        helper.start()
        assert callback(urls[-1], {'client_id': None}) == 400
        assert helper.status()['errorCode'] == 'registration_incomplete'
        assert not forms
    finally:
        helper.close()


# Wrong: returning account or granted-scope validation is skipped.
def test_identity_mismatch_keeps_saved_registration(tmp_path, signing, enabled):
    helper, urls, _ = setup_helper(tmp_path, signing, selected_subject='other-person')
    key = helper.store.write(record(helper.store))
    try:
        helper.start(key)
        assert callback(urls[-1]) == 400
        assert helper.status()['errorCode'] == 'account_identity_mismatch'
        assert helper.store.read(key)['refresh_token'] == 'offline-refresh'
    finally:
        helper.close()


def test_missing_plan_scope_retains_identity_only(tmp_path, signing, enabled):
    helper, urls, _ = setup_helper(tmp_path, signing, scope='openid email')
    try:
        helper.start(); assert callback(urls[-1]) == 200
        assert helper.status()['state'] == 'plan_disabled'
        with pytest.raises(CredentialError, match='chatgpt_plan_disabled'):
            access_record(helper.store, helper.status()['accountKey'])
    finally:
        helper.close()


# Wrong: cancellation changes UI but a delayed exchange still saves a token.
def test_cancel_during_exchange_prevents_save(tmp_path, signing, enabled):
    entered, release = threading.Event(), threading.Event()
    def block():
        entered.set(); assert release.wait(3)
    helper, urls, _ = setup_helper(tmp_path, signing, request_hook=block)
    helper.start()
    client = threading.Thread(target=lambda: callback(urls[-1]))
    client.start()
    try:
        assert entered.wait(3)
        helper.cancel(); release.set(); client.join(3)
        assert helper.status()['state'] == 'cancelled'
        assert not list(helper.store.root.glob('[a-f0-9]*.json'))
    finally:
        release.set(); helper.close(); client.join(3)


# Wrong: refresh posts scope/dynamic client or loses rotated credentials.
def test_refresh_is_atomic_and_uses_issued_client(tmp_path):
    store = CredentialStore(tmp_path / 'credentials')
    saved = record(store); saved['expires_at'] = time.time() - 10
    key = store.write(saved); forms = []
    def request(url, form):
        forms.append(form)
        return {'access_token': 'renewed-access', 'refresh_token': 'renewed-refresh',
                'token_type': 'Bearer', 'expires_in': 3600}
    updated = access_record(store, key, request=request)
    assert forms[0] == {'grant_type': 'refresh_token', 'client_id': saved['client_id'],
                        'refresh_token': 'offline-refresh', 'resource': 'https://api.openai.com/v1'}
    assert updated['refresh_token'] == store.read(key)['refresh_token'] == 'renewed-refresh'
    assert updated['scopes'] == saved['scopes']
    access_record(store, key, request=lambda *args: pytest.fail('duplicate refresh'))


@pytest.mark.parametrize('code,cleared', [('invalid_grant', True), ('provider_unavailable', False)])
def test_refresh_recovery_preserves_registration(tmp_path, code, cleared):
    store = CredentialStore(tmp_path / 'credentials')
    saved = record(store); saved['expires_at'] = 1; key = store.write(saved)
    def request(*args):
        raise CredentialError(code)
    with pytest.raises(CredentialError):
        access_record(store, key, request=request)
    after = store.read(key)
    assert after['client_id'] == saved['client_id']
    assert ('access_token' not in after) is cleared


# Wrong: a host import deduplicates email or replaces the VM host ID.
def test_workspace_separation_and_vm_handoff(tmp_path):
    source = CredentialStore(tmp_path / 'mac'); target = CredentialStore(tmp_path / 'vm')
    vm_host = target.host_id(); first = record(source); key = source.write(first)
    other = record(source, client='oaiapp_second_workspace')
    assert source.write(other) != key
    assert source.host_id() != vm_host
    calls = []
    def ssh(argv, **kwargs):
        calls.append((argv, kwargs))
        if argv[-1].endswith('host-id'):
            return SimpleNamespace(returncode=0, stdout=b'{}')
        imported = target.import_record(json.loads(kwargs['input']))
        return SimpleNamespace(returncode=0, stdout=json.dumps({'accountKey': imported}).encode())
    assert transfer(source, key, 'owner@vm', run=ssh)['state'] == 'transferred'
    assert target.read(key)['refresh_owner'] == target.read(key)['ext_agent_host_id'] == vm_host
    assert target.host_id() == vm_host
    assert 'access_token' not in source.read(key)
    assert 'offline-access' not in repr(calls[1][0])
    with pytest.raises(CredentialError, match='credential_transferred'):
        access_record(source, key)
    assert access_record(target, key)['access_token'] == 'offline-access'


def test_uncertain_transfer_fences_source(tmp_path):
    store = CredentialStore(tmp_path / 'mac'); key = store.write(record(store)); count = 0
    def ssh(*args, **kwargs):
        nonlocal count
        count += 1
        return SimpleNamespace(returncode=0 if count == 1 else 1, stdout=b'{}')
    with pytest.raises(CredentialError, match='ssh_transfer_uncertain'):
        transfer(store, key, 'owner@vm', run=ssh)
    assert store.read(key)['transfer_state'] == 'pending'
    with pytest.raises(CredentialError, match='credential_transferred'):
        access_record(store, key)


# Wrong: one exclusive credential lock covers a child's entire runtime lifetime.
def test_two_real_process_readers_allow_refresh_and_refuse_transfer(tmp_path):
    store = CredentialStore(tmp_path / 'credentials'); key = store.write(record(store))
    script = '''import sys
from types import SimpleNamespace
from pathlib import Path
from pdd.chatgpt_credentials import CredentialStore
from pdd.chatgpt_runtime import app_server
def run(*args, **kwargs):
 print('ready', flush=True)
 sys.stdin.readline()
 return SimpleNamespace(returncode=0)
app_server(CredentialStore(Path(sys.argv[1])),sys.argv[2],'/offline/codex','/offline/home',run=run)
'''
    children = []
    try:
        for _ in range(2):
            child = subprocess.Popen([sys.executable, '-c', script, str(store.root), key],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            children.append(child)
            assert select.select([child.stdout], [], [], 30)[0]
            assert child.stdout.readline() == b'ready\n'
        saved = store.read(key); saved['expires_at'] = 1
        with store.lock(key): store.write(saved)
        updated = access_record(store, key, request=lambda *a: {
            'access_token': 'new-access', 'refresh_token': 'new-refresh',
            'token_type': 'Bearer', 'expires_in': 3600})
        assert updated['access_token'] == 'new-access'
        with pytest.raises(CredentialError, match='credential_busy'):
            transfer(store, key, 'owner@vm', run=lambda *a, **k: pytest.fail('SSH while in use'))
        for child in children:
            child.kill(); child.wait(timeout=5)
        with store.usage(key, exclusive=True):
            pass  # Crash releases both shared leases.
    finally:
        for child in children:
            if child.poll() is None: child.kill(); child.wait(timeout=5)


# Wrong: token goes in argv/parent env or existing Codex home is replaced.
def test_appserver_child_credentials_and_home(tmp_path):
    store = CredentialStore(tmp_path / 'credentials'); key = store.write(record(store)); calls = []
    env = {'PATH': '/bin', 'OPENAI_API_KEY': 'fake-api', 'GH_TOKEN': 'fake-github'}
    def run(argv, **kwargs):
        calls.append((argv, kwargs)); return SimpleNamespace(returncode=0)
    assert app_server(store, key, '/tested/codex', '/existing/home', run=run, env=env) == 0
    argv, options = calls[0]
    assert argv[:4] == ['/tested/codex', 'app-server', '--listen', 'stdio://']
    assert 'offline-access' not in repr(argv)
    assert options['env'] == {'PATH': '/bin', 'CODEX_HOME': '/existing/home', 'ACCESS_TOKEN': 'offline-access'}
    assert env['OPENAI_API_KEY'] == 'fake-api'
    assert 'model_providers.openai_chatgpt_plan.supports_websockets=false' in argv


# Wrong: a planted symlink or loose file permissions leak local credentials.
def test_storage_rejects_unsafe_permissions_and_symlinks(tmp_path):
    store = CredentialStore(tmp_path / 'credentials'); key = store.write(record(store))
    path = store.root / (key + '.json'); path.chmod(0o644)
    with pytest.raises(CredentialError, match='credential_storage_unsafe'): store.read(key)
    path.chmod(0o600); path.unlink(); path.symlink_to(tmp_path / 'outside')
    with pytest.raises(CredentialError, match='credential_storage_unsafe'): store.read(key)

# Wrong: killing the wrapper releases transfer exclusion while its child runs.
def test_child_inherits_runtime_lease_after_wrapper_exit(tmp_path):
    store = CredentialStore(tmp_path / 'credentials'); key = store.write(record(store))
    executable = tmp_path / 'offline-codex'
    executable.write_text(f'#!{sys.executable}\nimport sys\nprint("ready", flush=True)\nsys.stdin.readline()\n')
    executable.chmod(0o700)
    script = '''import sys
from pathlib import Path
from pdd.chatgpt_credentials import CredentialStore
from pdd.chatgpt_runtime import app_server
app_server(CredentialStore(Path(sys.argv[1])),sys.argv[2],sys.argv[3],'/offline/home')
'''
    wrapper = subprocess.Popen([sys.executable, '-c', script, str(store.root), key, str(executable)],
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        assert select.select([wrapper.stdout], [], [], 30)[0]
        assert wrapper.stdout.readline() == b'ready\n'
        wrapper.kill(); wrapper.wait(timeout=5)
        with pytest.raises(CredentialError, match='credential_busy'):
            transfer(store, key, 'owner@vm', run=lambda *a, **k: pytest.fail('SSH while child alive'))
        wrapper.stdin.write(b'finish\n'); wrapper.stdin.flush()
        assert select.select([wrapper.stdout], [], [], 5)[0]
        assert wrapper.stdout.read() == b''
        with store.usage(key, exclusive=True):
            pass
    finally:
        if wrapper.poll() is None: wrapper.kill(); wrapper.wait(timeout=5)
        wrapper.stdin.close()

# Wrong: claimed ES256 support accepts a DER signature instead of JOSE bytes.
def test_es256_signature_and_nonce(signing):
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature
    private = ec.generate_private_key(ec.SECP256R1())
    point = private.public_key().public_numbers()
    jwks = {'keys': [{'kid': 'ec-offline', 'alg': 'ES256', 'kty': 'EC', 'crv': 'P-256',
                     'x': b64(point.x.to_bytes(32, 'big')), 'y': b64(point.y.to_bytes(32, 'big'))}]}
    message = b64(json.dumps({'alg': 'ES256', 'kid': 'ec-offline'}).encode()) + '.' + b64(json.dumps(claims()).encode())
    r, s = decode_dss_signature(private.sign(message.encode(), ec.ECDSA(hashes.SHA256())))
    token = message + '.' + b64(r.to_bytes(32, 'big') + s.to_bytes(32, 'big'))
    assert verify_identity(token, 'oaiapp_offline', 'nonce', jwks=jwks)['sub'] == 'offline-subject'
    with pytest.raises(CredentialError, match='id_token_invalid'):
        verify_identity(token, 'oaiapp_offline', 'wrong-nonce', jwks=jwks)


# Wrong: returning callback silently changes workspace registration.
def test_changed_returning_client_does_not_exchange(tmp_path, signing, enabled):
    helper, urls, forms = setup_helper(tmp_path, signing)
    key = helper.store.write(record(helper.store))
    try:
        helper.start(key)
        assert callback(urls[-1], {'client_id': 'oaiapp_other'}) == 400
        assert not forms
        assert helper.store.read(key)['client_id'] == 'oaiapp_offline'
    finally:
        helper.close()


# Wrong: invalid_grant retries the spent code or registers a second client.
def test_invalid_grant_starts_fresh_oauth_with_issued_client(tmp_path, signing, enabled):
    helper, urls, _ = setup_helper(tmp_path, signing)
    def invalid(*args): raise CredentialError('invalid_grant')
    helper.ports.request = invalid
    try:
        helper.start(); old = urllib.parse.parse_qs(urllib.parse.urlsplit(urls[-1]).query)
        assert callback(urls[-1]) == 400
        helper.start(); new = urllib.parse.parse_qs(urllib.parse.urlsplit(urls[-1]).query)
        assert new['client_id'] == ['oaiapp_offline']
        assert 'agent_name_hint' not in new
        assert new['state'] != old['state']
        assert new['code_challenge'] != old['code_challenge']
    finally:
        helper.close()

# Wrong: normal wrapper close abandons its child and leaves the use lease alive.
def test_wrapper_term_confirms_owned_child_cleanup(tmp_path):
    store = CredentialStore(tmp_path / 'credentials'); key = store.write(record(store))
    executable = tmp_path / 'offline-codex'
    executable.write_text(f'#!{sys.executable}\nimport signal,time\nsignal.signal(signal.SIGTERM,signal.SIG_IGN)\nprint("ready",flush=True)\ntime.sleep(30)\n')
    executable.chmod(0o700)
    script = '''import sys
from pathlib import Path
from pdd.chatgpt_credentials import CredentialStore
from pdd.chatgpt_runtime import app_server
app_server(CredentialStore(Path(sys.argv[1])),sys.argv[2],sys.argv[3],'/offline/home')
'''
    wrapper = subprocess.Popen([sys.executable, '-c', script, str(store.root), key, str(executable)],
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        assert select.select([wrapper.stdout], [], [], 30)[0]
        assert wrapper.stdout.readline() == b'ready\n'
        wrapper.terminate(); wrapper.wait(timeout=6)
        assert select.select([wrapper.stdout], [], [], 2)[0]
        assert wrapper.stdout.read() == b''
        with store.usage(key, exclusive=True): pass
    finally:
        if wrapper.poll() is None: wrapper.kill(); wrapper.wait(timeout=5)
        wrapper.stdin.close()
