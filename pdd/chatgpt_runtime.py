"""Local SIWC runtime. Source: chatgpt_runtime_python.prompt."""
from __future__ import annotations

import os
import re
import subprocess
import signal
import threading
import time
import json

from .chatgpt_credentials import CredentialError, CredentialStore, timestamp
from .chatgpt_oauth import require_enabled, request_json, verify_identity

RESOURCE = 'https://api.openai.com/v1'
_TERMINAL = {'invalid_grant', 'invalid_refresh_token', 'token_expired',
             'refresh_token_expired', 'refresh_token_invalidated', 'refresh_token_reused'}


def _run_child(argv: list, *, env: dict, check: bool, pass_fds: tuple):
    """Forward wrapper shutdown to its child, then confirm child exit."""
    with subprocess.Popen(argv, env=env, pass_fds=pass_fds) as child:
        timers = []

        def kill_child():
            if child.poll() is None:
                try:
                    child.kill()
                except ProcessLookupError:
                    pass

        def stop(signum, _frame):
            if child.poll() is not None:
                return
            try:
                child.send_signal(signum)
            except ProcessLookupError:
                return
            timer = threading.Timer(3, kill_child)
            timer.daemon = True
            timers.append(timer)
            timer.start()

        previous = {sig: signal.signal(sig, stop) for sig in (signal.SIGTERM, signal.SIGINT)}
        try:
            result = subprocess.CompletedProcess(argv, child.wait())
            if check and result.returncode:
                raise subprocess.CalledProcessError(result.returncode, argv)
            return result
        finally:
            for timer in timers:
                timer.cancel()
            if child.poll() is None:
                kill_child()
                child.wait()
            for sig, handler in previous.items():
                signal.signal(sig, handler)


def access_record(store: CredentialStore, key: str, *, request=None, verify=None,
                  now=time.time) -> dict:
    """Refresh one local session while serializing its rotating token."""
    require_enabled()
    with store.lock(key):
        return _access_locked(store, key, request or request_json, verify or verify_identity, now)


def _access_locked(store, key, request, verify, now) -> dict:
    request = request or request_json
    verify = verify or verify_identity
    record = store.read(key)
    if record.get('transfer_state') or record.get('refresh_owner') != store.host_id():
        raise CredentialError('credential_transferred')
    if 'chatgpt.tokens.use.direct' not in record.get('scopes', []):
        raise CredentialError('chatgpt_plan_disabled')
    if not record.get('access_token'):
        raise CredentialError('sign_in_required')
    if record['expires_at'] > now() + 60:
        return record
    if record.get('earliest_refresh_at', 0) > now():
        if record['expires_at'] <= now():
            raise CredentialError('refresh_not_ready')
        return record
    try:
        tokens = request('https://auth.openai.com/api/accounts/oauth/token', {
            'grant_type': 'refresh_token', 'client_id': record['client_id'],
            'refresh_token': record['refresh_token'], 'resource': RESOURCE})
    except CredentialError as exc:
        if exc.code in _TERMINAL:
            for field in ('access_token', 'refresh_token', 'id_token'):
                record.pop(field, None)
            store.write(record)
            raise CredentialError('sign_in_required') from exc
        raise
    if tokens.get('id_token'):
        claims = verify(tokens['id_token'], record['client_id'], None)
        if claims['sub'] != record['subject']:
            raise CredentialError('account_identity_mismatch')
    if (not tokens.get('access_token') or not tokens.get('refresh_token') or
            tokens.get('token_type', '').lower() != 'bearer' or
            not isinstance(tokens.get('expires_in'), (int, float)) or tokens['expires_in'] <= 0):
        raise CredentialError('token_response_invalid')
    record.update({k: tokens[k] for k in ('access_token', 'refresh_token', 'token_type')})
    if tokens.get('id_token'):
        record['id_token'] = tokens['id_token']
    record.update(expires_at=now() + tokens['expires_in'], saved_at=timestamp(),
                  earliest_refresh_at=tokens.get('earliest_refresh_at', 0))
    if 'scope' in tokens:
        record['scopes'] = tokens['scope'].split()
    store.write(record)
    if 'chatgpt.tokens.use.direct' not in record['scopes']:
        raise CredentialError('chatgpt_plan_disabled')
    return record


def child_environment(env: dict) -> dict:
    """Keep useful shell settings, removing inherited provider and login secrets."""
    return {k: v for k, v in env.items() if not k.endswith(('API_KEY', 'TOKEN'))
            and k not in {'SSH_AUTH_SOCK', 'SSH_AGENT_PID', 'GH_TOKEN', 'GITHUB_TOKEN'}}


def app_server(store: CredentialStore, key: str, codex_bin: str, codex_home: str,
               **ports) -> int:
    """Run the supplied tested Codex on stdio with credentials in child env only."""
    require_enabled()
    run = ports.pop('run', _run_child)
    env = ports.pop('env', None)
    if ports:
        raise TypeError('unexpected runtime port')
    with store.usage(key) as lease_fd:
        record = access_record(store, key)
        child_env = child_environment(dict(os.environ if env is None else env))
        child_env.update(ACCESS_TOKEN=record['access_token'], CODEX_HOME=codex_home)
        config = {'model_provider': '"openai_chatgpt_plan"',
                  'model_providers.openai_chatgpt_plan.name': '"ChatGPT plan"',
                  'model_providers.openai_chatgpt_plan.base_url': '"https://api.openai.com/v1"',
                  'model_providers.openai_chatgpt_plan.env_key': '"ACCESS_TOKEN"',
                  'model_providers.openai_chatgpt_plan.wire_api': '"responses"',
                  'model_providers.openai_chatgpt_plan.requires_openai_auth': 'false',
                  'model_providers.openai_chatgpt_plan.supports_websockets': 'false'}
        argv = [codex_bin, 'app-server', '--listen', 'stdio://']
        for name, value in config.items():
            argv += ['-c', f'{name}={value}']
        return run(argv, env=child_env, check=False, pass_fds=(lease_fd,)).returncode


def transfer(store: CredentialStore, key: str, destination: str,
             *, run=subprocess.run) -> dict:
    """Move a selected session over SSH and hand later refresh to the VM."""
    require_enabled()
    if not re.fullmatch(r'[a-zA-Z0-9][a-zA-Z0-9_.@-]{0,252}', destination):
        raise CredentialError('ssh_destination_invalid')
    # Fixed remote shell text contains no user-controlled arguments or credentials.
    prefix = ['ssh', '-o', 'BatchMode=yes', '--', destination]
    with store.usage(key, exclusive=True), store.lock(key):
        prepare = run(prefix + ['PDD_CHATGPT_SIGN_IN=1 python3 -m pdd.chatgpt_sign_in host-id'],
                      capture_output=True, timeout=30, check=False)
        if prepare.returncode:
            raise CredentialError('ssh_host_prepare_failed')
        record = store.read(key)
        if record.get('transfer_state'):
            raise CredentialError('credential_transferred')
        record['transfer_state'] = 'pending'
        store.write(record)
        try:
            imported = run(prefix + ['PDD_CHATGPT_SIGN_IN=1 python3 -m pdd.chatgpt_sign_in import'],
                           input=json.dumps(record).encode(), capture_output=True,
                           timeout=30, check=False)
            reply = json.loads(imported.stdout)
            if imported.returncode or reply.get('accountKey') != key:
                raise CredentialError('ssh_transfer_uncertain')
        except (OSError, ValueError, subprocess.TimeoutExpired) as exc:
            raise CredentialError('ssh_transfer_uncertain') from exc
        record['transfer_state'] = 'complete'
        for field in ('access_token', 'refresh_token', 'id_token'):
            record.pop(field, None)
        store.write(record)
        return store.summary(key)
