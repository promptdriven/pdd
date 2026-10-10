"""Protected machine-local SIWC records. Source: chatgpt_credentials_python.prompt."""
from __future__ import annotations

from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import tempfile
import uuid
import unicodedata


class CredentialError(Exception):
    """An error safe to return to an owner or Coordinator."""
    def __init__(self, code: str):
        super().__init__(code)
        self.code = code


def timestamp() -> str:
    """Return an ISO UTC timestamp."""
    return datetime.now(timezone.utc).isoformat()


def label_of(value: str) -> str:
    """Bound and remove control and format characters from a display label."""
    return ''.join(c for c in str(value)
                   if not unicodedata.category(c).startswith('C'))[:80]


class CredentialStore:
    """One private host identity and one record per verified registration."""
    def __init__(self, root: Path | None = None):
        self.root = Path(root) if root is not None else Path.home() / '.pdd' / 'chatgpt'
        self.root.mkdir(mode=0o700, parents=True, exist_ok=True)
        self._check(self.root, directory=True)

    @staticmethod
    def _check(path: Path, directory: bool = False) -> None:
        info = path.lstat()
        expected = stat.S_ISDIR(info.st_mode) if directory else stat.S_ISREG(info.st_mode)
        if not expected or info.st_uid != os.getuid() or info.st_mode & 0o077:
            raise CredentialError('credential_storage_unsafe')

    def _read(self, name: str) -> dict:
        path = self.root / name
        try:
            self._check(path)
            fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
            with os.fdopen(fd) as stream:
                return json.load(stream)
        except FileNotFoundError as exc:
            raise CredentialError('credential_missing') from exc
        except (OSError, ValueError) as exc:
            raise CredentialError('credential_storage_failed') from exc

    def _write(self, name: str, value: dict) -> None:
        target = self.root / name
        if target.exists() or target.is_symlink():
            self._check(target)
        fd, temporary = tempfile.mkstemp(dir=self.root, prefix='.pending-')
        try:
            with os.fdopen(fd, 'w') as stream:
                json.dump(value, stream)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, target)
            directory = os.open(self.root, os.O_RDONLY)
            try:
                os.fsync(directory)
            finally:
                os.close(directory)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)

    @staticmethod
    def key(record: dict) -> str:
        """Derive an opaque registration key, keeping workspaces separate."""
        identity = [record.get('issuer'), record.get('subject'), record.get('client_id')]
        if (identity[0] != 'https://auth.openai.com' or
                not all(isinstance(x, str) and x for x in identity) or
                identity[2] == 'dynamic_agent_client'):
            raise CredentialError('credential_identity_invalid')
        return hashlib.sha256(json.dumps(identity).encode()).hexdigest()

    @staticmethod
    def _name(key: str) -> str:
        if not isinstance(key, str) or not re.fullmatch('[a-f0-9]{64}', key):
            raise CredentialError('account_key_invalid')
        return key + '.json'

    @contextmanager
    def lock(self, key: str = 'host', blocking: bool = True):
        """Serialize operations across processes; locks survive no process exit."""
        name = 'host.lock' if key == 'host' else self._name(key) + '.lock'
        fd = os.open(self.root / name, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
        try:
            self._check(self.root / name)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | (0 if blocking else fcntl.LOCK_NB))
            except BlockingIOError as exc:
                raise CredentialError('credential_busy') from exc
            yield fd
        finally:
            os.close(fd)

    def host_id(self) -> str:
        """Create once per machine, independent of imported registrations."""
        with self.lock():
            try:
                value = self._read('host.json')['ext_agent_host_id']
                if not re.fullmatch(r'urn:uuid:[a-f0-9-]{36}', value):
                    raise CredentialError('host_id_invalid')
                uuid.UUID(value[9:])
                return value
            except CredentialError as exc:
                if exc.code != 'credential_missing':
                    raise
            value = 'urn:uuid:' + str(uuid.uuid4())
            self._write('host.json', {'ext_agent_host_id': value})
            return value

    @contextmanager
    def usage(self, key: str, exclusive: bool = False):
        """Shared runtime lease, exclusive import/transfer lease; crash released."""
        name = self._name(key) + '.use.lock'
        fd = os.open(self.root / name, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
        try:
            self._check(self.root / name)
            try:
                fcntl.flock(fd, (fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH) | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise CredentialError('credential_busy') from exc
            yield fd
        finally:
            os.close(fd)

    def read(self, key: str) -> dict:
        """Read a local record; never project this to remote status."""
        value = self._read(self._name(key))
        if self.key(value) != key:
            raise CredentialError('credential_identity_invalid')
        return value

    def write(self, record: dict) -> str:
        """Atomically save a record; caller holds the registration lock."""
        key = self.key(record)
        self._write(self._name(key), record)
        return key

    def import_record(self, record: dict) -> str:
        """Import a selected session, preserving this machine's host identity."""
        key = self.key(record)
        if (record.get('token_type', '').lower() != 'bearer' or
                not all(isinstance(record.get(x), str) and record[x]
                        for x in ('access_token', 'refresh_token', 'id_token')) or
                not isinstance(record.get('expires_at'), (int, float)) or
                not isinstance(record.get('scopes'), list) or
                not all(isinstance(s, str) for s in record['scopes'])):
            raise CredentialError('credential_import_invalid')
        host = self.host_id()
        with self.usage(key, exclusive=True), self.lock(key):
            saved = dict(record, ext_agent_host_id=host, refresh_owner=host,
                         transfer_state=None)
            self.write(saved)
        return key

    def summary(self, key: str) -> dict:
        """Return safe account state without tokens or paths."""
        record = self.read(key)
        state = ('connected' if 'chatgpt.tokens.use.direct' in record.get('scopes', [])
                 else 'plan_disabled')
        if record.get('transfer_state'):
            state = 'transferred'
        elif not record.get('access_token'):
            state = 'sign_in_required'
        return {'method': 'chatgpt', 'state': state, 'accountKey': key,
                'label': label_of(record.get('email') or 'ChatGPT account')[:71] + ' ' + key[:8],
                'errorCode': None, 'updatedAt': record.get('saved_at', timestamp())}
