// Layer-0 safe text sanitization, secret-path checks, and bounded file reads.
import * as nativeFs from 'node:fs';
import { basename } from 'node:path';

const SERVER_PATH = /(?<![\w.:/-])\/(?:home|Users|srv|var|tmp|private|opt|mnt|workspace|usr|etc)\/[^\s"'<>)\]]*/g;
const TOKENS = /\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,})\b|Bearer\s+\S+/g;
const SECRET_NAME = /^(?:\.env.*|auth\.json|credentials\.json|id_rsa|id_ed25519|id_ecdsa|id_dsa|\.npmrc|\.netrc|\.git-credentials|\.pypirc|.+\.(?:pem|key|p12|pfx|keystore|tfstate|tfvars))$/;
const SECRET_PART = new Set(['secrets', '.ssh', '.codex', '.terraform', '.aws']);

/**
 * Strip ANSI control sequences, C0/C1 control characters, explicit secrets, and optionally
 * local/server absolute paths from terminal diagnostic text.
 */
export function cleanText(value, secrets = [], { paths = true } = {}) {
  let text = String(value ?? '')
    .replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '')
    .replace(/[\x00-\x1f\x7f-\x9f]/g, ' ');
  for (const secret of secrets) {
    if (secret) text = text.split(secret).join('[secret]');
  }
  return (paths ? text.replace(SERVER_PATH, '<server path>') : text).trim();
}

/**
 * Extract the first non-empty diagnostic line from tool or server output, stripped of
 * control characters, known secrets, and common token formats (max 300 chars).
 */
export function causeText(value, secrets = []) {
  const line = String(value ?? '')
    .split(/\r?\n/)
    .map(part => cleanText(part, secrets, { paths: false }))
    .find(Boolean) ?? '';
  return line.replace(TOKENS, '[secret]').slice(0, 300);
}

/**
 * Return `true` when `filePath` matches a known credential/secret filename or directory.
 */
export function isSecretPath(filePath) {
  const text = String(filePath ?? '');
  return SECRET_NAME.test(basename(text))
    || text.split('/').some(part => SECRET_PART.has(part))
    || /(?:^|\/)\.docker\/config\.json$/.test(text)
    || /(?:^|\/)(?:\.pdd\/agents\.json|\.config\/pdd\/agents\.json)$/i.test(text);
}

/**
 * Read a regular UTF-8 file up to `maxBytes` using `O_RDONLY | O_NOFOLLOW | O_NONBLOCK`
 * (when `noFollow` is true), refusing symlinks, special files, and oversized files.
 */
export function readBoundedUtf8(
  filePath,
  { maxBytes = 65_536, noFollow = true, fs = nativeFs } = {},
) {
  const f = fs ?? nativeFs;
  if (f.openSync && f.fstatSync && f.readSync && f.closeSync) {
    const flags = (f.constants?.O_RDONLY ?? 0)
      | (noFollow ? (f.constants?.O_NOFOLLOW ?? 0) : 0)
      | (f.constants?.O_NONBLOCK ?? 0);
    let fd;
    try {
      fd = f.openSync(filePath, flags);
      const stat = f.fstatSync(fd);
      if (!stat.isFile()) {
        throw Object.assign(new Error(`${filePath}: expected a regular file.`), { code: 'not_regular_file' });
      }
      if (stat.size > maxBytes) {
        throw Object.assign(new Error(`${filePath}: exceeds ${maxBytes} byte read limit.`), { code: 'file_too_large' });
      }
      const buf = Buffer.alloc(maxBytes + 1);
      let len = 0;
      while (len < buf.length) {
        const n = f.readSync(fd, buf, len, buf.length - len, null);
        if (!n) break;
        len += n;
      }
      if (len > maxBytes) {
        throw Object.assign(new Error(`${filePath}: exceeds ${maxBytes} byte read limit.`), { code: 'file_too_large' });
      }
      return buf.subarray(0, len).toString('utf8');
    } finally {
      if (fd !== undefined) {
        try { f.closeSync(fd); } catch {}
      }
    }
  }
  const raw = f.readFileSync(filePath, 'utf8');
  if (Buffer.byteLength(raw, 'utf8') > maxBytes) {
    throw Object.assign(new Error(`${filePath}: exceeds ${maxBytes} byte read limit.`), { code: 'file_too_large' });
  }
  return raw;
}
