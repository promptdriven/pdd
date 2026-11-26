// Prompt: prompts/cli/live-local-host.prompt.md

import { constants } from 'node:fs';
import { access, lstat, mkdir, open, realpath, rename, unlink } from 'node:fs/promises';
import { delimiter, dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { randomUUID } from 'node:crypto';
import { spawn } from 'node:child_process';
import { createInterface } from 'node:readline';

const CAPTURE_LIMIT = 1024 * 1024;
const OPEN_READ_FLAGS = constants.O_RDONLY | constants.O_NOFOLLOW | (constants.O_NONBLOCK ?? 0);
const SECRET_KEY_RE = /token|secret|password|passwd|credential|authorization|cookie|api[_-]?key|_key$/i;
const fail = () => new Error('Local command host refused an unsafe or unavailable operation.');
const aborted = () => Object.assign(new Error('Local command cancelled.'), { name: 'AbortError' });

// All hosts share the same physical stdin; keep ownership outside the factory.
let confirmationTail = Promise.resolve();
function confirmOnTerminal(label, signal) {
  let cancelled = signal?.aborted === true;
  let abortActive;
  let resolveCancelled;
  const cancellation = new Promise(resolve => { resolveCancelled = resolve; });
  const cancel = () => {
    cancelled = true;
    abortActive?.();
    resolveCancelled({ confirmed: false });
  };
  signal?.addEventListener('abort', cancel, { once: true });
  if (cancelled) cancel();
  const confirmation = confirmationTail.then(() => {
    if (cancelled || !process.stdin.isTTY || !process.stdout.isTTY || process.stdin.destroyed || process.stdin.readableEnded) {
      return { confirmed: false };
    }
    return new Promise(resolveAnswer => {
      let reader;
      let settled = false;
      let prompt;
      let drainRevision = 0;
      const onDrainData = () => { drainRevision++; };
      const releaseReader = () => {
        if (!reader) return;
        const previous = reader;
        reader = null;
        previous.removeListener('close', onError);
        try { previous.close(); }
        finally {
          previous.removeListener('SIGINT', onError);
          previous.removeListener('error', onError);
        }
      };
      const finish = (confirmed = false) => {
        if (settled) return;
        settled = true;
        clearImmediate(prompt);
        try { releaseReader(); } catch { confirmed = false; }
        process.stdin.removeListener('error', onError);
        process.stdin.removeListener('data', onDrainData);
        abortActive = undefined;
        resolveAnswer({ confirmed: confirmed && !cancelled && !signal?.aborted });
      };
      abortActive = () => finish();
      const onError = () => finish();
      const openReader = () => {
        process.stdin.removeListener('error', onError);
        reader = createInterface({ input: process.stdin, output: process.stdout, terminal: true, historySize: 0 });
        reader.once('close', onError);
        reader.once('SIGINT', onError);
        reader.once('error', onError);
        process.stdin.once('error', onError);
      };
      try {
        openReader();
        process.stdin.on('data', onDrainData);
        // Let the resumed TTY pass through an I/O poll before opening a question,
        // discarding any pretyped or partial input before asking.
        prompt = setImmediate(() => {
          let drained = drainRevision;
          const ask = () => {
            if (settled) return;
            if (drainRevision !== drained) {
              drained = drainRevision;
              prompt = setImmediate(ask);
              return;
            }
            try {
              process.stdin.removeListener('data', onDrainData);
              releaseReader();
              openReader();
              reader.question(`Allow this local write? ${label}\nType yes to confirm: `, answer => finish(answer === 'yes'));
            } catch { finish(); }
          };
          prompt = setImmediate(ask);
        });
      } catch { finish(); }
    });
  });
  // Rejection must release the queue as well as normal decline or acceptance.
  confirmationTail = confirmation.then(() => {}, () => {});
  // Keep the queue tied to the real slot, even when a queued caller cancels early.
  return Promise.race([confirmation, cancellation]).finally(() => signal?.removeEventListener('abort', cancel));
}

function parseStrict(text) {
  const parsed = JSON.parse(text);
  let offset = 0;
  const ws = () => { while (/\s/.test(text[offset] ?? '') && offset < text.length) offset++; };
  const string = () => {
    const start = offset++;
    while (offset < text.length) {
      if (text[offset++] === '"') return JSON.parse(text.slice(start, offset));
      if (text[offset - 1] === '\\') offset++;
    }
    throw fail();
  };
  const value = depth => {
    if (depth > 128) throw fail();
    ws();
    if (text[offset] === '"') { string(); return; }
    if (text[offset] === '{') {
      offset++;
      ws();
      const keys = new Set();
      if (text[offset] === '}') { offset++; return; }
      while (true) {
        ws();
        const key = string();
        if (keys.has(key)) throw fail();
        keys.add(key);
        ws();
        offset++;
        value(depth + 1);
        ws();
        if (text[offset++] === '}') return;
      }
    }
    if (text[offset] === '[') {
      offset++;
      ws();
      if (text[offset] === ']') { offset++; return; }
      while (true) {
        value(depth + 1);
        ws();
        if (text[offset++] === ']') return;
      }
    }
    while (offset < text.length && !/[\s,\]}]/.test(text[offset])) offset++;
  };
  value(0);
  return parsed;
}

function freezeManifest(value) {
  if (value && typeof value === 'object') {
    for (const child of Object.values(value)) freezeManifest(child);
    Object.freeze(value);
  }
  return value;
}

const REDACT_BOUNDARY_RE = /[\s=&?:[\]{}'"]/;

function capped(text, limit, redact = null) {
  const chars = [...text];
  let bytes = 0;
  let end = 0;
  for (const char of chars) {
    const size = Buffer.byteLength(char);
    if (bytes + size > limit) break;
    bytes += size;
    end++;
  }
  const truncated = end < chars.length;
  let out = chars.slice(0, end).join('');
  if (truncated && redact) {
    while (end > 0) {
      const reRedacted = redact({ text: out }).text;
      if (reRedacted === out) break;
      const reChars = [...reRedacted];
      let diff = 0;
      while (diff < end && diff < reChars.length && chars[diff] === reChars[diff]) diff++;
      if (diff < end) {
        end = diff;
      } else {
        let prev = end - 1;
        while (prev > 0 && !REDACT_BOUNDARY_RE.test(chars[prev])) prev--;
        end = prev < end ? prev : end - 1;
      }
      out = chars.slice(0, end).join('');
    }
  }
  return { text: out, truncated };
}

async function readBoundedUtf8(file, limit = CAPTURE_LIMIT) {
  const buffer = Buffer.alloc(limit + 1);
  let size = 0;
  while (size < buffer.length) {
    const read = await file.read(buffer, size, buffer.length - size, null);
    if (!read.bytesRead) break;
    size += read.bytesRead;
  }
  if (size > limit) throw fail();
  return new TextDecoder('utf-8', { fatal: true }).decode(buffer.subarray(0, size));
}

async function resolveTargetPath(path) {
  let current = resolve(path);
  const tail = [];
  while (true) {
    try { return resolve(await realpath(current), ...tail.reverse()); }
    catch (error) {
      if (error.code !== 'ENOENT') throw error;
      const parent = dirname(current);
      if (parent === current) return resolve(path);
      tail.push(current.slice(parent.length).replace(/^[/\\]+/, ''));
      current = parent;
    }
  }
}

async function noSymlinkAncestors(path, anchor) {
  const stop = resolve(anchor);
  let current = resolve(path);
  let insideAnchor = true;
  while (true) {
    try {
      const stat = await lstat(current);
      const osRootLink = !insideAnchor && stat.uid === 0 && (process.getuid?.() !== 0 || ['/var', '/tmp'].includes(current));
      if (stat.isSymbolicLink() && !osRootLink) throw fail();
    } catch (error) {
      if (error.code !== 'ENOENT') throw error;
    }
    if (current === stop) insideAnchor = false;
    const parent = dirname(current);
    if (parent === current) return;
    current = parent;
  }
}

function privateStat(stat, directory = false) {
  if (
    (directory ? !stat.isDirectory() : !stat.isFile())
    || stat.isSymbolicLink()
    || (stat.mode & 0o077) !== 0
    || stat.uid !== process.getuid?.()
  ) {
    throw fail();
  }
}

export function createLiveLocalHost({ env = process.env, redaction, root = process.cwd() } = {}) {
  let sourceRoot = root;
  const manifestSnapshots = new Map();
  const sameFile = (a, b) => a.dev === b.dev && a.ino === b.ino;
  const unchangedFile = (a, b) => sameFile(a, b) && a.size === b.size && a.mtimeMs === b.mtimeMs && a.ctimeMs === b.ctimeMs;
  const redact = ({ text }) => {
    const result = redaction?.redact(text);
    if (typeof result !== 'string') throw fail();
    return { text: result };
  };
  const safeValue = value => {
    const text = JSON.stringify(value);
    if (typeof text !== 'string') throw fail();
    const known = redaction?.known?.();
    if (Array.isArray(known) && known.some(secret => typeof secret === 'string' && secret && text.includes(secret))) {
      throw fail();
    }
    const checkNode = (node, depth) => {
      if (depth > 128) throw fail();
      if (typeof node === 'string') {
        if (redact({ text: node }).text !== node) throw fail();
        return;
      }
      if (!node || typeof node !== 'object') return;
      if (Array.isArray(node)) {
        for (const item of node) checkNode(item, depth + 1);
        return;
      }
      for (const [key, item] of Object.entries(node)) {
        if (redact({ text: key }).text !== key) throw fail();
        if (SECRET_KEY_RE.test(key) && item !== null && item !== undefined && item !== '' && item !== '[redacted]') {
          throw fail();
        }
        checkNode(item, depth + 1);
      }
    };
    checkNode(value, 0);
    return text;
  };
  const journalDirectory = () => {
    const anchor = env.PDD_STATE_DIR || env.HOME || null;
    const base = env.PDD_STATE_DIR || (env.HOME ? join(env.HOME, '.local', 'state', 'pdd') : null);
    if (!anchor || !base || !isAbsolute(anchor) || !isAbsolute(base)) throw fail();
    return { anchor, dir: join(base, 'live-local-journal') };
  };
  const journalPath = async key => {
    if (typeof key !== 'string' || !/^[a-f0-9]{64}$/.test(key)) throw fail();
    const { anchor, dir } = journalDirectory();
    const actualRoot = await realpath(sourceRoot);
    const realDir = await resolveTargetPath(dir);
    const within = relative(actualRoot, realDir);
    if (within === '' || (within !== '..' && !within.startsWith(`..${sep}`) && !isAbsolute(within))) throw fail();
    await noSymlinkAncestors(dir, anchor);
    await mkdir(dir, { recursive: true, mode: 0o700 });
    privateStat(await lstat(dir), true);
    return join(dir, `${key}.json`);
  };
  const terminal = process.stdin.isTTY === true && process.stdout.isTTY === true;
  return {
    terminal,
    async readManifest({ path, root }) {
      let file;
      try {
        const actualRoot = await realpath(root);
        sourceRoot = actualRoot;
        const snapshotKey = resolve(actualRoot, path);
        const actualPath = await realpath(snapshotKey);
        file = await open(actualPath, OPEN_READ_FLAGS);
        const stat = await file.stat();
        if (!stat.isFile() || stat.size > CAPTURE_LIMIT) throw fail();
        const text = await readBoundedUtf8(file, CAPTURE_LIMIT);
        if (!unchangedFile(stat, await file.stat()) || !unchangedFile(stat, await lstat(actualPath))) throw fail();
        const manifest = freezeManifest(parseStrict(text));
        manifestSnapshots.set(snapshotKey, { actualPath, stat });
        return manifest;
      } catch {
        throw Object.assign(new Error('Local command manifest is invalid or unavailable.'), { code: 'live-local-manifest-invalid' });
      } finally {
        await file?.close();
      }
    },
    async manifestInSource({ path, root, files }) {
      const actualRoot = await realpath(root);
      const snapshotKey = resolve(actualRoot, path);
      const snapshot = manifestSnapshots.get(snapshotKey);
      if (!snapshot || !Array.isArray(files)) throw fail();
      const actualPath = await realpath(snapshotKey);
      const current = await lstat(actualPath);
      if (actualPath !== snapshot.actualPath || !unchangedFile(snapshot.stat, current)) throw fail();
      for (const file of files) {
        if (typeof file !== 'string' || isAbsolute(file) || file.includes('\\') || file.includes('\0') || file.split('/').includes('..')) {
          throw fail();
        }
        const selected = await realpath(resolve(actualRoot, file));
        if (selected === snapshot.actualPath || sameFile(await lstat(selected), snapshot.stat)) return true;
      }
      return false;
    },
    async resolveExecutable({ executable }) {
      if (typeof executable !== 'string' || !/^[A-Za-z0-9][A-Za-z0-9_.+-]{0,127}$/.test(executable)) throw fail();
      for (const entry of (env.PATH ?? '').split(delimiter).filter(Boolean)) {
        if (!isAbsolute(entry)) continue;
        try {
          const candidate = await realpath(join(entry, executable));
          if (!(await lstat(candidate)).isFile()) continue;
          await access(candidate, constants.X_OK);
          return candidate;
        } catch { /* Try the next local PATH entry. */ }
      }
      throw fail();
    },
    environment({ names }) {
      if (!Array.isArray(names) || names.some(name => typeof name !== 'string' || !/^[A-Z][A-Z0-9_]{0,127}$/.test(name))) throw fail();
      const values = Object.create(null);
      for (const name of [...new Set([...names, 'HOME', 'USERPROFILE', 'XDG_CONFIG_HOME', 'GH_CONFIG_DIR', 'APPDATA'])]) {
        if (typeof env[name] === 'string') values[name] = env[name];
      }
      redaction?.remember(...names.map(name => values[name]).filter(value => typeof value === 'string'));
      return values;
    },
    async execute({ request, resolvedExecutable, signal, environment, root }) {
      if (process.platform === 'win32' || signal?.aborted) throw signal?.aborted ? aborted() : fail();
      if (
        !request
        || typeof request !== 'object'
        || Array.isArray(request)
        || typeof resolvedExecutable !== 'string'
        || !isAbsolute(resolvedExecutable)
        || !environment
        || typeof environment !== 'object'
        || Array.isArray(environment)
        || !Array.isArray(request.argv)
        || request.argv.length < 1
        || request.argv.length > 128
        || request.argv.some(arg => typeof arg !== 'string' || arg.includes('\0') || Buffer.byteLength(arg) > 8192)
        || request.argv.reduce((sum, arg) => sum + Buffer.byteLength(arg), 0) > 65536
        || typeof request.stdin !== 'string'
        || request.stdin.includes('\0')
        || Buffer.byteLength(request.stdin) > 131072
      ) {
        throw fail();
      }
      const safeEnv = Object.create(null);
      for (const [name, value] of Object.entries(environment)) {
        if (typeof name !== 'string' || !name || name.includes('\0') || name.includes('=') || typeof value !== 'string' || value.includes('\0')) {
          throw fail();
        }
        safeEnv[name] = value;
      }
      if (
        !Number.isInteger(request.timeout_ms)
        || request.timeout_ms < 1
        || request.timeout_ms > 120000
        || ['stdout_limit_bytes', 'stderr_limit_bytes'].some(key => !Number.isInteger(request[key]) || request[key] < 0 || request[key] > 65536)
      ) {
        throw fail();
      }
      if (
        typeof request.cwd !== 'string'
        || !request.cwd
        || Buffer.byteLength(request.cwd) > 4096
        || isAbsolute(request.cwd)
        || request.cwd.includes('\\')
        || request.cwd.includes('\0')
        || request.cwd.split('/').includes('..')
      ) {
        throw fail();
      }
      const actualRoot = await realpath(root);
      const cwd = await realpath(resolve(actualRoot, request.cwd));
      const within = relative(actualRoot, cwd);
      if (within === '..' || within.startsWith(`..${sep}`) || isAbsolute(within)) throw fail();
      if (signal?.aborted) throw aborted();
      return new Promise((fulfill, reject) => {
        let timedOut = false;
        let cancelled = false;
        let overflow = false;
        let exited = false;
        let groupGone = false;
        let spawnError;
        const chunks = { stdout: [], stderr: [] };
        const sizes = { stdout: 0, stderr: 0 };
        const child = spawn(resolvedExecutable, request.argv.slice(1), {
          cwd,
          env: safeEnv,
          shell: false,
          detached: true,
          stdio: ['pipe', 'pipe', 'pipe'],
        });
        const kill = () => {
          if (groupGone || !Number.isInteger(child.pid) || child.pid <= 0) return;
          try { process.kill(-child.pid, 'SIGKILL'); }
          catch (error) {
            if (error.code === 'ESRCH') { groupGone = true; return; }
            if (error.code === 'EPERM' && process.platform === 'darwin' && exited) { groupGone = true; return; }
            spawnError ??= fail();
          }
        };
        const cancel = () => { cancelled = true; kill(); };
        signal?.addEventListener('abort', cancel, { once: true });
        const timeout = setTimeout(() => { timedOut = true; kill(); }, request.timeout_ms);
        for (const stream of ['stdout', 'stderr']) {
          child[stream].on('data', data => {
            sizes[stream] += data.length;
            if (sizes[stream] > CAPTURE_LIMIT) { overflow = true; kill(); return; }
            chunks[stream].push(data);
          });
        }
        child.once('error', () => { spawnError = fail(); });
        // Killing the process group on leader exit also closes inherited descendant pipes.
        child.once('exit', () => { exited = true; kill(); });
        child.stdin.on('error', () => {});
        child.stdin.end(request.stdin);
        child.once('close', code => {
          clearTimeout(timeout);
          signal?.removeEventListener('abort', cancel);
          kill();
          if (cancelled || signal?.aborted) return reject(aborted());
          if (spawnError || overflow || (!timedOut && !Number.isInteger(code))) return reject(fail());
          try {
            const stdout = capped(redact({ text: Buffer.concat(chunks.stdout).toString('utf8') }).text, request.stdout_limit_bytes, redact);
            const stderr = capped(redact({ text: Buffer.concat(chunks.stderr).toString('utf8') }).text, request.stderr_limit_bytes, redact);
            fulfill({
              stdout: stdout.text,
              stderr: stderr.text,
              exit_code: timedOut ? null : code,
              timed_out: timedOut,
              stdout_truncated: stdout.truncated,
              stderr_truncated: stderr.truncated,
            });
          } catch { reject(fail()); }
        });
        if (signal?.aborted) cancel();
      });
    },
    async confirm({ binding_id, executable, argv, signal }) {
      if (signal?.aborted || !terminal || !process.stdin.isTTY || !process.stdout.isTTY) return { confirmed: false };
      const label = redact({ text: JSON.stringify({ binding_id, executable, argv }) }).text
        .replace(/[\x00-\x1f\x7f-\x9f]/g, '')
        .replace(/[\u061c\u200e\u200f\u2028\u2029\u202a-\u202e\u2066-\u2069]/g, char => `\\u${char.charCodeAt(0).toString(16).padStart(4, '0')}`);
      return confirmOnTerminal(label, signal);
    },
    journal: {
      async read(key) {
        const path = await journalPath(key);
        let file;
        try {
          file = await open(path, OPEN_READ_FLAGS);
          const stat = await file.stat();
          privateStat(stat);
          if (stat.size > CAPTURE_LIMIT) throw fail();
          const text = await readBoundedUtf8(file, CAPTURE_LIMIT);
          const value = parseStrict(text);
          safeValue(value);
          return value;
        } catch (error) {
          if (error.code === 'ENOENT') return null;
          throw fail();
        } finally {
          await file?.close();
        }
      },
      async write(key, value) {
        const text = safeValue(value);
        if (Buffer.byteLength(text) > CAPTURE_LIMIT) throw fail();
        const path = await journalPath(key);
        try { privateStat(await lstat(path)); } catch (error) { if (error.code !== 'ENOENT') throw fail(); }
        const temporary = `${path}.${randomUUID()}.tmp`;
        let file;
        try {
          file = await open(temporary, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
          await file.writeFile(text);
          await file.sync();
          await file.close();
          file = null;
          await rename(temporary, path);
          const directory = await open(dirname(path), 'r');
          try { await directory.sync(); } finally { await directory.close(); }
        } finally {
          await file?.close();
          await unlink(temporary).catch(error => { if (error.code !== 'ENOENT') throw error; });
        }
      },
    },
    redact,
    randomUUID,
    sleep(ms, signal) {
      return new Promise((resolveSleep, rejectSleep) => {
        if (signal?.aborted) return rejectSleep(aborted());
        const done = () => { signal?.removeEventListener('abort', cancel); resolveSleep(); };
        const timer = setTimeout(done, ms);
        const cancel = () => { clearTimeout(timer); signal?.removeEventListener('abort', cancel); rejectSleep(aborted()); };
        signal?.addEventListener('abort', cancel, { once: true });
      });
    },
  };
}
