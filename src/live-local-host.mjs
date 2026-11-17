// Generated from prompts/cli/live-local-host.prompt.md (sha256: 029ba1022cfd0a53603645cbb2d193ace42f6f228bde638f4dd3024aa26340c2).
// Owned by prompts/cli/live-local-host.prompt.md.
import { constants } from 'node:fs';
import { access, lstat, mkdir, open, realpath, rename, unlink } from 'node:fs/promises';
import { delimiter, dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { randomUUID } from 'node:crypto';
import { spawn } from 'node:child_process';
import { createInterface } from 'node:readline';

const CAPTURE_LIMIT = 1024 * 1024;
const fail = () => new Error('Local command host refused an unsafe or unavailable operation.');
const aborted = () => Object.assign(new Error('Local command cancelled.'), { name: 'AbortError' });
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
      offset++; ws(); const keys = new Set();
      if (text[offset] === '}') { offset++; return; }
      while (true) {
        ws(); const key = string();
        if (keys.has(key)) throw fail();
        keys.add(key); ws(); offset++; value(depth + 1); ws();
        if (text[offset++] === '}') return;
      }
    }
    if (text[offset] === '[') {
      offset++; ws();
      if (text[offset] === ']') { offset++; return; }
      while (true) { value(depth + 1); ws(); if (text[offset++] === ']') return; }
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
function capped(text, limit) {
  let out = ''; let bytes = 0;
  for (const char of text) {
    const size = Buffer.byteLength(char);
    if (bytes + size > limit) break;
    out += char; bytes += size;
  }
  return { text: out, truncated: Buffer.byteLength(text) > bytes };
}
async function noSymlinkAncestors(path) {
  let current = resolve(path);
  while (true) {
    try { if ((await lstat(current)).isSymbolicLink()) throw fail(); }
    catch (error) { if (error.code !== 'ENOENT') throw error; }
    const parent = dirname(current);
    if (parent === current) return;
    current = parent;
  }
}
function privateStat(stat, directory = false) {
  if ((directory ? !stat.isDirectory() : !stat.isFile()) || stat.isSymbolicLink() || (stat.mode & 0o077) !== 0 || stat.uid !== process.getuid?.()) throw fail();
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
    if (typeof text !== 'string' || redact({ text }).text !== text) throw fail();
    return text;
  };
  const journalDirectory = () => {
    const base = env.PDD_STATE_DIR || (env.HOME ? join(env.HOME, '.local', 'state', 'pdd') : null);
    if (!base || !isAbsolute(base)) throw fail();
    return join(base, 'live-local-journal');
  };
  const journalPath = async key => {
    if (typeof key !== 'string' || !/^[a-f0-9]{64}$/.test(key)) throw fail();
    const dir = journalDirectory();
    const actualRoot = await realpath(sourceRoot);
    const within = relative(actualRoot, resolve(dir));
    if (within === '' || (within !== '..' && !within.startsWith(`..${sep}`) && !isAbsolute(within))) throw fail();
    await noSymlinkAncestors(dir);
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
        const actualPath = await realpath(resolve(root, path));
        file = await open(actualPath, constants.O_RDONLY | constants.O_NOFOLLOW);
        const stat = await file.stat();
        if (!stat.isFile() || stat.size > CAPTURE_LIMIT) throw fail();
        const buffer = Buffer.alloc(CAPTURE_LIMIT + 1);
        let size = 0;
        while (size < buffer.length) {
          const read = await file.read(buffer, size, buffer.length - size, null);
          if (!read.bytesRead) break;
          size += read.bytesRead;
        }
        if (size > CAPTURE_LIMIT) throw fail();
        if (!unchangedFile(stat, await file.stat())) throw fail();
        const manifest = freezeManifest(parseStrict(new TextDecoder('utf-8', { fatal: true }).decode(buffer.subarray(0, size))));
        manifestSnapshots.set(resolve(root, path), { actualPath, stat });
        return manifest;
      } catch { throw Object.assign(new Error('Local command manifest is invalid or unavailable.'), { code: 'live-local-manifest-invalid' }); }
      finally { await file?.close(); }
    },
    async manifestInSource({ path, root, files }) {
      const snapshot = manifestSnapshots.get(resolve(root, path));
      if (!snapshot || !Array.isArray(files)) throw fail();
      const actualPath = await realpath(resolve(root, path));
      const current = await lstat(actualPath);
      if (actualPath !== snapshot.actualPath || !unchangedFile(snapshot.stat, current)) throw fail();
      for (const file of files) {
        if (typeof file !== 'string' || isAbsolute(file) || file.split('/').includes('..')) throw fail();
        const selected = await realpath(resolve(root, file));
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
      if (!isAbsolute(resolvedExecutable) || !Array.isArray(request.argv) || request.argv.length < 1 || request.argv.length > 128 || request.argv.some(arg => typeof arg !== 'string' || arg.includes('\0') || Buffer.byteLength(arg) > 8192) || request.argv.reduce((sum, arg) => sum + Buffer.byteLength(arg), 0) > 65536 || typeof request.stdin !== 'string' || request.stdin.includes('\0') || Buffer.byteLength(request.stdin) > 131072) throw fail();
      if (!Number.isInteger(request.timeout_ms) || request.timeout_ms < 1 || request.timeout_ms > 120000 || ['stdout_limit_bytes', 'stderr_limit_bytes'].some(key => !Number.isInteger(request[key]) || request[key] < 0 || request[key] > 65536)) throw fail();
      if (typeof request.cwd !== 'string' || !request.cwd || Buffer.byteLength(request.cwd) > 4096 || isAbsolute(request.cwd) || request.cwd.includes('\\') || request.cwd.includes('\0') || request.cwd.split('/').includes('..')) throw fail();
      const actualRoot = await realpath(root);
      const cwd = await realpath(resolve(actualRoot, request.cwd));
      const within = relative(actualRoot, cwd);
      if (within === '..' || within.startsWith(`..${sep}`) || isAbsolute(within)) throw fail();
      if (signal?.aborted) throw aborted();
      return new Promise((fulfill, reject) => {
        let timedOut = false; let cancelled = false; let overflow = false; let spawnError;
        const chunks = { stdout: [], stderr: [] }; const sizes = { stdout: 0, stderr: 0 };
        const child = spawn(resolvedExecutable, request.argv.slice(1), { cwd, env: environment, shell: false, detached: true, stdio: ['pipe', 'pipe', 'pipe'] });
        const kill = () => { try { process.kill(-child.pid, 'SIGKILL'); } catch (error) { if (error.code !== 'ESRCH') spawnError ??= fail(); } };
        const cancel = () => { cancelled = true; kill(); };
        signal?.addEventListener('abort', cancel, { once: true });
        const timeout = setTimeout(() => { timedOut = true; kill(); }, request.timeout_ms);
        for (const stream of ['stdout', 'stderr']) child[stream].on('data', data => {
          sizes[stream] += data.length;
          if (sizes[stream] > CAPTURE_LIMIT) { overflow = true; kill(); return; }
          chunks[stream].push(data);
        });
        child.once('error', () => { spawnError = fail(); });
        // Killing the group on leader exit also closes inherited descendant pipes.
        child.once('exit', kill);
        child.stdin.on('error', () => {});
        child.stdin.end(request.stdin);
        child.once('close', code => {
          clearTimeout(timeout); signal?.removeEventListener('abort', cancel); kill();
          if (cancelled || signal?.aborted) return reject(aborted());
          if (spawnError || overflow || (!timedOut && !Number.isInteger(code))) return reject(fail());
          try {
            const stdout = capped(redact({ text: Buffer.concat(chunks.stdout).toString('utf8') }).text, request.stdout_limit_bytes);
            const stderr = capped(redact({ text: Buffer.concat(chunks.stderr).toString('utf8') }).text, request.stderr_limit_bytes);
            fulfill({ stdout: stdout.text, stderr: stderr.text, exit_code: timedOut ? null : code, timed_out: timedOut, stdout_truncated: stdout.truncated, stderr_truncated: stderr.truncated });
          } catch { reject(fail()); }
        });
        if (signal?.aborted) cancel();
      });
    },
    async confirm({ binding_id, executable, argv }) {
      if (!terminal || !process.stdin.isTTY || !process.stdout.isTTY) return { confirmed: false };
      const label = redact({ text: JSON.stringify({ binding_id, executable, argv }) }).text.replace(/[\x00-\x1f\x7f-\x9f]/g, '').replace(/[\u202a-\u202e\u2066-\u2069]/g, char => `\\u${char.charCodeAt(0).toString(16).padStart(4, '0')}`);
      const reader = createInterface({ input: process.stdin, output: process.stdout, terminal: true });
      try {
        return await new Promise(resolveAnswer => {
          reader.once('close', () => resolveAnswer({ confirmed: false }));
          reader.once('SIGINT', () => { reader.close(); });
          reader.question(`Allow this local write? ${label}\nType yes to confirm: `, answer => resolveAnswer({ confirmed: answer === 'yes' }));
        });
      } finally { reader.close(); }
    },
    journal: {
      async read(key) {
        const path = await journalPath(key); let file;
        try {
          file = await open(path, constants.O_RDONLY | constants.O_NOFOLLOW);
          privateStat(await file.stat());
          if ((await file.stat()).size > CAPTURE_LIMIT) throw fail();
          const value = parseStrict(await file.readFile('utf8')); safeValue(value); return value;
        } catch (error) { if (error.code === 'ENOENT') return null; throw fail(); }
        finally { await file?.close(); }
      },
      async write(key, value) {
        const text = safeValue(value); if (Buffer.byteLength(text) > CAPTURE_LIMIT) throw fail();
        const path = await journalPath(key);
        try { privateStat(await lstat(path)); } catch (error) { if (error.code !== 'ENOENT') throw fail(); }
        const temporary = `${path}.${randomUUID()}.tmp`; let file;
        try {
          file = await open(temporary, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
          await file.writeFile(text); await file.sync(); await file.close(); file = null;
          await rename(temporary, path);
          const directory = await open(dirname(path), 'r');
          try { await directory.sync(); } finally { await directory.close(); }
        } finally { await file?.close(); await unlink(temporary).catch(error => { if (error.code !== 'ENOENT') throw error; }); }
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
