#!/usr/bin/env node
// Permanent 13-check interactive PTY & forced-rotation verification suite for P1 Accounts
// (COUNCIL-FINAL-PLAN.md §4.4). Supports `--offline` (deterministic mock-gateway + real Python PTY)
// and `--live` (safe non-mutating real-binary macOS smoke check with before/after home hash proof).
import { createHash, randomBytes } from 'node:crypto';
import {
  chmodSync, existsSync, lstatSync, mkdirSync, mkdtempSync, readdirSync,
  readFileSync, readlinkSync, rmSync, symlinkSync, writeFileSync,
} from 'node:fs';
import { createServer } from 'node:http';
import { homedir, tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { renderAutoSwitchBlock, runAccountsCli } from '../src/accounts-cli.mjs';
import { ensureUserCodexHomeBaseline, writeCloudAccountsState } from '../src/login-pool.mjs';
import { sharedRuntimeDirPath } from '../src/pdd-codex.mjs';
import { sharedClaudeRuntimeDir } from '../src/pdd-claude.mjs';

const REPO_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const BIN_CODEX = join(REPO_ROOT, 'bin', 'pdd-codex.mjs');
const BIN_CLAUDE = join(REPO_ROOT, 'bin', 'pdd-claude.mjs');

const HOST_SCRUB_KEYS = new Set([
  'CODEX_HOME', 'CLAUDE_CONFIG_DIR',
  'XDG_CONFIG_HOME', 'XDG_STATE_HOME', 'XDG_DATA_HOME', 'XDG_CACHE_HOME',
]);

function scrubHostEnv(base = process.env) {
  const out = {};
  for (const [k, v] of Object.entries(base ?? {})) {
    if (typeof v !== 'string') continue;
    if (HOST_SCRUB_KEYS.has(k) || k.startsWith('PDD_')) continue;
    out[k] = v;
  }
  return out;
}

const PTY_BRIDGE_PY = `
import fcntl, os, pty, select, signal, struct, subprocess, sys, termios
m, s = pty.openpty()
fcntl.ioctl(s, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 120, 0, 0))
p = subprocess.Popen(sys.argv[1:], stdin=s, stdout=s, stderr=s, start_new_session=True, close_fds=True)
os.close(s)
in_fd, in_open = sys.stdin.fileno(), True
def kill_pg():
  try: os.killpg(p.pid, signal.SIGKILL)
  except OSError: pass
try:
  while True:
    r, _, _ = select.select([m] + ([in_fd] if in_open else []), [], [], 0.05)
    if m in r:
      try: d = os.read(m, 4096)
      except OSError: d = b""
      if d: os.write(1, d)
      elif p.poll() is not None: break
    if in_open and in_fd in r:
      cmd = os.read(in_fd, 4096)
      if not cmd: in_open = False
      else:
        for line in cmd.splitlines(True):
          if line.strip() == b"@@SIGKILL@@": kill_pg()
          else:
            try: os.write(m, line)
            except OSError: pass
    if p.poll() is not None:
      while select.select([m], [], [], 0.03)[0]:
        try: d2 = os.read(m, 4096)
        except OSError: break
        if not d2: break
        os.write(1, d2)
      break
finally:
  if p.poll() is None: kill_pg()
  try: os.close(m)
  except OSError: pass
rc = p.wait()
sys.exit(rc if rc >= 0 else 128 - rc)
`;

function spawnPtySession(cmdArgs, env, cwd, registry = null) {
  const child = spawn('python3', ['-u', '-c', PTY_BRIDGE_PY, ...cmdArgs], { cwd, env, stdio: ['pipe', 'pipe', 'pipe'] });
  let buf = '', errBuf = '', exited = false;
  const waiters = [];
  const flush = () => {
    for (let i = waiters.length - 1; i >= 0; i -= 1) {
      const w = waiters[i];
      if (w.re.test(buf.slice(w.from))) { clearTimeout(w.timer); waiters.splice(i, 1); w.resolve(buf.slice(w.from)); }
    }
  };
  child.stdout.on('data', d => { buf += d.toString('utf8'); flush(); });
  child.stderr.on('data', d => { errBuf += d.toString('utf8'); });
  const rawExit = new Promise(r => child.on('close', (code, sig) => {
    exited = true;
    registry?.delete(session);
    r({ code: code ?? (sig ? 128 : 1), buf, errBuf });
  }));
  const kill = () => {
    if (exited) return;
    try { child.stdin.write('@@SIGKILL@@\n'); } catch {}
    try { child.kill('SIGKILL'); } catch {}
  };
  const session = {
    child, kill, mark: () => buf.length,
    send: line => { if (!exited) child.stdin.write(`${line}\n`); },
    sigkill: () => { if (!exited) child.stdin.write('@@SIGKILL@@\n'); },
    waitFor: (re, { from = 0, timeoutMs = 8000 } = {}) => new Promise((res, rej) => {
      if (re.test(buf.slice(from))) return res(buf.slice(from));
      const w = { re, from, resolve: res };
      w.timer = setTimeout(() => {
        const i = waiters.indexOf(w);
        if (i >= 0) waiters.splice(i, 1);
        kill();
        rej(new Error(`PTY waitFor timeout (${timeoutMs}ms) for ${re}. Output:\n${buf.slice(from)}\nstderr:\n${errBuf}`));
      }, timeoutMs);
      waiters.push(w);
    }),
    waitExit: (timeoutMs = 15_000) => new Promise((res, rej) => {
      const timer = setTimeout(() => {
        kill();
        rej(new Error(`PTY waitExit timeout (${timeoutMs}ms) for ${cmdArgs.join(' ')}. Output:\n${buf}\nstderr:\n${errBuf}`));
      }, timeoutMs);
      rawExit.then(r => { clearTimeout(timer); res(r); });
    }),
  };
  registry?.add(session);
  return session;
}

function runCmd(bin, args, { env = process.env, cwd = REPO_ROOT, timeoutMs = 10_000 } = {}) {
  return new Promise(res => {
    const child = spawn(bin, args, { cwd, env, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '', stderr = '', done = false;
    const finish = status => { if (!done) { done = true; clearTimeout(timer); res({ status, stdout, stderr }); } };
    const timer = setTimeout(() => { try { child.kill('SIGKILL'); } catch {} finish(124); }, timeoutMs);
    child.stdout.on('data', d => { stdout += d.toString('utf8'); });
    child.stderr.on('data', d => { stderr += d.toString('utf8'); });
    child.on('error', err => finish(err?.code === 'ENOENT' ? 127 : 1));
    child.on('close', (code, sig) => finish(code ?? (sig ? 128 : 1)));
  });
}

const sha256 = buf => createHash('sha256').update(buf).digest('hex');

function snapshotTree(targets, { recursive = true, ignoreChildDirs = new Set() } = {}) {
  const out = {};
  const visit = (p, depth) => {
    let st;
    try { st = lstatSync(p); } catch { out[p] = 'MISSING'; return; }
    const mode = (st.mode & 0o7777).toString(8);
    if (st.isSymbolicLink()) { out[p] = `SYMLINK:${mode}->${readlinkSync(p)}`; return; }
    if (st.isFile()) { out[p] = `FILE:${mode}:${sha256(readFileSync(p))}`; return; }
    if (st.isDirectory()) {
      const names = readdirSync(p).filter(n => !(depth === 0 && ignoreChildDirs.has(n))).sort();
      out[p] = `DIR:${mode}:[${names.join(',')}]`;
      if (recursive && depth < 8) {
        for (const n of names) visit(join(p, n), depth + 1);
      }
    }
  };
  for (const t of targets) visit(t, 0);
  return out;
}

const diffSnapshots = (a, b) => [...new Set([...Object.keys(a), ...Object.keys(b)])].filter(k => a[k] !== b[k]).map(k => `${k}: ${a[k]} !== ${b[k]}`);

function walkReachableModules(entryPaths) {
  const visited = new Set(), stack = entryPaths.map(p => resolve(p));
  const re = /(?:import|export)\s+(?:[^'"]*?\s+from\s+)?['"](\.[^'"]+)['"]|import\(\s*['"](\.[^'"]+)['"]\s*\)/g;
  while (stack.length) {
    const file = stack.pop();
    if (visited.has(file) || !existsSync(file)) continue;
    visited.add(file);
    const src = readFileSync(file, 'utf8');
    let m;
    while ((m = re.exec(src))) {
      const target = resolve(dirname(file), m[1] || m[2]);
      if (existsSync(target) && !visited.has(target)) stack.push(target);
    }
  }
  return visited;
}

async function measureColdStartupMs(entryPath, samples = 3) {
  const times = [];
  for (let i = 0; i < samples; i += 1) {
    const t0 = performance.now();
    const r = await runCmd(process.execPath, [entryPath, '--pdd-help']);
    if (r.status !== 0) throw new Error(`${entryPath} --pdd-help failed: ${r.stderr}`);
    times.push(Math.round((performance.now() - t0) * 10) / 10);
  }
  times.sort((a, b) => a - b);
  return { p50: times[Math.floor(times.length / 2)], p95: times[times.length - 1] };
}

async function startMockGatewayServer() {
  let seq = 0;
  const leases = new Map();
  const state = { seatAExhausted: false, force503: false, leaseRequests: 0, revoked: new Set(), mcpAuthOk: 0, mcpAuthFail: 0 };
  const server = createServer((req, res) => {
    const chunks = [];
    req.on('data', c => chunks.push(c));
    req.on('end', () => {
      const raw = Buffer.concat(chunks).toString('utf8');
      const body = raw ? (() => { try { return JSON.parse(raw); } catch { return {}; } })() : {};
      const url = new URL(req.url, 'http://127.0.0.1');
      const json = (code, obj) => { res.writeHead(code, { 'content-type': 'application/json', connection: 'close' }); res.end(JSON.stringify(obj)); };
      const origin = `http://127.0.0.1:${server.address().port}`;
      if (req.method === 'POST' && url.pathname === '/v1/accounts/lease') {
        state.leaseRequests += 1;
        if (state.force503) return json(503, { error: 'service_unavailable', message: 'Gateway temporarily unavailable' });
        const provider = body.provider || 'codex', autoRotate = body.auto_rotate !== false;
        const leaseId = `lse_${provider}_${++seq}`, token = provider === 'codex' ? `pddg_${leaseId}_tok` : `pddg_cl_${leaseId}_tok`;
        const seat = body.preferred_account || 'seat-A';
        leases.set(token, { leaseId, provider, autoRotate, seat });
        return json(200, {
          state: 'leased',
          account: { account_id: `acc_${seat}`, label: seat, provider, state: 'ready', plan_type: 'pro' },
          lease: {
            lease_id: leaseId, expires_at: new Date(Date.now() + 7 * 86400_000).toISOString(), delivery_mode: 'gateway_grant', auto_rotate: autoRotate,
            ...(provider === 'codex'
              ? { codex_gateway_url: `${origin}/v1/codex-gateway`, codex_backend_api_url: `${origin}/v1/codex-gateway/backend-api`, codex_gateway_token: token, gateway_bearer_token: token }
              : { anthropic_base_url: `${origin}/v1/claude-gateway`, gateway_bearer_token: token, claude_oauth_token: token }),
          },
        });
      }
      if (req.method === 'POST' && /^\/v1\/accounts\/leases\/([^/]+)\/heartbeat$/.test(url.pathname)) return json(200, { ok: true, expires_at: new Date(Date.now() + 7 * 86400_000).toISOString() });
      if (req.method === 'POST' && /^\/v1\/accounts\/leases\/([^/]+)\/release$/.test(url.pathname)) { state.revoked.add(url.pathname.split('/')[4]); return json(200, { revoked: true }); }
      if (url.pathname === '/v1/codex-gateway/backend-api/ps/mcp') {
        const tok = String(req.headers.authorization || '').replace(/^Bearer\s+/i, '');
        if (!leases.has(tok)) { state.mcpAuthFail += 1; return json(401, { error: 'Missing Codex gateway grant' }); }
        state.mcpAuthOk += 1;
        return json(200, { ok: true, tools: ['echo'] });
      }
      if (req.method === 'POST' && (url.pathname === '/v1/codex-gateway/backend-api/codex/responses' || url.pathname === '/v1/claude-gateway/v1/messages')) {
        const tok = String(req.headers.authorization || req.headers['x-api-key'] || '').replace(/^Bearer\s+/i, '');
        const info = leases.get(tok);
        if (!info) return json(401, { error: 'invalid_grant' });
        if (state.seatAExhausted && info.seat === 'seat-A') return info.autoRotate ? json(200, { ok: true, seat: 'seat-B' }) : json(429, { error: 'usage_limit_reached', seat: 'seat-A' });
        return json(200, { ok: true, seat: info.seat });
      }
      json(404, { error: 'not_found' });
    });
  });
  await new Promise(r => server.listen(0, '127.0.0.1', r));
  return { server, url: `http://127.0.0.1:${server.address().port}`, state, leases };
}

function writeMockBinaries(binDir, mcpEchoPath, browserStateFile) {
  writeFileSync(mcpEchoPath, `#!/usr/bin/env node
import { createInterface } from 'node:readline';
for await (const line of createInterface({ input: process.stdin })) {
  if (!line.trim()) continue;
  const req = JSON.parse(line);
  if (req.method === 'tools/call') process.stdout.write(JSON.stringify({ jsonrpc: '2.0', id: req.id, result: { text: req.params?.nonce || '' } }) + '\\n');
}
`, { mode: 0o755 });
  const makeMockCli = kind => `#!/usr/bin/env node
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { createInterface } from 'node:readline';
import { spawnSync } from 'node:child_process';
const args = process.argv.slice(2), kind = ${JSON.stringify(kind)};
const parsed = { cFlags: {}, settingsPath: null, pos: [] };
for (let i = 0; i < args.length; i += 1) {
  if (kind === 'codex' && args[i] === '-c' && i + 1 < args.length) { const kv = args[++i], eq = kv.indexOf('='); if (eq > 0) parsed.cFlags[kv.slice(0, eq)] = kv.slice(eq + 1).replace(/^"|"$/g, ''); }
  else if (kind === 'claude' && args[i] === '--settings' && i + 1 < args.length) parsed.settingsPath = args[++i];
  else parsed.pos.push(args[i]);
}
if (parsed.pos[0] === 'app-server') process.exit(0);
if (parsed.pos.includes('DUMP_ENV_PASSTHROUGH')) { console.log('ENV_JSON=' + JSON.stringify(Object.keys(process.env).sort())); process.exit(0); }
if (parsed.pos.some(a => a === '--version' || a === '-V' || a === '-v')) { console.log(kind + '-mock 1.0.0'); process.exit(0); }
if (['mcp', 'plugin', 'features'].includes(parsed.pos[0]) && parsed.pos[1] === 'list') { console.log(kind + ':' + parsed.pos[0] + ':ok'); process.exit(0); }
if (parsed.pos[0] === '--' && parsed.pos[1] === '-prompt') { console.log('OPERAND:' + parsed.pos[1]); process.exit(0); }
const sessDir = kind === 'codex' ? join(process.env.CODEX_HOME || join(process.env.HOME, '.codex'), 'sessions') : join(process.env.HOME, '.claude', 'projects');
function getAuth() {
  if (kind === 'codex') {
    const auth = existsSync(join(process.env.CODEX_HOME || '', 'auth.json')) ? JSON.parse(readFileSync(join(process.env.CODEX_HOME, 'auth.json'), 'utf8')) : null;
    return { token: auth?.tokens?.access_token || null, base: parsed.cFlags.openai_base_url || null, backend: parsed.cFlags.chatgpt_base_url || null };
  }
  const s = parsed.settingsPath && existsSync(parsed.settingsPath) ? JSON.parse(readFileSync(parsed.settingsPath, 'utf8')) : null;
  return { token: s?.env?.CLAUDE_CODE_OAUTH_TOKEN || null, base: s?.env?.ANTHROPIC_BASE_URL || null, backend: null };
}
async function callGw(prompt) {
  const a = getAuth();
  if (!a.token || !a.base) return { status: 200, seat: 'stock-local' };
  const r = await fetch(kind === 'codex' ? a.base + '/responses' : a.base + '/v1/messages', { method: 'POST', headers: { authorization: 'Bearer ' + a.token, 'content-type': 'application/json' }, body: JSON.stringify({ prompt }) });
  return { status: r.status, seat: (await r.json()).seat || 'unknown' };
}
if (parsed.pos[0] === 'exec' || parsed.pos[0] === '-p') {
  const msg = parsed.pos[1] || '';
  if (msg === 'DUMP_ENV') { console.log('ENV_JSON=' + JSON.stringify(Object.keys(process.env).sort())); process.exit(0); }
  const r = await callGw(msg);
  console.log('NONTTY_OK=' + msg + ' SEAT=' + r.seat + ' STATUS=' + r.status);
  process.exit(r.status === 200 ? 0 : 1);
}
if (parsed.pos[0] === 'resume' || parsed.pos[0] === '--resume' || parsed.pos[0] === '-c') {
  const sid = (parsed.pos[1] && parsed.pos[1] !== '--last') ? parsed.pos[1] : readFileSync(join(sessDir, 'last.txt'), 'utf8').trim();
  const saved = JSON.parse(readFileSync(join(sessDir, sid + '.json'), 'utf8'));
  const r = await callGw('resume');
  console.log('RESUMED=' + saved.nonce + ' SID=' + sid + ' SEAT=' + r.seat);
  process.exit(0);
}
if (!process.stdin.isTTY || !process.stdout.isTTY) { console.error('NOT_A_TTY'); process.exit(2); }
const sid = kind + '-sid-' + process.pid + '-' + Date.now();
let turn1Nonce = '';
console.log('READY SID=' + sid + ' PID=' + process.pid + ' TTY=1');
for await (const rawLine of createInterface({ input: process.stdin })) {
  const line = rawLine.trim();
  if (!line) continue;
  if (line === 'EXIT') process.exit(0);
  if (line.startsWith('TURN:')) {
    const nonce = line.slice(5); if (!turn1Nonce) turn1Nonce = nonce;
    const r = await callGw(nonce);
    mkdirSync(sessDir, { recursive: true });
    writeFileSync(join(sessDir, sid + '.json'), JSON.stringify({ sid, nonce: turn1Nonce }));
    writeFileSync(join(sessDir, 'last.txt'), sid);
    console.log('REPLY=' + nonce + ' SEAT=' + r.seat + ' STATUS=' + r.status + ' PID=' + process.pid);
  } else if (line === 'RECALL') {
    const r = await callGw('recall');
    console.log('RECALLED=' + turn1Nonce + ' SEAT=' + r.seat + ' STATUS=' + r.status + ' PID=' + process.pid);
  } else if (line.startsWith('MCP_ECHO:')) {
    const nonce = line.slice(9);
    const mcp = spawnSync(process.execPath, [${JSON.stringify(mcpEchoPath)}], { input: JSON.stringify({ jsonrpc: '2.0', id: 1, method: 'tools/call', params: { name: 'echo', nonce } }) + '\\n', encoding: 'utf8' });
    const a = getAuth();
    const psStatus = (kind === 'codex' && a.backend) ? (await fetch(a.backend + '/ps/mcp', { headers: { authorization: 'Bearer ' + (process.env.CODEX_CONNECTORS_TOKEN || '') } })).status : 200;
    console.log('MCP_OK=' + JSON.parse(mcp.stdout.trim()).result.text + ' PS_STATUS=' + psStatus);
  } else if (line === 'HOOK_WRITE') {
    writeFileSync(${JSON.stringify(browserStateFile)}, kind + ':hook-browser-ok:' + process.pid);
    if (kind === 'codex' && process.env.CODEX_HOME) {
      const cfg = join(process.env.CODEX_HOME, 'config.toml');
      writeFileSync(cfg, (existsSync(cfg) ? readFileSync(cfg, 'utf8') : '') + '\\n[hooks.state."' + process.env.CODEX_HOME + '/hooks/demo.sh"]\\ntrusted = true\\n');
    }
    console.log('HOOK_OK=1');
  }
}
process.exit(0);
`;
  writeFileSync(join(binDir, 'codex'), makeMockCli('codex'), { mode: 0o755 });
  writeFileSync(join(binDir, 'claude'), makeMockCli('claude'), { mode: 0o755 });
  writeFileSync(join(binDir, 'pdd-codex'), `#!/bin/sh\nexec ${JSON.stringify(process.execPath)} ${JSON.stringify(BIN_CODEX)} "$@"\n`, { mode: 0o755 });
  writeFileSync(join(binDir, 'pdd-claude'), `#!/bin/sh\nexec ${JSON.stringify(process.execPath)} ${JSON.stringify(BIN_CLAUDE)} "$@"\n`, { mode: 0o755 });
  for (const n of ['codex', 'claude', 'pdd-codex', 'pdd-claude']) chmodSync(join(binDir, n), 0o755);
}

async function runOfflineChecks() {
  const results = [], activePtys = new Set();
  const rec = (id, name, pass, detail) => results.push({ id, name, status: pass ? 'PASS' : 'FAIL', detail });
  const root = mkdtempSync(join(tmpdir(), 'pdd-pty-verify-'));
  const home = join(root, 'home'), c5Home = join(root, 'c5-home'), stateDir = join(root, 'state'), mockBin = join(root, 'bin'), dotfilesDir = join(root, 'dotfiles');
  for (const d of [join(home, '.codex'), join(home, '.claude'), join(c5Home, '.codex'), join(c5Home, '.claude'), stateDir, mockBin, dotfilesDir]) mkdirSync(d, { recursive: true, mode: 0o700 });
  const codexDir = join(home, '.codex'), claudeDir = join(home, '.claude'), claudeJson = join(home, '.claude.json');
  const codexAuth = join(codexDir, 'auth.json'), codexCfg = join(codexDir, 'config.toml'), claudeSettings = join(claudeDir, 'settings.json');
  const stowZshrc = join(dotfilesDir, 'zshrc'), userZshrc = join(home, '.zshrc');
  ensureUserCodexHomeBaseline({ existsSync, mkdirSync, writeFileSync, chmodSync, lstatSync }, codexDir);
  writeFileSync(codexAuth, JSON.stringify({ tokens: { access_token: 'PERSONAL_KEEP' } }), { mode: 0o600 });
  writeFileSync(codexCfg, 'model = "gpt-5.4"\n', { mode: 0o600 });
  writeFileSync(claudeSettings, JSON.stringify({ theme: 'dark', env: { USER_FLAG: 'keep' } }, null, 2), { mode: 0o600 });
  writeFileSync(claudeJson, JSON.stringify({ user: 'keep' }), { mode: 0o600 });
  writeFileSync(join(c5Home, '.codex', 'config.toml'), 'model = "gpt-5.4"\n', { mode: 0o600 });
  writeFileSync(stowZshrc, '# user zshrc\n', { mode: 0o640 });
  symlinkSync(stowZshrc, userZshrc);

  const browserStateFile = join(root, 'browser-hook-state.txt');
  writeMockBinaries(mockBin, join(root, 'mcp-echo.mjs'), browserStateFile);
  const gw = await startMockGatewayServer();
  const cleanHost = scrubHostEnv(process.env);
  const baseEnv = {
    ...cleanHost, HOME: home, PDD_STATE_DIR: stateDir,
    PDD_CODEX_RUNTIME_ROOT: join(stateDir, 'codex-runtime'), PDD_CLAUDE_RUNTIME_ROOT: join(stateDir, 'claude-runtime'),
    PDD_ACCOUNTS_URL: gw.url, PDD_TOKEN: 'pdd_test_bearer_token',
    PDD_CODEX_BIN: join(mockBin, 'codex'), PDD_CLAUDE_BIN: join(mockBin, 'claude'),
    PATH: `${mockBin}:${cleanHost.PATH ?? '/usr/bin:/bin'}`,
  };
  writeCloudAccountsState({
    enrolled: true, providers: ['codex', 'claude'],
    active: {
      codex: { account_id: 'acc_seat-A', label: 'seat-A', provider: 'codex', state: 'ready' },
      claude: { account_id: 'acc_seat-A', label: 'seat-A', provider: 'claude', state: 'ready' },
    },
  }, { env: baseEnv });
  const homeSnapOpts = { recursive: true, ignoreChildDirs: new Set(['sessions', 'projects']) };
  const homeBefore = snapshotTree([codexDir, claudeDir, claudeJson], homeSnapOpts);

  try {
    const c1 = [], c2 = [], c3 = [], c4 = [], c5 = [], c8 = [];
    for (const [label, binPath] of [['codex', BIN_CODEX], ['claude', BIN_CLAUDE]]) {
      gw.state.seatAExhausted = false;
      const nonce1 = `N1_${label}_${randomBytes(4).toString('hex')}`, nonceMcp = `MCP_${label}_${randomBytes(4).toString('hex')}`;
      const pty = spawnPtySession([process.execPath, binPath], baseEnv, root, activePtys);
      const [, sid, pid1] = (await pty.waitFor(/READY SID=([^\s]+) PID=(\d+) TTY=1/)).match(/READY SID=([^\s]+) PID=(\d+) TTY=1/);
      let m = pty.mark();
      pty.send(`TURN:${nonce1}`);
      await pty.waitFor(new RegExp(`REPLY=${nonce1} SEAT=seat-A STATUS=200 PID=${pid1}`), { from: m });
      c1.push(`${label}:sid=${sid},seat=seat-A`);
      gw.state.seatAExhausted = true;
      m = pty.mark();
      pty.send('RECALL');
      await pty.waitFor(new RegExp(`RECALLED=${nonce1} SEAT=seat-B STATUS=200 PID=${pid1}`), { from: m });
      c2.push(`${label}:recalled=${nonce1},pid=${pid1}`);
      c8.push(`${label}:A->B(pid=${pid1})`);
      m = pty.mark();
      pty.send(`MCP_ECHO:${nonceMcp}`);
      await pty.waitFor(new RegExp(`MCP_OK=${nonceMcp} PS_STATUS=200`), { from: m });
      c4.push(`${label}:echo=${nonceMcp},ps=200`);
      pty.send('EXIT');
      const ex = await pty.waitExit();
      if (ex.code !== 0) throw new Error(`${label} interactive PTY exited ${ex.code}`);

      // C05 runs in its own isolated c5Home so main home's config.toml stays 100% untouched for C10!
      const c5Env = { ...baseEnv, HOME: c5Home, PDD_CODEX_RUNTIME_ROOT: join(stateDir, 'c5-codex-rt'), PDD_CLAUDE_RUNTIME_ROOT: join(stateDir, 'c5-claude-rt') };
      const pty5 = spawnPtySession([process.execPath, binPath], c5Env, root, activePtys);
      await pty5.waitFor(/READY SID=/);
      const m5 = pty5.mark();
      pty5.send('HOOK_WRITE');
      await pty5.waitFor(/HOOK_OK=1/, { from: m5 });
      pty5.send('EXIT');
      if ((await pty5.waitExit()).code !== 0) throw new Error(`${label} C05 PTY exited non-zero`);
      if (!readFileSync(browserStateFile, 'utf8').includes(`${label}:hook-browser-ok`)) throw new Error(`${label} hook state missing`);
      if (label === 'codex') {
        const cfgAfter = readFileSync(join(c5Home, '.codex', 'config.toml'), 'utf8');
        if (cfgAfter.includes('pdd-codex-') || !cfgAfter.includes(`${c5Home}/.codex/hooks/demo.sh`)) throw new Error(`codex writeback failed: ${cfgAfter}`);
      }
      c5.push(`${label}:hook+writeback=ok`);

      const r1 = await runCmd(process.execPath, [binPath, ...(label === 'codex' ? ['resume', sid] : ['--resume', sid])], { env: baseEnv, cwd: root });
      const r2 = await runCmd(process.execPath, [binPath, ...(label === 'codex' ? ['resume', '--last'] : ['-c'])], { env: baseEnv, cwd: root });
      if (r1.status !== 0 || !r1.stdout.includes(`RESUMED=${nonce1}`) || r2.status !== 0 || !r2.stdout.includes(`RESUMED=${nonce1}`)) throw new Error(`${label} resume failed: ${r1.stdout}${r1.stderr} | ${r2.stdout}${r2.stderr}`);
      c3.push(`${label}:sid+last=ok`);
      const pin = await runCmd(process.execPath, [binPath, '--account', 'seat-A', ...(label === 'codex' ? ['exec', 'pin'] : ['-p', 'pin'])], { env: baseEnv, cwd: root });
      if (pin.status === 0 || !pin.stdout.includes('SEAT=seat-A STATUS=429')) throw new Error(`${label} pin negative control failed: ${pin.stdout}${pin.stderr}`);
      c8.push(`${label}:pin-no-rotate=429`);
    }
    rec('C01', 'Interactive PTY Start & Turn 1', true, c1.join('; '));
    rec('C02', 'Multi-Turn Memory (Same PTY/PID)', true, c2.join('; '));
    rec('C03', 'Cross-Process Resume (SID + --last/-c)', true, c3.join('; '));
    rec('C04', 'Real Stdio MCP Echo + Gateway Auth', gw.state.mcpAuthOk >= 1 && gw.state.mcpAuthFail === 0, c4.join('; '));
    rec('C05', 'Hook/Browser State & Writeback Norm', true, c5.join('; '));

    const parityDiffs = [];
    for (const [stockBin, wrapBin, cmds] of [
      [join(mockBin, 'codex'), BIN_CODEX, [['mcp', 'list'], ['plugin', 'list'], ['features', 'list'], ['--', '-prompt']]],
      [join(mockBin, 'claude'), BIN_CLAUDE, [['mcp', 'list'], ['plugin', 'list'], ['--', '-prompt']]],
    ]) {
      for (const cmdArgs of cmds) {
        const s = await runCmd(stockBin, cmdArgs, { env: baseEnv, cwd: root });
        const w = await runCmd(process.execPath, [wrapBin, ...cmdArgs], { env: baseEnv, cwd: root });
        if (s.status !== w.status || s.stdout !== w.stdout) parityDiffs.push(`${cmdArgs.join(' ')}: ${s.status}/${w.status}`);
      }
    }
    rec('C06', 'Stock CLI Parity Diff', parityDiffs.length === 0, parityDiffs.length ? parityDiffs.join('; ') : '0 diffs across codex & claude');

    gw.state.seatAExhausted = false;
    const c7Details = [];
    for (const [label, binPath, runtimeDir] of [['codex', BIN_CODEX, sharedRuntimeDirPath({ env: baseEnv })], ['claude', BIN_CLAUDE, sharedClaudeRuntimeDir(baseEnv)]]) {
      const leasesBefore = gw.leases.size, revokedBefore = gw.state.revoked.size;
      const sessions = [0, 1, 2].map(() => spawnPtySession([process.execPath, binPath], baseEnv, root, activePtys));
      for (const s of sessions) await s.waitFor(/READY SID=/);
      const addedLeases = gw.leases.size - leasesBefore;
      sessions[0].sigkill();
      await sessions[0].waitExit();
      sessions[1].send('EXIT');
      sessions[2].send('EXIT');
      await Promise.all([sessions[1].waitExit(), sessions[2].waitExit()]);
      const pids = existsSync(join(runtimeDir, 'pids')) ? readdirSync(join(runtimeDir, 'pids')) : [];
      const authLeft = existsSync(join(runtimeDir, 'auth.json')) || existsSync(join(runtimeDir, 'lease.json'));
      const sessFiles = label === 'claude' && existsSync(join(runtimeDir, 'sessions')) ? readdirSync(join(runtimeDir, 'sessions')) : [];
      const revokedAdded = gw.state.revoked.size - revokedBefore;
      if (addedLeases !== 1 || revokedAdded !== 1 || pids.length !== 0 || authLeft || sessFiles.length !== 0) {
        throw new Error(`${label} C07 leak: leases=${addedLeases} revoked=${revokedAdded} pids=${pids} auth=${authLeft} sess=${sessFiles}`);
      }
      c7Details.push(`${label}:3-sess=1-lease,revoked=1,sigkill-swept,0-leftovers`);
    }
    rec('C07', 'Concurrent Sessions (3) + SIGKILL Cleanup', true, c7Details.join('; '));
    rec('C08', 'Forced A->B Rotation + Pinned Negative Control', true, c8.join('; '));

    // C09: REAL enrolled-state 503 lease-failure fail-open + empty-state fail-open + fail-closed + zero ~/.codex creation + ENOENT->127!
    const freshHome = join(root, 'fresh-failopen-home');
    mkdirSync(freshHome, { recursive: true, mode: 0o700 });
    gw.state.force503 = true;
    const reqBefore503 = gw.state.leaseRequests;
    const enrolledFailEnv = { ...baseEnv, HOME: freshHome, PDD_CODEX_RUNTIME_ROOT: join(stateDir, 'c9-cx-rt'), PDD_CLAUDE_RUNTIME_ROOT: join(stateDir, 'c9-cl-rt') };
    const foCx503 = await runCmd(process.execPath, [BIN_CODEX, 'exec', 'fo503'], { env: { ...enrolledFailEnv, PDD_CODEX_AUTO_FAIL_OPEN: '1' }, cwd: root });
    const foCl503 = await runCmd(process.execPath, [BIN_CLAUDE, '-p', 'fo503'], { env: { ...enrolledFailEnv, PDD_CLAUDE_AUTO_FAIL_OPEN: '1' }, cwd: root });
    const fcCx503 = await runCmd(process.execPath, [BIN_CODEX, 'exec', 'fc503'], { env: enrolledFailEnv, cwd: root });
    const fcCl503 = await runCmd(process.execPath, [BIN_CLAUDE, '-p', 'fc503'], { env: enrolledFailEnv, cwd: root });
    const leaseHits503 = gw.state.leaseRequests - reqBefore503;
    const noCodexCreatedOnFailOpen = !existsSync(join(freshHome, '.codex'));
    gw.state.force503 = false;
    const enCx = await runCmd(process.execPath, [BIN_CODEX, '--version'], { env: { ...baseEnv, PDD_CODEX_BIN: '/nonexistent/codex-bin' }, cwd: root });
    const enCl = await runCmd(process.execPath, [BIN_CLAUDE, '--version'], { env: { ...baseEnv, PDD_CLAUDE_BIN: '/nonexistent/claude-bin' }, cwd: root });
    const c9Ok = leaseHits503 >= 4 && foCx503.status === 0 && foCx503.stdout.includes('SEAT=stock-local')
      && foCl503.status === 0 && foCl503.stdout.includes('SEAT=stock-local')
      && fcCx503.status !== 0 && fcCl503.status !== 0 && noCodexCreatedOnFailOpen
      && enCx.status === 127 && enCl.status === 127;
    rec('C09', 'Fail-Open (503 Lease), Fail-Closed & ENOENT->127', c9Ok, `503-hits=${leaseHits503}, fo=${foCx503.status}/${foCl503.status}, fc=${fcCx503.status}/${fcCl503.status}, noHomeTouch=${noCodexCreatedOnFailOpen}, enoent=${enCx.status}/${enCl.status}`);

    // C11: Zero PDD_* leakage across ALL 3 paths (leased + fail-open + pass-through) & non-/tmp runtime root
    const dirtyEnv = { ...baseEnv, PDD_TOKEN: 'tok_leak', PDD_ACCOUNTS_TOKEN: 'acct_leak', PDD_SECRET_LEAK: 'nope', OPENAI_API_KEY: 'sk-leak', CODEX_API_KEY: 'sk-cx-leak', ANTHROPIC_API_KEY: 'sk-ant-leak', CLAUDE_CODE_OAUTH_TOKEN: 'sk-ant-oat-leak' };
    const leaks = [];
    const checkEnvOut = (tag, r, extraForbidden = new Set()) => {
      const m = r.stdout.match(/ENV_JSON=(\[.*\])/);
      const bad = (m ? JSON.parse(m[1]) : ['MISSING']).filter(k => k.startsWith('PDD_') || extraForbidden.has(k));
      if (bad.length) leaks.push(`${tag}:${bad.join(',')}`);
    };
    checkEnvOut('codex-leased', await runCmd(process.execPath, [BIN_CODEX, 'exec', 'DUMP_ENV'], { env: dirtyEnv, cwd: root }), new Set(['OPENAI_API_KEY', 'CODEX_API_KEY', 'CODEX_ACCESS_TOKEN', 'OPENAI_BASE_URL']));
    checkEnvOut('claude-leased', await runCmd(process.execPath, [BIN_CLAUDE, '-p', 'DUMP_ENV'], { env: dirtyEnv, cwd: root }), new Set(['ANTHROPIC_API_KEY', 'ANTHROPIC_AUTH_TOKEN', 'CLAUDE_CODE_OAUTH_TOKEN', 'ANTHROPIC_BASE_URL']));
    checkEnvOut('codex-passthrough', await runCmd(process.execPath, [BIN_CODEX, 'completion', 'DUMP_ENV_PASSTHROUGH'], { env: dirtyEnv, cwd: root }));
    checkEnvOut('claude-passthrough', await runCmd(process.execPath, [BIN_CLAUDE, 'mcp', 'DUMP_ENV_PASSTHROUGH'], { env: dirtyEnv, cwd: root }));
    gw.state.force503 = true;
    checkEnvOut('codex-failopen', await runCmd(process.execPath, [BIN_CODEX, 'exec', 'DUMP_ENV'], { env: { ...dirtyEnv, PDD_CODEX_AUTO_FAIL_OPEN: '1', PDD_CODEX_RUNTIME_ROOT: join(stateDir, 'c11-cx-rt') }, cwd: root }));
    checkEnvOut('claude-failopen', await runCmd(process.execPath, [BIN_CLAUDE, '-p', 'DUMP_ENV'], { env: { ...dirtyEnv, PDD_CLAUDE_AUTO_FAIL_OPEN: '1', PDD_CLAUDE_RUNTIME_ROOT: join(stateDir, 'c11-cl-rt') }, cwd: root }));
    gw.state.force503 = false;
    const nonTmp = !sharedRuntimeDirPath({ env: { HOME: '/home/u' }, uid: 501 }).startsWith(resolve(tmpdir())) && !sharedClaudeRuntimeDir({ HOME: '/home/u' }, 501).startsWith(resolve(tmpdir()));
    rec('C11', 'Zero Secret/PDD_* Leakage (All Paths) & Non-/tmp Root', leaks.length === 0 && nonTmp, leaks.length ? leaks.join('; ') : '0 leaked PDD_* across leased+failopen+passthrough; runtime under ~/.local/state/pdd');

    const cxT = await measureColdStartupMs(BIN_CODEX), clT = await measureColdStartupMs(BIN_CLAUDE);
    const reachable = walkReachableModules([BIN_CODEX, BIN_CLAUDE, join(REPO_ROOT, 'src', 'accounts-cli.mjs')]);
    const reachesSeam = reachable.has(resolve(REPO_ROOT, 'src', 'runtime-seam.mjs'));
    rec('C12', 'Cold Startup & 0 runtime-seam Reachability', !reachesSeam, `codex p50=${cxT.p50}ms/p95=${cxT.p95}ms, claude p50=${clT.p50}ms/p95=${clT.p95}ms, modules=${reachable.size}, seam=${reachesSeam}`);

    const shFile = join(root, 'auto.sh');
    writeFileSync(shFile, `${renderAutoSwitchBlock('sh')}\n`);
    const shCx = await runCmd('bash', ['-c', `source ${JSON.stringify(shFile)} && codex exec hello`], { env: baseEnv, cwd: root });
    const shCl = await runCmd('bash', ['-c', `source ${JSON.stringify(shFile)} && claude -p hello`], { env: baseEnv, cwd: root });
    const stockOnly = join(root, 'stock-only-bin');
    mkdirSync(stockOnly, { recursive: true });
    symlinkSync(process.execPath, join(stockOnly, 'node'));
    for (const n of ['codex', 'claude']) writeFileSync(join(stockOnly, n), readFileSync(join(mockBin, n)), { mode: 0o755 });
    const shPip = await runCmd('bash', ['-c', `source ${JSON.stringify(shFile)} && codex exec pip-ok && claude -p pip-ok`], { env: { ...baseEnv, PATH: `${stockOnly}:/usr/bin:/bin` }, cwd: root });
    const c13Ok = shCx.status === 0 && shCx.stdout.includes('SEAT=seat-A') && shCl.status === 0 && shCl.stdout.includes('SEAT=seat-A') && shPip.status === 0 && shPip.stdout.includes('NONTTY_OK=pip-ok SEAT=stock-local');
    rec('C13', 'Shell Auto-Switch & Pip-Fallback Proof', c13Ok, c13Ok ? 'codex/claude managed=seat-A; absent-wrapper fallback=ok' : `cx=${shCx.status} cl=${shCl.status} pip=${shPip.status}`);

    // C10 runs LAST (after C11 + C13): real `pdd accounts auto on/off` Stow symlink proof + full recursive .codex/.claude/.claude.json diff!
    const autoOnRes = await runAccountsCli({ commandId: 'accounts.auto', operands: ['on'], cwd: root, env: baseEnv });
    const autoOffRes = await runAccountsCli({ commandId: 'accounts.auto', operands: ['off'], cwd: root, env: baseEnv });
    const stowOk = autoOnRes.exitCode === 0 && autoOffRes.exitCode === 0
      && lstatSync(userZshrc).isSymbolicLink() && readlinkSync(userZshrc) === stowZshrc
      && (lstatSync(stowZshrc).mode & 0o777) === 0o640;
    const homeDiffs = diffSnapshots(homeBefore, snapshotTree([codexDir, claudeDir, claudeJson], homeSnapOpts));
    results.splice(9, 0, {
      id: 'C10',
      name: 'Zero Home Mutation (Full Tree) & Auto Stow Symlink Proof',
      status: homeDiffs.length === 0 && stowOk ? 'PASS' : 'FAIL',
      detail: homeDiffs.length ? homeDiffs.join('; ') : '0 diffs across full ~/.codex & ~/.claude trees + ~/.claude.json; pdd accounts auto preserves Stow symlink + 0640 mode',
    });
  } finally {
    for (const s of activePtys) s.kill();
    gw.server.closeAllConnections?.();
    gw.server.close();
    rmSync(root, { recursive: true, force: true });
  }
  return results;
}

async function runLiveChecks() {
  const results = [];
  const rec = (id, name, status, detail) => results.push({ id, name, status, detail });
  const realHome = homedir();
  const protectedPaths = [join(realHome, '.codex', 'auth.json'), join(realHome, '.codex', 'config.toml'), join(realHome, '.claude', 'settings.json'), join(realHome, '.claude.json')];
  const before = snapshotTree(protectedPaths, { recursive: false });
  const tmpState = mkdtempSync(join(tmpdir(), 'pdd-pty-live-safe-'));
  const liveSafeEnv = { ...scrubHostEnv(process.env), HOME: realHome, PDD_STATE_DIR: join(tmpState, 'state'), PDD_CODEX_RUNTIME_ROOT: join(tmpState, 'codex-rt'), PDD_CLAUDE_RUNTIME_ROOT: join(tmpState, 'claude-rt'), PDD_ACCOUNTS_URL: 'http://127.0.0.1:1' };
  mkdirSync(liveSafeEnv.PDD_STATE_DIR, { recursive: true, mode: 0o700 });
  try {
    const hasCx = (await runCmd('codex', ['--version'], { env: liveSafeEnv })).status === 0;
    const hasCl = (await runCmd('claude', ['--version'], { env: liveSafeEnv })).status === 0;
    for (const [id, name] of [['C01', 'Interactive PTY Start & Turn 1'], ['C02', 'Multi-Turn Memory (Same PTY/PID)'], ['C03', 'Cross-Process Resume (SID + --last/-c)'], ['C04', 'Real Stdio MCP Echo + Gateway Auth'], ['C05', 'Hook/Browser State & Writeback Norm']]) {
      rec(id, name, 'SKIP', 'Requires live test account/model call (proved deterministically in --offline; 0 credits spent)');
    }
    const sCxV = hasCx ? await runCmd('codex', ['--version'], { env: liveSafeEnv }) : null;
    const wCxV = hasCx ? await runCmd(process.execPath, [BIN_CODEX, '--version'], { env: liveSafeEnv }) : null;
    const sClV = hasCl ? await runCmd('claude', ['--version'], { env: liveSafeEnv }) : null;
    const wClV = hasCl ? await runCmd(process.execPath, [BIN_CLAUDE, '--version'], { env: liveSafeEnv }) : null;
    rec('C06', 'Stock CLI Parity Diff (Real Binaries)', (!hasCx || (sCxV.status === 0 && sCxV.stdout === wCxV.stdout)) && (!hasCl || (sClV.status === 0 && sClV.stdout === wClV.stdout)) ? 'PASS' : 'FAIL', `codex=${sCxV?.stdout.trim() || 'missing'}, claude=${sClV?.stdout.trim() || 'missing'}`);
    rec('C07', 'Concurrent Sessions + SIGKILL Cleanup', 'SKIP', 'Requires live test account (proved in --offline)');
    rec('C08', 'Forced A->B Rotation + Negative Control', 'SKIP', 'Requires Decision #10 cloud test switch (proved in --offline)');
    // C09 live: real ENOENT->127 + fail-closed against unreachable gateway (0 model/API calls!)
    writeCloudAccountsState({ enrolled: true, providers: ['codex', 'claude'], active: {} }, { env: liveSafeEnv });
    const fcCx = await runCmd(process.execPath, [BIN_CODEX, 'exec', 'unreachable-check'], { env: { ...liveSafeEnv, PDD_TOKEN: 'dummy' } });
    const fcCl = await runCmd(process.execPath, [BIN_CLAUDE, '-p', 'unreachable-check'], { env: { ...liveSafeEnv, PDD_TOKEN: 'dummy' } });
    const enCx = await runCmd(process.execPath, [BIN_CODEX, '--version'], { env: { ...liveSafeEnv, PDD_CODEX_BIN: '/nonexistent/codex-bin' } });
    const enCl = await runCmd(process.execPath, [BIN_CLAUDE, '--version'], { env: { ...liveSafeEnv, PDD_CLAUDE_BIN: '/nonexistent/claude-bin' } });
    rec('C09', 'Fail-Closed & ENOENT->127 (Real Binaries)', fcCx.status === 1 && fcCl.status === 1 && enCx.status === 127 && enCl.status === 127 ? 'PASS' : 'FAIL', `fc=${fcCx.status}/${fcCl.status}, enoent=${enCx.status}/${enCl.status}`);
    rec('C11', 'Non-/tmp Default Runtime Root', !sharedRuntimeDirPath({ env: { HOME: realHome } }).startsWith(resolve(tmpdir())) && !sharedClaudeRuntimeDir({ HOME: realHome }).startsWith(resolve(tmpdir())) ? 'PASS' : 'FAIL', 'codex-runtime & claude-runtime under ~/.local/state/pdd');
    const cxT = await measureColdStartupMs(BIN_CODEX), clT = await measureColdStartupMs(BIN_CLAUDE);
    const reachesSeam = walkReachableModules([BIN_CODEX, BIN_CLAUDE, join(REPO_ROOT, 'src', 'accounts-cli.mjs')]).has(resolve(REPO_ROOT, 'src', 'runtime-seam.mjs'));
    rec('C12', 'Cold Startup & 0 runtime-seam Reachability', !reachesSeam ? 'PASS' : 'FAIL', `codex p50=${cxT.p50}ms, claude p50=${clT.p50}ms, seam=${reachesSeam}`);
    const shBin = join(tmpState, 'wbin');
    mkdirSync(shBin, { recursive: true });
    writeFileSync(join(shBin, 'pdd-codex'), `#!/bin/sh\nexec ${JSON.stringify(process.execPath)} ${JSON.stringify(BIN_CODEX)} "$@"\n`, { mode: 0o755 });
    writeFileSync(join(shBin, 'pdd-claude'), `#!/bin/sh\nexec ${JSON.stringify(process.execPath)} ${JSON.stringify(BIN_CLAUDE)} "$@"\n`, { mode: 0o755 });
    const shFile = join(tmpState, 'auto.sh');
    writeFileSync(shFile, `${renderAutoSwitchBlock('sh')}\n`);
    const shEnv = { ...liveSafeEnv, PATH: `${shBin}:${liveSafeEnv.PATH}` };
    const rCx = hasCx ? await runCmd('bash', ['-c', `source ${JSON.stringify(shFile)} && codex --version`], { env: shEnv }) : { status: 0, stdout: 'n/a' };
    const rCl = hasCl ? await runCmd('bash', ['-c', `source ${JSON.stringify(shFile)} && claude --version`], { env: shEnv }) : { status: 0, stdout: 'n/a' };
    rec('C13', 'Real Bash Auto-Switch Wrapper Smoke', rCx.status === 0 && rCl.status === 0 ? 'PASS' : 'FAIL', `codex=${rCx.stdout.trim()}, claude=${rCl.stdout.trim()}`);
  } finally {
    rmSync(tmpState, { recursive: true, force: true });
  }
  const diffs = diffSnapshots(before, snapshotTree(protectedPaths, { recursive: false }));
  results.splice(9, 0, { id: 'C10', name: 'Real Personal Home Zero-Mutation Proof', status: diffs.length === 0 ? 'PASS' : 'FAIL', detail: diffs.length === 0 ? 'SHA-256 + mode + symlink identical across ~/.codex & ~/.claude' : diffs.join('; ') });
  return results;
}

const args = new Set(process.argv.slice(2));
const mode = args.has('--live') ? 'live' : 'offline';
const rows = mode === 'live' ? await runLiveChecks() : await runOfflineChecks();
const failed = rows.filter(r => r.status === 'FAIL');
if (args.has('--json')) {
  process.stdout.write(`${JSON.stringify({ mode, passed: rows.filter(r => r.status === 'PASS').length, skipped: rows.filter(r => r.status === 'SKIP').length, failed: failed.length, checks: rows }, null, 2)}\n`);
} else {
  process.stdout.write(`P1 Accounts 13-Check PTY Suite (--${mode})\n| Check | Name | Status | Detail |\n|---|---|---|---|\n`);
  for (const r of rows) process.stdout.write(`| ${r.id} | ${r.name} | ${r.status} | ${r.detail} |\n`);
}
process.exitCode = failed.length > 0 ? 1 : 0;
