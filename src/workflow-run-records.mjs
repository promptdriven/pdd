// Generated from prompts/cli/workflow-run-records.prompt.md (sha256: 8f41eeba1d4b9e8b0caf1495ff2c40595e9c26808fa5dccd8f0413f8023ec2ac).
import { promises as fs } from 'node:fs';
import { join, dirname, basename } from 'node:path';
import { homedir } from 'node:os';

const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
const sessionFile = /^rollout-[^/]+\.jsonl$/;
const sessionId = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const fsOf = ports => ports.fs ?? fs;
const object = value => value && typeof value === 'object' && !Array.isArray(value);

const normalizedEntry = raw => ({ v: raw.v ?? 1, runId: raw.runId, workflow: raw.workflow ?? null,
  repo: raw.repo ?? null, issue: object(raw.issue) ? { number: raw.issue.number ?? null, url: raw.issue.url ?? null, title: raw.issue.title ?? null } : null,
  agent: raw.agent ?? null, root: raw.root ?? null, runDir: raw.runDir, startedAt: raw.startedAt ?? null });

export async function appendRunIndex(entry, ports = {}) {
  try {
    const home = ports.home ?? process.env.HOME ?? homedir();
    if (!object(entry) || !UUID.test(entry.runId ?? '') || typeof entry.runDir !== 'string' || !entry.runDir.startsWith('/')) return { ok: false, code: 'bad_input' };
    const io = fsOf(ports), dir = join(home, '.pdd', 'runs'), path = join(dir, 'index.jsonl');
    await io.mkdir(dir, { recursive: true, mode: 0o700 });
    const text = JSON.stringify(normalizedEntry(entry)) + '\n';
    if (Buffer.byteLength(text) > 4096) return { ok: false, code: 'too_large' };
    const handle = await io.open(path, 'a', 0o600);
    try { await handle.write(text); } finally { await handle.close(); }
    return { ok: true };
  } catch (error) { return { ok: false, code: error?.code ?? 'write_failed' }; }
}

async function readMachineIndex(ports = {}) {
  try {
    const home = ports.home ?? process.env.HOME ?? homedir(), io = fsOf(ports);
    const text = await io.readFile(join(home, '.pdd', 'runs', 'index.jsonl'), 'utf8');
    const map = new Map();
    for (const line of text.split('\n')) {
      if (!line.trim() || Buffer.byteLength(line) > 16384) continue;
      try { const raw = JSON.parse(line); if (object(raw) && UUID.test(raw.runId ?? '') && typeof raw.runDir === 'string' && raw.runDir.startsWith('/')) map.set(raw.runId, normalizedEntry(raw)); } catch {}
    }
    return [...map.values()];
  } catch { return []; }
}

async function gitDirFor(cwd, ports = {}) {
  const io = fsOf(ports);
  let current = cwd;
  for (let depth = 0; depth < 64; depth++) {
    const dot = join(current, '.git');
    try {
      const stat = await io.lstat(dot);
      if (stat.isDirectory()) return dot;
      if (stat.isFile()) {
        const text = await io.readFile(dot, 'utf8');
        const match = text.match(/^gitdir:\s*(.+)\s*$/m);
        if (match) return match[1].startsWith('/') ? match[1] : join(current, match[1]);
      }
    } catch { /* keep walking toward the checkout root */ }
    const parent = dirname(current);
    if (parent === current) break;
    current = parent;
  }
  return null;
}
async function allGitDirs(cwd, ports = {}) {
  const io = fsOf(ports), own = await gitDirFor(cwd, ports), dirs = [];
  if (!own) return dirs;
  dirs.push(own);
  let common = own;
  try {
    const raw = (await io.readFile(join(own, 'commondir'), 'utf8')).trim();
    if (raw) common = raw.startsWith('/') ? raw : join(own, raw);
  } catch { /* a main checkout has no worktree commondir file */ }
  if (common !== own) dirs.push(common);
  for (const row of await io.readdir(join(common, 'worktrees'), { withFileTypes: true }).catch(() => []))
    if (row.isDirectory?.()) dirs.push(join(common, 'worktrees', row.name));
  return [...new Set(dirs)];
}
export async function gitCommonDir(cwd, ports = {}) {
  const io = fsOf(ports), own = await gitDirFor(cwd, ports);
  if (!own) return null;
  try {
    const raw = (await io.readFile(join(own, 'commondir'), 'utf8')).trim();
    return raw ? (raw.startsWith('/') ? raw : join(own, raw)) : own;
  } catch { return own; }
}

export async function readJournalLast(runDir, ports = {}) {
  try {
    const text = await fsOf(ports).readFile(join(runDir, 'journal.jsonl'), 'utf8');
    const rows = text.trimEnd().split(/\r?\n/).filter(Boolean);
    if (!rows.length) return { value: null, warnings: ['missing'] };
    const row = JSON.parse(rows.at(-1));
    if (!object(row) || !Number.isSafeInteger(row.seq) || !object(row.state) || row.state.runId !== basename(runDir))
      return { value: null, warnings: ['bad_record'] };
    return { value: row, warnings: [] };
  } catch (error) { return { value: null, warnings: [error?.code === 'ENOENT' ? 'missing' : 'unreadable'] }; }
}

export async function readRunIndex(ports = {}) {
  if (ports.all) return { entries: await readMachineIndex(ports), dropped: 0 };
  const dirs = await allGitDirs(ports.cwd ?? process.cwd(), ports);
  const entries = [], io = fsOf(ports), seen = new Set();
  for (const gitDir of dirs) {
    const root = join(gitDir, 'pdd', 'workflows');
    let names; try { names = await io.readdir(root); } catch { continue; }
    for (const name of names.filter(item => UUID.test(item)).sort()) {
      if (seen.has(name)) continue;
      const runDir = join(root, name), last = await readJournalLast(runDir, ports), state = last.value?.state;
      if (!state || state.runId !== name) continue;
      seen.add(name);
      entries.push({ v: 1, runId: name, workflow: state.name ?? null, repo: state.repo ?? null,
        issue: object(state.issue) ? { number: state.issue.number ?? null, url: state.issue.url ?? null, title: state.issue.title ?? null } : null,
        agent: state.agent ?? null, root: state.root ?? null, runDir, startedAt: state.startedAt ?? null });
    }
  }
  return { entries, dropped: 0 };
}

const nativeSession = (backend, fallbackAgent) => {
  const value = backend?.nativeSession?.value;
  const agent = backend?.agent ?? backend?.agentKind ?? fallbackAgent;
  return typeof value === 'string' && value && ['codex', 'claude'].includes(agent) ? { agent, id: value } : null;
};
export function reopenCommand(root, session) {
  if (!session || typeof root !== 'string' || !root.startsWith('/')) return null;
  const quoted = `'${root.replaceAll("'", "'\\''")}'`;
  return `cd ${quoted} && ${session.agent === 'codex' ? 'codex resume' : 'claude --resume'} ${session.id}`;
}

const toEpoch = value => {
  if (Number.isFinite(value)) return value;
  if (typeof value !== 'string' || !value.trim()) return null;
  const parsed = Date.parse(value); return Number.isFinite(parsed) ? parsed : null;
};
function sessionMeta(text) {
  for (const line of text.split(/\r?\n/, 8)) {
    if (!line) continue;
    try {
      const row = JSON.parse(line), payload = row?.payload ?? row;
      const meta = row?.session_meta ?? payload?.session_meta ?? payload;
      if (row?.type !== 'session_meta' && payload?.type !== 'session_meta' && !row?.session_meta && !payload?.session_meta) continue;
      const id = meta.id ?? meta.session_id, cwd = meta.cwd, timestamp = toEpoch(meta.timestamp ?? payload.timestamp ?? row.timestamp);
      return sessionId.test(id ?? '') && typeof cwd === 'string' && Number.isFinite(timestamp) ? { id, cwd, timestamp } : null;
    } catch { /* try the next metadata line */ }
  }
  return null;
}
async function sessionFiles(stage, ports = {}) {
  const io = fsOf(ports), home = ports.home ?? process.env.HOME ?? homedir();
  const root = stage.agent === 'codex' ? join(ports.codexHome ?? process.env.CODEX_HOME ?? join(home, '.codex'), 'sessions')
    : join(ports.claudeHome ?? home, '.claude', 'projects', stage.root.replaceAll('/', '-'));
  const found = [];
  async function walk(dir, depth = 0) {
    if (depth > 20) return;
    let rows; try { rows = await io.readdir(dir, { withFileTypes: true }); } catch { return; }
    for (const row of rows) {
      if (row.isSymbolicLink?.()) continue;
      const path = join(dir, row.name);
      if (row.isDirectory?.()) await walk(path, depth + 1);
      else if (row.isFile?.() && (stage.agent === 'codex' ? sessionFile.test(row.name) : row.name.endsWith('.jsonl'))) found.push(path);
    }
  }
  await walk(root);
  const matches = [];
  for (const path of found) {
    let meta; try { meta = sessionMeta(await io.readFile(path, 'utf8')); } catch { continue; }
    if (meta && meta.cwd === stage.root && meta.timestamp >= stage.startedAt && meta.timestamp <= stage.endedAt)
      matches.push({ agent: stage.agent, id: meta.id, source: 'session-file' });
  }
  return matches;
}
export async function matchStageSessionFiles(stage, ports = {}) {
  if (!stage || !['codex', 'claude'].includes(stage.agent) || typeof stage.root !== 'string'
    || !Number.isFinite(stage.startedAt) || !Number.isFinite(stage.endedAt) || stage.endedAt < stage.startedAt)
    return { matches: [], reason: 'stage window unavailable' };
  const matches = await sessionFiles(stage, ports);
  return { matches, reason: matches.length === 1 ? null : matches.length ? `${matches.length} session files matched the worktree and stage window` : 'no session file matched the worktree and stage window' };
}

export async function runStatusFromState(state, extras = {}, ports = {}) {
  if (!object(state) || !Array.isArray(state.definitions) || !Number.isInteger(state.index))
    return { v: 1, runId: null, workflow: null, state: 'unknown', steps: [] };
  const completed = new Map((state.completed ?? []).filter(item => object(item) && typeof item.id === 'string').map(item => [item.id, item]));
  const current = state.definitions[state.index];
  const status = state.index >= state.definitions.length ? 'completed' : current?.kind === 'human' ? 'waiting' : state.pending ? 'running' : 'waiting';
  const steps = [];
  for (let i = 0; i < state.definitions.length; i++) {
    const def = state.definitions[i], item = completed.get(def.id), pending = state.pending?.stage === def.id ? state.pending : null;
    const source = item ?? pending, backend = source?.backend, session = nativeSession(backend, state.agent);
    const row = { id: def.id, kind: def.kind, state: item?.skipped ? 'skipped' : item ? 'done' : i === state.index ? status : i > state.index ? 'next' : 'unknown',
      startedAt: source?.startedAt ?? null, endedAt: source?.endedAt ?? null, agent: source?.agent ?? session?.agent ?? (source ? state.agent : null), session, reopen: reopenCommand(state.root, session) };
    if (row.state === 'done' && !row.session && row.agent && Number.isFinite(row.startedAt) && Number.isFinite(row.endedAt)) {
      const found = await matchStageSessionFiles({ agent: row.agent, root: state.root, startedAt: row.startedAt, endedAt: row.endedAt }, ports);
      if (found.matches.length === 1) { row.session = found.matches[0]; row.reopen = reopenCommand(state.root, row.session); }
      else row.sessionReason = `session file unavailable: ${found.reason}`;
    }
    steps.push(row);
  }
  return { v: 1, runId: state.runId, workflow: state.name ?? null, repo: state.repo ?? null, issue: state.issue ?? null,
    root: state.root ?? null, agent: state.agent ?? null, startedAt: state.startedAt ?? null, journalSeq: state.seq ?? 0, state: status, stage: current ? { id: current.id, index: state.index, total: state.definitions.length } : null, steps,
    updatedAt: extras.now ?? null };
}

