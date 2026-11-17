// Prompt: prompts/cli/autopilot-merge-queue.prompt.md
import { execFile as execFileCb, spawn } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { dirname, join, posix, resolve } from 'node:path';
import { findOwners, headerEntries, headerHashState, isTestOwnedPath, isTestPromptPath, promptHeaderHash } from './file-owner.mjs';

export const MERGE_QUEUE_SCHEMA = 'pdd.merge-queue.v1';
export const MAX_ATTEMPTS_PER_BASE = 2;

const QUEUE_FILE = 'merge-queue.json';
const LOCK_FILE = 'merge-queue.lock';
const LOCK_STALE_MS = 15 * 60 * 1000;
const GIT_IDENTITY = ['-c', 'user.name=Autopilot', '-c', 'user.email=autopilot@promptdriven.local'];
const PROTECTED_BRANCHES = new Set(['main', 'master', 'trunk', 'develop', 'production', 'release', 'head']);
const HEADER_LINE = /^(\s*(?:(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')?\s*Generated from|(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')\s*Prompt:)) (\S+\.prompt\.md)(?: \(sha256: ([a-f0-9]{0,64})\)| sha256=([a-f0-9]{0,64}))?(\.?\s*(?:\*\/|-->|"""|''')?\s*)$/;
const CONFLICT_MARKER_LINE = /^(?:<<<<<<< |\|\|\|\|\|\|\| |=======\r?$|>>>>>>> )/m;

const isObj = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const stripCtl = text => String(text ?? '')
  .replace(/\x1b(?:\[[0-9;?]*[ -/]*[@-~]|\][^\u0007\x1b]*(?:\u0007|\x1b\\)|[@-Z\\-_])/g, '')
  .replace(/[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f-\u009f]/g, ' ');

export function isAllowedMergeQueueBranch(branch, baseBranch = 'main') {
  if (typeof branch !== 'string') return false;
  const trimmed = branch.trim();
  if (!trimmed || trimmed.length > 200 || trimmed.startsWith('-') || trimmed.includes('..') || /\s/.test(trimmed)) return false;
  const lower = trimmed.toLowerCase();
  if (PROTECTED_BRANCHES.has(lower) || lower === String(baseBranch ?? '').trim().toLowerCase()) return false;
  if (lower.startsWith('refs/') || lower.startsWith('origin/')) return false;
  return /^pdd\/core-\d+-[A-Za-z0-9._-]+$/.test(trimmed);
}

export function sanitizePublicQueueNote(text) {
  let out = stripCtl(text);
  out = out.replace(/\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b/gi, '');
  out = out.replace(/\bsha256:\s*[0-9a-f]{7,64}\b/gi, 'header digest');
  out = out.replace(/\b\d{8}-\d{6}-[a-z0-9]{4,12}\b/gi, '');
  out = out.replace(/\b[0-9a-f]{7,64}\b/gi, '');
  out = out.replace(/\(\s*\)/g, '').replace(/\s{2,}/g, ' ').trim();
  return out.slice(0, 500);
}

export function hasGitConflictMarkers(text) {
  return CONFLICT_MARKER_LINE.test(String(text ?? ''));
}

export function buildConflictAgentInvocation(agent = {}) {
  const kind = typeof agent?.kind === 'string' ? agent.kind.trim().toLowerCase() : '';
  const model = typeof agent?.model === 'string' && agent.model.trim() ? agent.model.trim() : null;
  const cmd = fallback => (typeof agent?.command === 'string' && agent.command.trim() ? agent.command.trim() : fallback);
  const modelArgs = model ? ['--model', model] : [];
  if (kind === 'codex') {
    return {
      kind: 'codex',
      command: cmd('codex'),
      args: ['exec', '--json', '--dangerously-bypass-approvals-and-sandbox', '-c', 'features.multi_agent=false', ...modelArgs, '-'],
    };
  }
  if (kind === 'claude') {
    return {
      kind: 'claude',
      command: cmd('claude'),
      args: ['-p', '--output-format', 'stream-json', '--verbose', '--permission-mode', 'bypassPermissions', ...modelArgs],
    };
  }
  if (kind === 'gemini') {
    return {
      kind: 'gemini',
      command: cmd('gemini'),
      args: ['-p', '', '--output-format', 'stream-json', '--approval-mode', 'yolo', ...modelArgs],
    };
  }
  if (kind === 'agy') {
    return {
      kind: 'agy',
      command: cmd('agy'),
      args: ['--input-format', 'text', '--output-format', 'stream-json', '--dangerously-skip-permissions', ...modelArgs],
    };
  }
  throw new Error(`Unsupported conflict-resolution agent kind: ${String(agent?.kind ?? 'none')}`);
}

function defaultGitPort(args, { cwd } = {}) {
  return new Promise(resolvePromise => {
    execFileCb('git', args, {
      cwd,
      encoding: 'utf8',
      maxBuffer: 16 * 1024 * 1024,
      env: { ...process.env, GIT_TERMINAL_PROMPT: '0' },
    }, (error, stdout = '', stderr = '') => {
      const code = error ? (Number.isInteger(error.code) ? error.code : 1) : 0;
      resolvePromise({ code, stdout: String(stdout), stderr: String(stderr || error?.message || '') });
    });
  });
}

function defaultExecAgent({ command, args = [], input = '', cwd, timeoutMs = 180_000, env = process.env }) {
  return new Promise(resolvePromise => {
    const child = spawn(command, args, { cwd, env, stdio: ['pipe', 'pipe', 'pipe'] });
    let stdout = '', stderr = '', settled = false;
    const timer = setTimeout(() => {
      if (settled) return;
      settled = true;
      try { child.kill('SIGKILL'); } catch { /* Best effort. */ }
      resolvePromise({ code: 124, stdout, stderr: `${stderr}\nconflict agent timed out` });
    }, timeoutMs);
    child.stdout.on('data', chunk => { if (stdout.length < 256_000) stdout += chunk.toString('utf8'); });
    child.stderr.on('data', chunk => { if (stderr.length < 256_000) stderr += chunk.toString('utf8'); });
    child.on('error', err => {
      if (settled) return;
      settled = true; clearTimeout(timer);
      resolvePromise({ code: 1, stdout, stderr: err.message });
    });
    child.on('close', code => {
      if (settled) return;
      settled = true; clearTimeout(timer);
      resolvePromise({ code: code ?? 1, stdout, stderr });
    });
    try { child.stdin.end(input); } catch { /* Closed early. */ }
  });
}

function isPidAlive(pid) {
  if (!Number.isSafeInteger(pid) || pid <= 0) return false;
  try { process.kill(pid, 0); return true; } catch (err) { return err?.code === 'EPERM'; }
}

async function withMergeQueueLock(stateDir, { fs = nativeFs, now = Date.now } = {}, fn) {
  fs.mkdirSync(stateDir, { recursive: true, mode: 0o700 });
  const lockPath = join(stateDir, LOCK_FILE);
  const acquire = () => {
    const fd = fs.openSync(lockPath, 'wx', 0o600);
    try { fs.writeFileSync(fd, JSON.stringify({ pid: process.pid, at: now() })); }
    finally { fs.closeSync(fd); }
  };
  let acquired = false;
  try {
    acquire();
    acquired = true;
  } catch (err) {
    if (err?.code !== 'EEXIST') throw err;
    try {
      const existing = JSON.parse(fs.readFileSync(lockPath, 'utf8'));
      const stale = !isObj(existing)
        || !Number.isFinite(existing.at)
        || now() - existing.at > LOCK_STALE_MS
        || (existing.pid !== process.pid && !isPidAlive(existing.pid));
      if (stale) {
        fs.rmSync(lockPath, { force: true });
        acquire();
        acquired = true;
      }
    } catch {
      try { fs.rmSync(lockPath, { force: true }); acquire(); acquired = true; } catch { /* Still locked. */ }
    }
  }
  if (!acquired) return { locked: true };
  try {
    return await fn();
  } finally {
    try { fs.rmSync(lockPath, { force: true }); } catch { /* Best effort. */ }
  }
}

function sortFifo(items) {
  return [...items].sort((a, b) => (a.readyAt - b.readyAt) || (a.pr - b.pr));
}

function normalizeQueueItem(raw) {
  if (!isObj(raw) || !Number.isSafeInteger(raw.pr) || raw.pr <= 0) return null;
  const issue = Number.isSafeInteger(raw.issue) && raw.issue > 0 ? raw.issue : raw.pr;
  const issues = Array.isArray(raw.issues) && raw.issues.length
    ? [...new Set(raw.issues.filter(n => Number.isSafeInteger(n) && n > 0))]
    : [issue];
  const state = ['queued', 'processing', 'synced', 'merged', 'ejected', 'closed'].includes(raw.state) ? raw.state : 'queued';
  const attemptsByBase = isObj(raw.attemptsByBase)
    ? Object.fromEntries(Object.entries(raw.attemptsByBase).filter(([k, v]) => typeof k === 'string' && k && Number.isSafeInteger(v) && v > 0))
    : {};
  return {
    pr: raw.pr,
    issue,
    issues,
    branch: typeof raw.branch === 'string' ? raw.branch.trim() : '',
    baseBranch: typeof raw.baseBranch === 'string' && raw.baseBranch.trim() ? raw.baseBranch.trim() : 'main',
    headSha: typeof raw.headSha === 'string' ? raw.headSha.trim() : '',
    readyAt: Number.isFinite(raw.readyAt) ? raw.readyAt : 0,
    state,
    syncedBaseSha: typeof raw.syncedBaseSha === 'string' && raw.syncedBaseSha ? raw.syncedBaseSha : null,
    attemptsByBase,
    mergedAt: Number.isFinite(raw.mergedAt) ? raw.mergedAt : null,
    ejectedAt: Number.isFinite(raw.ejectedAt) ? raw.ejectedAt : null,
    ejectedBaseSha: typeof raw.ejectedBaseSha === 'string' && raw.ejectedBaseSha ? raw.ejectedBaseSha : null,
    ejectedHeadSha: typeof raw.ejectedHeadSha === 'string' && raw.ejectedHeadSha ? raw.ejectedHeadSha : null,
    ejectReason: typeof raw.ejectReason === 'string' && raw.ejectReason ? raw.ejectReason : null,
    lastError: typeof raw.lastError === 'string' && raw.lastError ? raw.lastError : null,
  };
}

export function readMergeQueue(stateDir, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const file = join(resolve(stateDir), QUEUE_FILE);
  try {
    const parsed = JSON.parse(fs.readFileSync(file, 'utf8'));
    if (!isObj(parsed) || !Array.isArray(parsed.items)) return { schema: MERGE_QUEUE_SCHEMA, updatedAt: 0, items: [] };
    const byPr = new Map();
    for (const raw of parsed.items) {
      const item = normalizeQueueItem(raw);
      if (item) byPr.set(item.pr, item);
    }
    return {
      schema: MERGE_QUEUE_SCHEMA,
      updatedAt: Number.isFinite(parsed.updatedAt) ? parsed.updatedAt : 0,
      items: sortFifo([...byPr.values()]),
    };
  } catch {
    return { schema: MERGE_QUEUE_SCHEMA, updatedAt: 0, items: [] };
  }
}

function writeMergeQueue(stateDir, items, { fs = nativeFs, now = Date.now } = {}) {
  const dir = resolve(stateDir);
  fs.mkdirSync(dir, { recursive: true, mode: 0o700 });
  const sorted = sortFifo(items.map(normalizeQueueItem).filter(Boolean));
  const doc = { schema: MERGE_QUEUE_SCHEMA, updatedAt: now(), items: sorted };
  const target = join(dir, QUEUE_FILE);
  const tmp = `${target}.${process.pid}.${randomUUID().slice(0, 8)}.tmp`;
  fs.writeFileSync(tmp, `${JSON.stringify(doc, null, 2)}\n`, { mode: 0o600 });
  fs.renameSync(tmp, target);
  return doc;
}

export async function enqueueMergeQueueItem(input, ports = {}) {
  const fs = ports.fs ?? nativeFs, now = ports.now ?? Date.now;
  const stateDir = resolve(input.stateDir);
  const pr = Number(input.pr);
  if (!Number.isSafeInteger(pr) || pr <= 0) throw new Error('Invalid PR number for merge queue');
  const baseBranch = typeof input.baseBranch === 'string' && input.baseBranch.trim() ? input.baseBranch.trim() : 'main';
  const branch = typeof input.branch === 'string' ? input.branch.trim() : '';
  if (!isAllowedMergeQueueBranch(branch, baseBranch)) {
    throw new Error(`Refusing to enqueue non-Autopilot or protected branch: ${branch || '(empty)'}`);
  }
  const headSha = String(input.headSha ?? '').trim();
  if (!headSha) throw new Error('Missing headSha for merge queue entry');

  let out = null;
  const lockRes = await withMergeQueueLock(stateDir, { fs, now }, async () => {
    const current = readMergeQueue(stateDir, { fs });
    const byPr = new Map(current.items.map(i => [i.pr, i]));
    const existing = byPr.get(pr);
    const issue = Number.isSafeInteger(input.issue) && input.issue > 0 ? input.issue : existing?.issue ?? pr;
    const issues = Array.isArray(input.issues) && input.issues.length
      ? [...new Set(input.issues.filter(n => Number.isSafeInteger(n) && n > 0))]
      : existing?.issues ?? [issue];
    let entry;
    if (!existing) {
      entry = normalizeQueueItem({
        pr,
        issue,
        issues,
        branch,
        baseBranch,
        headSha,
        readyAt: Number.isFinite(input.readyAt) ? input.readyAt : now(),
        state: input.syncedBaseSha ? 'synced' : 'queued',
        syncedBaseSha: input.syncedBaseSha ?? null,
        attemptsByBase: {},
      });
    } else if (existing.state === 'merged') {
      entry = existing;
    } else if (existing.state === 'ejected' && existing.ejectedHeadSha === headSha && !input.forceRequeue) {
      entry = existing;
    } else {
      const headChanged = existing.headSha !== headSha;
      const wasTerminal = existing.state === 'ejected' || existing.state === 'closed';
      entry = normalizeQueueItem({
        ...existing,
        issue,
        issues,
        branch,
        baseBranch,
        headSha,
        readyAt: wasTerminal ? (Number.isFinite(input.readyAt) ? input.readyAt : now()) : existing.readyAt,
        state: wasTerminal || headChanged ? (input.syncedBaseSha ? 'synced' : 'queued') : existing.state,
        syncedBaseSha: headChanged ? (input.syncedBaseSha ?? null) : (input.syncedBaseSha ?? existing.syncedBaseSha),
        attemptsByBase: wasTerminal ? {} : existing.attemptsByBase,
        ejectedAt: wasTerminal ? null : existing.ejectedAt,
        ejectedBaseSha: wasTerminal ? null : existing.ejectedBaseSha,
        ejectedHeadSha: wasTerminal ? null : existing.ejectedHeadSha,
        ejectReason: wasTerminal ? null : existing.ejectReason,
        lastError: wasTerminal || headChanged ? null : existing.lastError,
      });
    }
    byPr.set(pr, entry);
    const queue = writeMergeQueue(stateDir, [...byPr.values()], { fs, now });
    out = { entry: queue.items.find(i => i.pr === pr) ?? entry, queue };
  });
  if (lockRes?.locked) {
    const queue = readMergeQueue(stateDir, { fs });
    return { entry: queue.items.find(i => i.pr === pr) ?? null, queue, locked: true };
  }
  return out;
}

export function resolveGeneratedHeaderConflicts(content, { worktree, fs = nativeFs } = {}) {
  const raw = String(content ?? '');
  const crlf = raw.includes('\r\n');
  const lines = raw.replace(/\r\n/g, '\n').split('\n');
  const out = [], prompts = new Set();
  let sawConflict = false;

  for (let i = 0; i < lines.length; i++) {
    if (!lines[i].startsWith('<<<<<<< ')) {
      out.push(lines[i]);
      continue;
    }
    sawConflict = true;
    const sections = { ours: [], base: [], theirs: [] };
    let cur = 'ours', j = i + 1, foundSep = false, foundEnd = false;
    for (; j < lines.length; j++) {
      if (lines[j].startsWith('||||||| ')) { cur = 'base'; continue; }
      if (lines[j] === '=======') { cur = 'theirs'; foundSep = true; continue; }
      if (lines[j].startsWith('>>>>>>> ')) { foundEnd = true; break; }
      sections[cur].push(lines[j]);
    }
    if (!foundSep || !foundEnd || !sections.ours.length || !sections.theirs.length) {
      return { resolved: false, content: null, prompts: [] };
    }
    const allLines = [...sections.ours, ...sections.base, ...sections.theirs];
    let promptPath = null, templateMatch = null;
    for (const candidate of allLines) {
      const m = HEADER_LINE.exec(candidate);
      if (!m) return { resolved: false, content: null, prompts: [] };
      if (promptPath && m[2] !== promptPath) return { resolved: false, content: null, prompts: [] };
      promptPath = m[2];
      templateMatch ??= m;
    }
    if (!promptPath || !worktree) return { resolved: false, content: null, prompts: [] };
    const fullPrompt = join(worktree, promptPath);
    let promptBytes;
    try {
      promptBytes = fs.readFileSync(fullPrompt);
    } catch {
      return { resolved: false, content: null, prompts: [] };
    }
    const promptText = promptBytes.toString('utf8');
    if (hasGitConflictMarkers(promptText)) return { resolved: false, content: null, prompts: [] };
    const oursFirst = HEADER_LINE.exec(sections.ours[0]);
    if (oursFirst && oursFirst[3] === undefined && oursFirst[4] === undefined) {
      out.push(`${oursFirst[1]} ${promptPath}${oursFirst[5] || ''}`);
    } else {
      const expected = promptHeaderHash(promptBytes);
      const suffix = templateMatch[5] || '';
      const hashPart = templateMatch[4] !== undefined ? ` sha256=${expected}` : ` (sha256: ${expected})`;
      out.push(`${templateMatch[1]} ${promptPath}${hashPart}${suffix}`);
    }
    prompts.add(promptPath);
    i = j;
  }

  if (!sawConflict) return { resolved: false, content: null, prompts: [] };
  const joined = out.join(crlf ? '\r\n' : '\n');
  if (hasGitConflictMarkers(joined)) return { resolved: false, content: null, prompts: [] };
  return { resolved: true, content: joined, prompts: [...prompts] };
}

function listWorktreeFiles(rootDir, fs = nativeFs) {
  const out = [];
  const walk = relDir => {
    let entries = [];
    try { entries = fs.readdirSync(relDir ? join(rootDir, relDir) : rootDir, { withFileTypes: true }); } catch { return; }
    for (const ent of entries) {
      if (ent.name === '.git' || ent.name === 'node_modules') continue;
      const rel = relDir ? `${relDir}/${ent.name}` : ent.name;
      if (ent.isDirectory()) walk(rel);
      else if (ent.isFile()) out.push(rel);
    }
  };
  walk('');
  return out.sort();
}

export function refreshOwnedPromptHeaders({ worktree, touchedFiles = [], fs = nativeFs } = {}) {
  const touchedSet = new Set(
    (Array.isArray(touchedFiles) ? touchedFiles : [])
      .filter(p => typeof p === 'string' && p.trim())
      .map(p => p.replaceAll('\\', '/').replace(/^\.\/+/, '')),
  );
  if (!worktree || !touchedSet.size) return { refreshedFiles: [] };

  let ownerReport;
  try {
    const allFiles = listWorktreeFiles(worktree, fs);
    ownerReport = findOwners({ root: worktree, paths: allFiles });
  } catch {
    return { refreshedFiles: [] };
  }

  const refreshedFiles = [];
  for (const row of ownerReport.files ?? []) {
    if (!Array.isArray(row.headers) || !row.headers.length) continue;
    const relevant = touchedSet.has(row.path) || row.headers.some(h => touchedSet.has(h.prompt));
    if (!relevant) continue;
    const staleHeaders = row.headers.filter(h => h.state === 'stale' && typeof h.expected === 'string' && h.expected.length === 64);
    if (!staleHeaders.length) continue;

    const fullFile = join(worktree, row.path);
    let text;
    try { text = fs.readFileSync(fullFile, 'utf8'); } catch { continue; }
    if (hasGitConflictMarkers(text)) continue;

    const crlf = text.includes('\r\n');
    const lines = text.replace(/\r\n/g, '\n').split('\n');
    const staleByPrompt = new Map(staleHeaders.map(h => [h.prompt, h.expected]));
    let changed = false;
    for (let idx = 0; idx < Math.min(lines.length, 60); idx++) {
      const m = HEADER_LINE.exec(lines[idx]);
      if (!m) continue;
      const expected = staleByPrompt.get(m[2]);
      if (!expected) continue;
      const hashPart = m[4] !== undefined ? ` sha256=${expected}` : ` (sha256: ${expected})`;
      const updated = `${m[1]} ${m[2]}${hashPart}${m[5]}`;
      if (updated !== lines[idx]) {
        lines[idx] = updated;
        changed = true;
      }
    }
    if (changed) {
      fs.writeFileSync(fullFile, lines.join(crlf ? '\r\n' : '\n'));
      refreshedFiles.push(row.path);
    }
  }
  return { refreshedFiles: refreshedFiles.sort() };
}

export function discoverFocusedTestFiles(worktree, touchedFiles = [], { fs = nativeFs } = {}) {
  const directSet = new Set();
  const stems = new Set();
  for (const raw of Array.isArray(touchedFiles) ? touchedFiles : []) {
    if (typeof raw !== 'string' || !raw.trim()) continue;
    const rel = raw.replaceAll('\\', '/').replace(/^\.\/+/, '');
    if (/\.(?:test|spec)\.(?:mjs|js|cjs)$/i.test(rel)) {
      try { if (fs.statSync(join(worktree, rel)).isFile()) directSet.add(rel); } catch { /* Missing. */ }
      continue;
    }
    const base = posix.basename(rel)
      .replace(/\.prompt\.md$/i, '')
      .replace(/\.[a-z0-9]{1,8}$/i, '');
    if (base && base !== 'index') stems.add(base.toLowerCase());
  }

  for (const testDir of ['test', 'tests']) {
    let entries = [];
    try { entries = fs.readdirSync(join(worktree, testDir), { withFileTypes: true }); } catch { continue; }
    for (const ent of entries) {
      if (!ent.isFile() || !/\.(?:test|spec)\.(?:mjs|js|cjs)$/i.test(ent.name)) continue;
      if (/\.e2e\.test\./i.test(ent.name)) continue;
      const stem = ent.name
        .replace(/\.(?:vectors|formal)\.test\.[a-z0-9]+$/i, '')
        .replace(/\.(?:test|spec)\.[a-z0-9]+$/i, '')
        .toLowerCase();
      if (stems.has(stem)) directSet.add(`${testDir}/${ent.name}`);
    }
  }
  return [...directSet].sort();
}

function defaultVerifyOwners({ cwd, touchedFiles }) {
  const candidates = (Array.isArray(touchedFiles) ? touchedFiles : []).filter(Boolean);
  if (!candidates.length) return { ok: true };
  let report;
  try {
    const checkPaths = candidates.some(p => String(p).endsWith('.prompt.md'))
      ? listWorktreeFiles(cwd, nativeFs)
      : candidates;
    report = findOwners({ root: cwd, paths: checkPaths });
  } catch (err) {
    return { ok: false, reason: `pdd owner check failed: ${err.message}` };
  }
  const problems = [];
  for (const row of report.files ?? []) {
    if (isTestPromptPath(row.path)) problems.push(`${row.path} is a test prompt path`);
    if (isTestOwnedPath(row.path) && row.owners?.length) problems.push(`${row.path} cannot be owned by ${row.owners.join(', ')}`);
    if (String(row.note ?? '').includes('pdd-bindings.json could not be read')) problems.push('pdd-bindings.json could not be read');
    for (const h of row.headers ?? []) {
      if (h.state !== 'current' && h.state !== 'none') problems.push(`${row.path} has ${h.state} Generated from header for ${h.prompt}`);
    }
  }
  return problems.length ? { ok: false, reason: problems.join('; ') } : { ok: true };
}

function defaultRunFocusedTests({ cwd, testFiles }) {
  if (!Array.isArray(testFiles) || !testFiles.length) return Promise.resolve({ ok: true, ran: 0 });
  const { NODE_TEST_CONTEXT: _dropTestCtx, ...baseEnv } = process.env;
  return new Promise(resolvePromise => {
    execFileCb(process.execPath, ['--test', ...testFiles], {
      cwd,
      encoding: 'utf8',
      timeout: 120_000,
      maxBuffer: 16 * 1024 * 1024,
      env: { ...baseEnv, CI: 'true' },
    }, (error, stdout = '', stderr = '') => {
      if (!error) return resolvePromise({ ok: true, ran: testFiles.length });
      const summary = String(stderr || stdout || error.message).split(/\r?\n/).filter(Boolean).slice(-5).join(' | ');
      resolvePromise({ ok: false, ran: testFiles.length, reason: `focused tests failed (${testFiles.join(', ')}): ${summary}` });
    });
  });
}

function buildConflictResolutionPrompt({ pr, issue, branch, baseBranch, conflictFiles, conflictHunks, baseDiff, prDiff }) {
  return [
    `Resolve the Git rebase conflict for PR #${pr} (issue #${issue}, branch ${branch} onto origin/${baseBranch}).`,
    '',
    'Rules:',
    '- Edit ONLY the conflicted files in the current working directory to combine both changes cleanly.',
    '- Remove all Git conflict markers (<<<<<<<, |||||||, =======, >>>>>>>).',
    '- Do NOT run git rebase --continue, git commit, git push, or switch branches.',
    '',
    `Conflicted files: ${conflictFiles.join(', ')}`,
    '',
    'Conflict hunks:',
    String(conflictHunks ?? '').slice(0, 16_000),
    '',
    `Upstream diff (origin/${baseBranch}):`,
    String(baseDiff ?? '').slice(0, 16_000),
    '',
    `PR diff (${branch}):`,
    String(prDiff ?? '').slice(0, 16_000),
  ].join('\n');
}

async function fetchTrackingRef(git, cwd, branch) {
  const explicit = await git(['fetch', '-q', 'origin', `+refs/heads/${branch}:refs/remotes/origin/${branch}`], { cwd });
  if (explicit.code === 0) {
    const rev = await git(['rev-parse', '--verify', '-q', `refs/remotes/origin/${branch}`], { cwd });
    if (rev.code === 0 && rev.stdout.trim()) return rev.stdout.trim();
  }
  const fallback = await git(['fetch', '-q', 'origin', branch], { cwd });
  if (fallback.code !== 0) return null;
  for (const ref of [`refs/remotes/origin/${branch}`, `origin/${branch}`, 'FETCH_HEAD']) {
    const rev = await git(['rev-parse', '--verify', '-q', ref], { cwd });
    if (rev.code === 0 && rev.stdout.trim()) return rev.stdout.trim().split(/\s+/)[0];
  }
  return null;
}

async function continueOrSkipRebase(git, cwd) {
  const staged = await git(['diff', '--cached', '--name-only'], { cwd });
  const unstaged = await git(['diff', '--name-only'], { cwd });
  if (staged.code === 0 && !staged.stdout.trim() && unstaged.code === 0 && !unstaged.stdout.trim()) {
    return git(['rebase', '--skip'], { cwd });
  }
  return new Promise(resolvePromise => {
    // Pass GIT_EDITOR=true via -c core.editor=true so both custom git ports and native git skip interactive editors!
    git([...GIT_IDENTITY, '-c', 'core.editor=true', 'rebase', '--continue'], { cwd }).then(resolvePromise);
  });
}

async function rebaseAndVerifyHead({
  item,
  stateDir,
  repoRoot,
  baseBranch,
  baseTipSha,
  remoteBranchSha,
  agent,
  fs,
  git,
  runConflictAgent,
  execAgent,
  verifyOwners,
  runFocusedTests,
}) {
  if (!isAllowedMergeQueueBranch(item.branch, baseBranch)) {
    return { ok: false, stage: 'branch-guard', reason: `unsafe branch ${item.branch}` };
  }
  const wtRoot = join(resolve(stateDir), 'merge-queue-worktrees');
  const wt = join(wtRoot, `pr-${item.pr}`);
  fs.mkdirSync(wtRoot, { recursive: true, mode: 0o700 });

  const cleanupWt = async () => {
    await git(['rebase', '--abort'], { cwd: wt }).catch(() => {});
    await git(['worktree', 'remove', '--force', wt], { cwd: repoRoot }).catch(() => {});
    try { fs.rmSync(wt, { recursive: true, force: true }); } catch { /* Best effort. */ }
    await git(['worktree', 'prune'], { cwd: repoRoot }).catch(() => {});
  };

  await cleanupWt();
  const added = await git(['worktree', 'add', '-q', '--detach', wt, remoteBranchSha], { cwd: repoRoot });
  if (added.code !== 0) {
    await cleanupWt();
    return { ok: false, stage: 'worktree', reason: `could not create isolated rebase worktree for ${item.branch}` };
  }

  try {
    const mbOut = await git(['merge-base', baseTipSha, remoteBranchSha], { cwd: wt });
    const mergeBaseSha = mbOut.code === 0 && mbOut.stdout.trim() ? mbOut.stdout.trim() : baseTipSha;
    const prOrigFiles = (await git(['diff', '--name-only', `${mergeBaseSha}..${remoteBranchSha}`], { cwd: wt })).stdout.split(/\r?\n/).filter(Boolean);
    const baseDiff = (await git(['diff', `${mergeBaseSha}..${baseTipSha}`], { cwd: wt })).stdout;
    const prDiff = (await git(['diff', `${mergeBaseSha}..${remoteBranchSha}`], { cwd: wt })).stdout;

    let rebaseRes = await git([...GIT_IDENTITY, '-c', 'core.editor=true', 'rebase', baseTipSha], { cwd: wt });
    let agentPassesUsed = 0;
    let steps = 0;

    while (rebaseRes.code !== 0) {
      if (++steps > 24) {
        await git(['rebase', '--abort'], { cwd: wt });
        return { ok: false, stage: 'rebase', reason: `rebase exceeded step limit on ${item.branch}` };
      }
      const unmergedOut = await git(['diff', '--name-only', '--diff-filter=U'], { cwd: wt });
      const conflictFiles = unmergedOut.stdout.split(/\r?\n/).map(s => s.trim()).filter(Boolean);
      if (!conflictFiles.length) {
        await git(['rebase', '--abort'], { cwd: wt });
        const detail = String(rebaseRes.stderr || rebaseRes.stdout || '').trim().slice(0, 200);
        return { ok: false, stage: 'rebase', reason: `git rebase failed on ${item.branch}${detail ? `: ${detail}` : ''}` };
      }

      // 1. Zero-AI automatic PDD Generated-from header conflict resolution when every conflict block is header-only.
      const resolvedHeaders = new Map();
      let allHeaderOnly = true;
      for (const rel of conflictFiles) {
        let rawText;
        try { rawText = fs.readFileSync(join(wt, rel), 'utf8'); } catch { allHeaderOnly = false; break; }
        const attempt = resolveGeneratedHeaderConflicts(rawText, { worktree: wt, fs });
        if (!attempt.resolved) { allHeaderOnly = false; break; }
        resolvedHeaders.set(rel, attempt.content);
      }

      if (allHeaderOnly && resolvedHeaders.size === conflictFiles.length) {
        for (const [rel, content] of resolvedHeaders) fs.writeFileSync(join(wt, rel), content);
        await git(['add', '--', ...conflictFiles], { cwd: wt });
        rebaseRes = await continueOrSkipRebase(git, wt);
        continue;
      }

      // 2. Bounded 1-pass conflict-resolution agent for real conflict markers.
      if (agentPassesUsed >= 1) {
        await git(['rebase', '--abort'], { cwd: wt });
        return { ok: false, stage: 'conflict', reason: `unresolved rebase conflict in ${conflictFiles.join(', ')}` };
      }
      agentPassesUsed++;

      const conflictHunks = conflictFiles.map(rel => {
        try { return `--- ${rel} ---\n${fs.readFileSync(join(wt, rel), 'utf8').slice(0, 8000)}`; }
        catch { return `--- ${rel} (unreadable) ---`; }
      }).join('\n\n');
      const prompt = buildConflictResolutionPrompt({
        pr: item.pr,
        issue: item.issue,
        branch: item.branch,
        baseBranch,
        conflictFiles,
        conflictHunks,
        baseDiff,
        prDiff,
      });

      let invocation = null;
      if (agent?.kind) {
        try { invocation = buildConflictAgentInvocation(agent); }
        catch (err) {
          await git(['rebase', '--abort'], { cwd: wt });
          return { ok: false, stage: 'conflict', reason: err.message };
        }
      }

      let agentOut = null;
      try {
        if (runConflictAgent) {
          agentOut = await runConflictAgent({
            cwd: wt,
            pr: item.pr,
            issue: item.issue,
            branch: item.branch,
            baseBranch,
            conflictFiles,
            conflictHunks,
            baseDiff,
            prDiff,
            prompt,
            agent,
            invocation,
          });
        } else if (invocation) {
          const execRes = await execAgent({ command: invocation.command, args: invocation.args, input: prompt, cwd: wt });
          agentOut = { resolved: execRes.code === 0, code: execRes.code };
        } else {
          await git(['rebase', '--abort'], { cwd: wt });
          return { ok: false, stage: 'conflict', reason: `rebase conflict in ${conflictFiles.join(', ')} (no conflict agent configured)` };
        }
      } catch (err) {
        await git(['rebase', '--abort'], { cwd: wt });
        return { ok: false, stage: 'conflict', reason: `conflict agent error in ${conflictFiles.join(', ')}: ${err.message}` };
      }

      if (agentOut?.resolved === false) {
        await git(['rebase', '--abort'], { cwd: wt });
        return { ok: false, stage: 'conflict', reason: `conflict agent declined conflict in ${conflictFiles.join(', ')}` };
      }

      for (const rel of conflictFiles) {
        let text = '';
        try { text = fs.readFileSync(join(wt, rel), 'utf8'); } catch { /* Deleted file allowed if staged cleanly. */ }
        if (hasGitConflictMarkers(text)) {
          await git(['rebase', '--abort'], { cwd: wt });
          return { ok: false, stage: 'conflict', reason: `conflict markers remain in ${rel}` };
        }
      }

      refreshOwnedPromptHeaders({ worktree: wt, touchedFiles: [...prOrigFiles, ...conflictFiles], fs });
      await git(['add', '-A', '--', ...conflictFiles], { cwd: wt });
      const stillUnmerged = (await git(['diff', '--name-only', '--diff-filter=U'], { cwd: wt })).stdout.trim();
      if (stillUnmerged) {
        await git(['rebase', '--abort'], { cwd: wt });
        return { ok: false, stage: 'conflict', reason: `unmerged index entries remain in ${conflictFiles.join(', ')}` };
      }
      rebaseRes = await continueOrSkipRebase(git, wt);
    }

    // 3. Post-rebase PDD header-hash drift sweep (0 AI calls) when both prompt & owned module merged cleanly.
    const rebasedDiffFiles = (await git(['diff', '--name-only', `${baseTipSha}..HEAD`], { cwd: wt })).stdout.split(/\r?\n/).filter(Boolean);
    const prScope = [...new Set([...prOrigFiles, ...rebasedDiffFiles])];
    const { refreshedFiles } = refreshOwnedPromptHeaders({ worktree: wt, touchedFiles: prScope, fs });
    if (refreshedFiles.length > 0) {
      await git(['add', '--', ...refreshedFiles], { cwd: wt });
      const staged = (await git(['diff', '--cached', '--name-only'], { cwd: wt })).stdout.trim();
      if (staged) {
        const curHead = (await git(['rev-parse', 'HEAD'], { cwd: wt })).stdout.trim();
        const commitArgs = curHead && curHead !== baseTipSha
          ? [...GIT_IDENTITY, 'commit', '-q', '--amend', '--no-edit']
          : [...GIT_IDENTITY, 'commit', '-q', '-m', 'chore: refresh generated prompt header'];
        const amendRes = await git(commitArgs, { cwd: wt });
        if (amendRes.code !== 0) {
          return { ok: false, stage: 'header-refresh', reason: 'could not record refreshed prompt header' };
        }
      }
    }

    // 4. Post-rebase verification: pdd owner + focused tests BEFORE push.
    const finalTouched = (await git(['diff', '--name-only', `${baseTipSha}..HEAD`], { cwd: wt })).stdout.split(/\r?\n/).filter(Boolean);
    for (const rel of finalTouched) {
      try {
        const text = fs.readFileSync(join(wt, rel), 'utf8');
        if (hasGitConflictMarkers(text)) {
          return { ok: false, stage: 'verify', reason: `conflict markers detected in ${rel}` };
        }
      } catch { /* Deleted file. */ }
    }

    const ownerVerdict = await verifyOwners({ cwd: wt, touchedFiles: finalTouched, pr: item.pr, issue: item.issue });
    if (!ownerVerdict?.ok) {
      return { ok: false, stage: 'owner', reason: ownerVerdict?.reason || 'pdd owner verification failed after rebase' };
    }

    const testFiles = discoverFocusedTestFiles(wt, finalTouched, { fs });
    const testVerdict = await runFocusedTests({ cwd: wt, touchedFiles: finalTouched, testFiles, pr: item.pr, issue: item.issue });
    if (!testVerdict?.ok) {
      return { ok: false, stage: 'tests', reason: testVerdict?.reason || 'focused post-rebase tests failed' };
    }

    // 5. Safe push strictly with --force-with-lease on the pdd/core-* branch (never main, never plain --force).
    if (!isAllowedMergeQueueBranch(item.branch, baseBranch)) {
      return { ok: false, stage: 'branch-guard', reason: `unsafe push target ${item.branch}` };
    }
    const newHeadSha = (await git(['rev-parse', 'HEAD'], { cwd: wt })).stdout.trim();
    if (newHeadSha !== remoteBranchSha) {
      const pushRes = await git([
        'push',
        '-q',
        `--force-with-lease=refs/heads/${item.branch}:${remoteBranchSha}`,
        'origin',
        `HEAD:refs/heads/${item.branch}`,
      ], { cwd: wt });
      if (pushRes.code !== 0) {
        return { ok: false, stage: 'push', reason: `force-with-lease push rejected for ${item.branch}` };
      }
    }

    return {
      ok: true,
      headSha: newHeadSha,
      agentUsed: agentPassesUsed > 0,
      refreshedFiles,
      testFiles,
    };
  } finally {
    await cleanupWt();
  }
}

export async function processMergeQueue(input, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = ports.now ?? Date.now;
  const warn = ports.warn ?? (() => {});
  const git = ports.git ?? defaultGitPort;
  const getPullRequest = ports.getPullRequest ?? null;
  const mergePullRequest = ports.mergePullRequest ?? null;
  const runConflictAgent = ports.runConflictAgent ?? null;
  const execAgent = ports.execAgent ?? defaultExecAgent;
  const verifyOwners = ports.verifyOwners ?? defaultVerifyOwners;
  const runFocusedTests = ports.runFocusedTests ?? defaultRunFocusedTests;
  const commentOnPr = ports.commentOnPr ?? null;
  const onEject = ports.onEject ?? null;

  const stateDir = resolve(input.stateDir);
  const repoRoot = resolve(input.repoRoot);
  const baseBranch = typeof input.baseBranch === 'string' && input.baseBranch.trim() ? input.baseBranch.trim() : 'main';
  const mode = input.mode === 'observe' ? 'observe' : 'auto';
  const agent = input.agent ?? null;
  const maxItems = Number.isFinite(input.maxItems) && input.maxItems > 0 ? input.maxItems : Infinity;
  const maxAttemptsPerCall = Number.isSafeInteger(input.maxAttemptsPerCall) && input.maxAttemptsPerCall >= 1
    ? Math.min(input.maxAttemptsPerCall, MAX_ATTEMPTS_PER_BASE)
    : 1;

  const merged = [], synced = [], ejected = [], retried = [];
  let processed = 0;

  const lockRes = await withMergeQueueLock(stateDir, { fs, now }, async () => {
    let current = readMergeQueue(stateDir, { fs });
    const hasWork = current.items.some(i => ['queued', 'processing', 'synced'].includes(i.state));
    if (!hasWork) return;

    let baseTipSha = await fetchTrackingRef(git, repoRoot, baseBranch);
    if (!baseTipSha) {
      warn(`Autopilot merge queue could not fetch origin/${baseBranch}`);
      return;
    }

    const byPr = new Map(current.items.map(i => [i.pr, i]));
    const save = () => {
      current = writeMergeQueue(stateDir, [...byPr.values()], { fs, now });
      return current;
    };

    const deferred = new Set();
    const attemptsThisCall = new Map();

    const recordFailureAndMaybeEject = async (item, remoteBranchSha, rawReason) => {
      const prev = Number.isSafeInteger(item.attemptsByBase?.[baseTipSha]) ? item.attemptsByBase[baseTipSha] : 0;
      const count = prev + 1;
      item.attemptsByBase = { ...(item.attemptsByBase ?? {}), [baseTipSha]: count };
      const cleanReason = sanitizePublicQueueNote(rawReason || 'rebase verification failed');
      item.lastError = cleanReason;

      if (count >= MAX_ATTEMPTS_PER_BASE) {
        item.state = 'ejected';
        item.ejectedAt = now();
        item.ejectedBaseSha = baseTipSha;
        item.ejectedHeadSha = remoteBranchSha || item.headSha;
        item.ejectReason = cleanReason;
        save();
        ejected.push(item.pr);
        processed++;
        const message = sanitizePublicQueueNote(
          `Autopilot removed PR #${item.pr} from the landing queue after ${count} failed rebase verification attempts against ${baseBranch} (${cleanReason}). Resolve the conflict on ${item.branch} and push a new commit to re-queue it.`,
        );
        if (commentOnPr) {
          try { await commentOnPr(item.pr, message); } catch (err) { warn(`Autopilot merge queue comment failed on PR #${item.pr}: ${err.message}`); }
        }
        if (onEject) {
          try { await onEject({ entry: { ...item }, reason: cleanReason, message }); } catch (err) { warn(`Autopilot merge queue onEject failed on PR #${item.pr}: ${err.message}`); }
        }
        return 'ejected-advance';
      }

      const used = (attemptsThisCall.get(item.pr) ?? 0) + 1;
      attemptsThisCall.set(item.pr, used);
      item.state = 'queued';
      save();
      if (used < maxAttemptsPerCall) return 'retry-now';
      retried.push(item.pr);
      return 'hold-head';
    };

    while (processed < maxItems) {
      const ordered = sortFifo([...byPr.values()]);
      let head = null;
      for (const candidate of ordered) {
        if (deferred.has(candidate.pr)) continue;
        if (!['queued', 'processing', 'synced'].includes(candidate.state)) continue;
        if (mode === 'observe' && candidate.state === 'synced' && candidate.syncedBaseSha === baseTipSha && !input.recheckSynced) {
          deferred.add(candidate.pr);
          continue;
        }
        if (mode === 'observe' && candidate.state === 'synced' && candidate.syncedBaseSha === baseTipSha && input.recheckSynced) {
          if (!getPullRequest) { deferred.add(candidate.pr); continue; }
          const snap = await getPullRequest(candidate.pr).catch(() => null);
          if (snap?.merged) {
            candidate.state = 'merged'; candidate.mergedAt = now(); candidate.lastError = null; save();
            merged.push(candidate.pr); processed++;
            baseTipSha = (await fetchTrackingRef(git, repoRoot, baseBranch)) ?? baseTipSha;
            head = 'reloop';
            break;
          }
          if (snap && snap.state && snap.state !== 'open') {
            candidate.state = 'closed'; save(); processed++;
            head = 'reloop';
            break;
          }
          const conflicting = snap?.mergeable === false
            || snap?.mergeable === 'CONFLICTING'
            || ['CONFLICTING', 'DIRTY'].includes(String(snap?.mergeStateStatus ?? '').toUpperCase());
          const externalMove = snap?.headSha && snap.headSha !== candidate.headSha;
          if (!conflicting && !externalMove) { deferred.add(candidate.pr); continue; }
        }
        head = candidate;
        break;
      }

      if (head === 'reloop') continue;
      if (!head) break;

      const prInfo = getPullRequest ? await getPullRequest(head.pr).catch(() => null) : null;
      if (prInfo?.merged) {
        head.state = 'merged'; head.mergedAt = now(); head.lastError = null; save();
        merged.push(head.pr); processed++;
        baseTipSha = (await fetchTrackingRef(git, repoRoot, baseBranch)) ?? baseTipSha;
        continue;
      }
      if (prInfo && prInfo.state && prInfo.state !== 'open') {
        head.state = 'closed'; save(); processed++;
        continue;
      }
      if (typeof prInfo?.branch === 'string' && prInfo.branch.trim()) head.branch = prInfo.branch.trim();

      if (!isAllowedMergeQueueBranch(head.branch, baseBranch)) {
        head.state = 'ejected';
        head.ejectedAt = now();
        head.ejectedBaseSha = baseTipSha;
        head.ejectedHeadSha = head.headSha;
        head.ejectReason = 'refused non-Autopilot or protected branch';
        save();
        ejected.push(head.pr);
        processed++;
        continue;
      }

      head.state = 'processing';
      save();

      const remoteBranchSha = await fetchTrackingRef(git, repoRoot, head.branch);
      if (!remoteBranchSha) {
        const recheck = getPullRequest ? await getPullRequest(head.pr).catch(() => null) : null;
        if (recheck?.merged) {
          head.state = 'merged'; head.mergedAt = now(); save();
          merged.push(head.pr);
        } else {
          head.state = 'closed'; save();
        }
        processed++;
        continue;
      }
      head.headSha = remoteBranchSha;

      const ancestorCheck = await git(['merge-base', '--is-ancestor', baseTipSha, remoteBranchSha], { cwd: repoRoot });
      const ghConflicting = prInfo?.mergeable === false
        || prInfo?.mergeable === 'CONFLICTING'
        || ['CONFLICTING', 'DIRTY'].includes(String(prInfo?.mergeStateStatus ?? '').toUpperCase());
      const upToDateAndClean = ancestorCheck.code === 0 && !ghConflicting;

      if (upToDateAndClean) {
        if (mode === 'observe') {
          head.state = 'synced';
          head.syncedBaseSha = baseTipSha;
          head.lastError = null;
          save();
          synced.push(head.pr);
          deferred.add(head.pr);
          processed++;
          continue;
        }

        if (!mergePullRequest) {
          head.state = 'synced';
          head.syncedBaseSha = baseTipSha;
          save();
          synced.push(head.pr);
          break;
        }
        const mergeOut = await mergePullRequest({
          pr: head.pr,
          issue: head.issue,
          issues: head.issues,
          branch: head.branch,
          baseBranch,
          headSha: remoteBranchSha,
          rebased: false,
        });
        if (mergeOut?.merged) {
          head.state = 'merged';
          head.mergedAt = now();
          head.syncedBaseSha = baseTipSha;
          head.lastError = null;
          save();
          merged.push(head.pr);
          processed++;
          baseTipSha = (await fetchTrackingRef(git, repoRoot, baseBranch)) || mergeOut.baseTipSha || baseTipSha;
          continue;
        }
        if (mergeOut?.pendingCi) {
          head.state = 'synced';
          head.syncedBaseSha = baseTipSha;
          head.lastError = null;
          save();
          synced.push(head.pr);
          break;
        }
        const action = await recordFailureAndMaybeEject(head, remoteBranchSha, mergeOut?.error || 'merge pull request failed');
        if (action === 'ejected-advance' || action === 'retry-now') continue;
        break;
      }

      // Base moved ahead or GitHub reported conflict -> rebase, auto-refresh PDD headers, verify, and push.
      const rebaseOut = await rebaseAndVerifyHead({
        item: head,
        stateDir,
        repoRoot,
        baseBranch,
        baseTipSha,
        remoteBranchSha,
        agent,
        fs,
        git,
        runConflictAgent,
        execAgent,
        verifyOwners,
        runFocusedTests,
      });

      if (!rebaseOut.ok) {
        const action = await recordFailureAndMaybeEject(head, remoteBranchSha, rebaseOut.reason);
        if (action === 'ejected-advance' || action === 'retry-now') continue;
        break;
      }

      head.headSha = rebaseOut.headSha;
      head.syncedBaseSha = baseTipSha;
      head.lastError = null;

      if (mode === 'observe') {
        head.state = 'synced';
        save();
        synced.push(head.pr);
        deferred.add(head.pr);
        processed++;
        continue;
      }

      if (!mergePullRequest) {
        head.state = 'synced';
        save();
        synced.push(head.pr);
        break;
      }
      const mergeOut = await mergePullRequest({
        pr: head.pr,
        issue: head.issue,
        issues: head.issues,
        branch: head.branch,
        baseBranch,
        headSha: rebaseOut.headSha,
        rebased: true,
      });
      if (mergeOut?.merged) {
        head.state = 'merged';
        head.mergedAt = now();
        save();
        merged.push(head.pr);
        processed++;
        baseTipSha = (await fetchTrackingRef(git, repoRoot, baseBranch)) || mergeOut.baseTipSha || baseTipSha;
        continue;
      }
      if (mergeOut?.pendingCi) {
        head.state = 'synced';
        save();
        synced.push(head.pr);
        break;
      }
      const action = await recordFailureAndMaybeEject(head, rebaseOut.headSha, mergeOut?.error || 'merge pull request failed after rebase');
      if (action === 'ejected-advance' || action === 'retry-now') continue;
      break;
    }
  });

  const queue = readMergeQueue(stateDir, { fs });
  return {
    locked: Boolean(lockRes?.locked),
    processed,
    merged,
    synced,
    ejected,
    retried,
    queue,
  };
}

export function mergeQueueStatusLine(stateDir, ports = {}) {
  const queue = readMergeQueue(stateDir, ports);
  const queued = queue.items.filter(i => i.state === 'queued' || i.state === 'processing');
  const synced = queue.items.filter(i => i.state === 'synced');
  const ejected = queue.items.filter(i => i.state === 'ejected');
  if (!queued.length && !synced.length && !ejected.length) return '';
  const parts = [];
  if (queued.length) parts.push(`${queued.length} queued (${queued.map(i => `PR #${i.pr}`).join(', ')})`);
  if (synced.length) parts.push(`${synced.length} synced`);
  if (ejected.length) parts.push(`${ejected.length} ejected (${ejected.map(i => `PR #${i.pr}`).join(', ')})`);
  return `Merge queue: ${parts.join('; ')}.`;
}
