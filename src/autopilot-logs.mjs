// Generated from prompts/cli/autopilot-logs.prompt.md (sha256: 8b345c3f03e51f5c556ed65221ba2fe82d41490371f48304181f244a439d7588).
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { basename, join, resolve } from 'node:path';
import { createHash } from 'node:crypto';
import { execFile, spawnSync } from 'node:child_process';
import { promisify } from 'node:util';
import { readSuiteProgress } from './test-suite-queue.mjs';
import { redactSecrets } from './secret-redaction.mjs';

const execute = promisify(execFile);
const ANSI_RE = /\x1b\[[0-?]*[ -/]*[@-~]|\x1b\][^\x07]*(?:\x07|\x1b\\)/g;
const CTRL_RE = /[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]/g;
const DEFAULT_LINES = 40;
const MAX_LINES = 5000;
const DEFAULT_POLL_MS = 250;
const MAX_CMD_PREVIEW_LINES = 6;
const READ_CHUNK_LIMIT = 512 * 1024;

const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const named = value => typeof value === 'string' && value.trim().length > 0;

function cleanText(value, maxLen = 400) {
  const sanitized = redactSecrets(String(value ?? '').replace(ANSI_RE, '').replace(/\r\n/g, '\n').replace(/\r/g, '\n').replace(CTRL_RE, ''));
  return sanitized.length > maxLen ? `${sanitized.slice(0, maxLen - 3)}...` : sanitized;
}

function oneLine(value, maxLen = 200) {
  return cleanText(value, maxLen * 2).replace(/\s+/g, ' ').trim().slice(0, maxLen);
}

function shortSha(sha) {
  return typeof sha === 'string' && sha.trim() ? sha.trim().slice(0, 8) : 'unknown';
}

function formatAge(nowMs, atMs) {
  if (!Number.isFinite(atMs) || atMs <= 0) return 'unknown';
  const diffSec = Math.max(0, Math.round((nowMs - atMs) / 1000));
  if (diffSec < 60) return `${diffSec}s ago`;
  const diffMin = Math.floor(diffSec / 60);
  if (diffMin < 60) return `${diffMin}m ago`;
  const hours = Math.floor(diffMin / 60);
  const mins = diffMin % 60;
  return mins > 0 ? `${hours}h ${mins}m ago` : `${hours}h ago`;
}

function formatStamp(nowMs, atMs) {
  if (!Number.isFinite(atMs) || atMs <= 0) return 'unknown';
  return `${formatAge(nowMs, atMs)} (${new Date(atMs).toISOString()})`;
}

function readJson(fs, filePath, fallback = null) {
  if (typeof filePath !== 'string' || !filePath) return fallback;
  try {
    const parsed = JSON.parse(fs.readFileSync(filePath, 'utf8'));
    return parsed ?? fallback;
  } catch {
    return fallback;
  }
}

function statInfo(fs, filePath) {
  if (typeof filePath !== 'string' || !filePath) return null;
  try {
    const st = fs.statSync(filePath);
    return st.isFile() ? { size: st.size, mtimeMs: st.mtimeMs } : null;
  } catch {
    return null;
  }
}

function listDir(fs, dirPath) {
  try { return fs.readdirSync(dirPath); } catch { return []; }
}

function defaultIsProcessAlive(pid, token) {
  if (!Number.isSafeInteger(pid) || pid <= 0) return false;
  try { process.kill(pid, 0); } catch (error) { if (error?.code !== 'EPERM') return false; }
  if (!named(token)) return true;
  const row = spawnSync('ps', ['-ww', '-o', 'command=', '-p', String(pid)], {
    encoding: 'utf8',
    timeout: 3000,
    maxBuffer: 4 * 1024 * 1024,
    env: { ...process.env, LC_ALL: 'C', LANG: 'C' },
  });
  return row.status === 0 && String(row.stdout ?? '').includes(token);
}

async function defaultGit(args, { cwd, env }) {
  try {
    const out = await execute('git', args, {
      cwd,
      encoding: 'utf8',
      env: { ...env, LC_ALL: 'C', LANG: 'C' },
    });
    return { code: 0, stdout: String(out.stdout ?? ''), stderr: String(out.stderr ?? '') };
  } catch (error) {
    return {
      code: Number.isInteger(error?.code) ? error.code : 1,
      stdout: String(error?.stdout ?? ''),
      stderr: String(error?.stderr ?? error?.message ?? ''),
    };
  }
}

export function parseIssueSelector(raw) {
  if (raw === undefined || raw === null) return { ok: true, issue: null, repo: null };
  const text = String(raw).trim().replace(/\/$/, '');
  if (!text) return { ok: false, issue: null, repo: null };
  const plain = /^#?([1-9][0-9]*)$/.exec(text);
  if (plain) return { ok: true, issue: Number(plain[1]), repo: null };
  const qualified = /^([A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+)#([1-9][0-9]*)$/.exec(text);
  if (qualified) return { ok: true, issue: Number(qualified[2]), repo: qualified[1] };
  const url = /^https:\/\/github\.com\/([A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+)\/issues\/([1-9][0-9]*)$/.exec(text);
  if (url) return { ok: true, issue: Number(url[2]), repo: url[1] };
  return { ok: false, issue: null, repo: null };
}

function previewCommandOutput(output) {
  if (!named(output)) return [];
  const rawLines = cleanText(output, 4000)
    .split('\n')
    .map(line => line.trimEnd())
    .filter(line => line.trim().length > 0);
  if (!rawLines.length) return [];
  const tail = rawLines.slice(-MAX_CMD_PREVIEW_LINES);
  const omitted = rawLines.length - tail.length;
  return [
    ...(omitted > 0 ? [`  | ... (${omitted} earlier line${omitted === 1 ? '' : 's'})`] : []),
    ...tail.map(line => `  | ${line.length > 180 ? `${line.slice(0, 177)}...` : line}`),
  ];
}

export function formatWorkerLogLine(rawLine) {
  if (typeof rawLine !== 'string') return '';
  const stripped = rawLine.replace(ANSI_RE, '').replace(/\r/g, '');
  const trimmed = stripped.trim();
  if (!trimmed) return '';
  if (!trimmed.startsWith('{') || !trimmed.endsWith('}')) {
    return cleanText(stripped, 500);
  }
  let event;
  try { event = JSON.parse(trimmed); } catch { return cleanText(stripped, 500); }
  if (!isObject(event)) return cleanText(stripped, 500);

  // Skip noisy token-count and delta heartbeats.
  if (event.type === 'token_count' || (event.type === 'event_msg' && event.payload?.type === 'token_count')) return '';
  if (event.type === 'content_block_delta' || event.type === 'message_delta' || event.type === 'message_stop' || event.type === 'ping') return '';

  // Codex thread/turn lifecycle
  if (event.type === 'thread.started' || event.type === 'session_meta') {
    const model = event.model ?? event.payload?.model;
    return `[session] started${named(model) ? ` (${oneLine(model, 80)})` : ''}`;
  }
  if (event.type === 'turn.started' || event.type === 'message_start') return '';
  if (event.type === 'turn.completed') {
    const u = isObject(event.usage) ? event.usage : null;
    return u && (Number.isFinite(u.input_tokens) || Number.isFinite(u.output_tokens))
      ? `[turn] completed (in ${u.input_tokens ?? 0}, out ${u.output_tokens ?? 0} tokens)`
      : '[turn] completed';
  }
  if (event.type === 'turn.failed' || event.type === 'error') {
    const msg = event.error?.message ?? event.message ?? JSON.stringify(event);
    return `[error] ${oneLine(msg, 240)}`;
  }

  // Codex item.started / item.completed
  if ((event.type === 'item.started' || event.type === 'item.completed') && isObject(event.item)) {
    const item = event.item;
    const itemType = String(item.type ?? item.item_type ?? '');
    const cmd = item.command ?? item.arguments?.command;
    if (event.type === 'item.started') {
      if (itemType === 'command_execution' && named(cmd)) return `[run] $ ${oneLine(cmd, 180)}`;
      if (named(item.tool ?? item.name)) return `[tool] ${oneLine(item.tool ?? item.name, 80)} started`;
      return '';
    }
    if (itemType === 'agent_message' && named(item.text)) {
      return cleanText(item.text, 800)
        .split('\n')
        .filter(line => line.trim())
        .map(line => `[agent] ${line}`)
        .join('\n');
    }
    if (itemType === 'reasoning') {
      return named(item.text) ? `[think] ${oneLine(item.text, 160)}` : '';
    }
    if (itemType === 'command_execution') {
      const code = Number.isInteger(item.exit_code) ? item.exit_code : 0;
      const head = `[cmd exit=${code}] $ ${oneLine(cmd ?? '(command)', 170)}`;
      return [head, ...previewCommandOutput(item.aggregated_output ?? item.output)].join('\n');
    }
    if (itemType === 'file_change' || itemType === 'patch') {
      const paths = Array.isArray(item.changes)
        ? item.changes.map(c => c?.path).filter(named).join(', ')
        : (item.path ?? '');
      return `[edit] ${oneLine(paths || 'updated files', 180)}`;
    }
    const toolName = item.tool ?? item.name ?? (itemType || 'item');
    return `[tool] ${oneLine(toolName, 120)}`;
  }

  // Claude stream-json events
  if (event.type === 'system' && event.subtype === 'init') {
    return `[session] started${named(event.model) ? ` (${oneLine(event.model, 80)})` : ''}`;
  }
  if (event.type === 'assistant' && isObject(event.message)) {
    const parts = Array.isArray(event.message.content) ? event.message.content : [];
    const out = [];
    for (const part of parts) {
      if (part?.type === 'text' && named(part.text)) {
        for (const l of cleanText(part.text, 800).split('\n').filter(s => s.trim())) out.push(`[agent] ${l}`);
      } else if (part?.type === 'tool_use' && named(part.name)) {
        const detail = part.input?.command ?? part.input?.file_path ?? part.input?.path ?? part.input?.pattern ?? '';
        out.push(`[tool] ${oneLine(part.name, 60)}${named(detail) ? `: ${oneLine(detail, 150)}` : ''}`);
      }
    }
    return out.join('\n');
  }
  if (event.type === 'user' && isObject(event.message)) {
    const parts = Array.isArray(event.message.content) ? event.message.content : [];
    const out = [];
    for (const part of parts) {
      if (part?.type === 'tool_result') {
        const raw = typeof part.content === 'string'
          ? part.content
          : Array.isArray(part.content)
            ? part.content.map(c => c?.text ?? '').join('\n')
            : '';
        if (part.is_error) out.push(`[tool error] ${oneLine(raw || 'command failed', 200)}`);
        else out.push(...previewCommandOutput(raw));
      }
    }
    return out.join('\n');
  }
  if (event.type === 'result') {
    const status = event.subtype ?? (event.is_error ? 'error' : 'done');
    return `[result] ${oneLine(status, 40)}${named(event.result) ? `: ${oneLine(event.result, 180)}` : ''}`;
  }

  // Gemini / Agy stream-json events
  if (event.event === 'step_update' && isObject(event.step_update)) {
    const step = event.step_update;
    if (step.step_type === 'tool' && named(step.tool_name)) {
      const cmd = step.tool_info?.parameters?.command ?? step.tool_info?.parameters?.CommandLine ?? '';
      const head = `[tool] ${oneLine(step.tool_name, 60)}${named(cmd) ? `: ${oneLine(cmd, 150)}` : ''} (${oneLine(step.state ?? 'update', 20)})`;
      return step.state === 'DONE' ? [head, ...previewCommandOutput(step.tool_info?.output)].join('\n') : head;
    }
    return '';
  }
  if (event.type === 'tool_use' && named(event.tool_name)) {
    const cmd = event.parameters?.command ?? event.parameters?.cmd ?? event.parameters?.path ?? event.parameters?.file_path ?? '';
    return `[tool] ${oneLine(event.tool_name, 60)}${named(cmd) ? `: ${oneLine(cmd, 150)}` : ''}`;
  }
  if (event.type === 'tool_result') {
    const raw = typeof event.output === 'string' ? event.output : JSON.stringify(event.output ?? '');
    return previewCommandOutput(raw).join('\n');
  }
  if (event.type === 'message' && named(event.content)) {
    const prefix = event.role === 'assistant' ? '[agent]' : `[${oneLine(event.role ?? 'msg', 20)}]`;
    return cleanText(event.content, 800).split('\n').filter(s => s.trim()).map(l => `${prefix} ${l}`).join('\n');
  }

  if (named(event.type)) return `[event] ${oneLine(event.type, 80)}`;
  return '';
}

function formatLogTail(fs, filePath, maxLines) {
  if (!filePath) return [];
  let raw;
  try {
    const st = fs.statSync(filePath);
    if (!st.isFile() || st.size <= 0) return [];
    const readSize = Math.min(st.size, Math.max(64 * 1024, maxLines * 2048));
    const start = Math.max(0, st.size - readSize);
    const fd = fs.openSync(filePath, 'r');
    try {
      const buf = Buffer.alloc(readSize);
      const bytes = fs.readSync(fd, buf, 0, readSize, start);
      raw = buf.subarray(0, bytes).toString('utf8');
      if (start > 0) {
        const nl = raw.indexOf('\n');
        if (nl >= 0) raw = raw.slice(nl + 1);
      }
    } finally {
      try { fs.closeSync(fd); } catch {}
    }
  } catch {
    return [];
  }
  const formatted = [];
  for (const rawLine of raw.split('\n')) {
    const rendered = formatWorkerLogLine(rawLine);
    if (!rendered) continue;
    for (const line of rendered.split('\n')) {
      if (line.trim()) formatted.push(line);
    }
  }
  return formatted.slice(-maxLines);
}

function validExitRecord(value) {
  return isObject(value)
    && (Number.isSafeInteger(value.code) || value.code === null)
    && (value.signal === null || typeof value.signal === 'string')
    && Number.isFinite(value.at);
}

function inspectPart(part, role, { fs, isProcessAlive }) {
  if (!isObject(part)) return null;
  const exitRecord = typeof part.exit === 'string' ? readJson(fs, part.exit, null) : null;
  const hasExit = validExitRecord(exitRecord);
  const pid = Number.isSafeInteger(part.pid) && part.pid > 0 ? part.pid : null;
  const alive = pid !== null ? Boolean(isProcessAlive(pid, part.token)) : false;
  const logStat = typeof part.log === 'string' ? statInfo(fs, part.log) : null;
  const hangsRaw = typeof part.hangs === 'string' ? readJson(fs, part.hangs, null) : null;
  const hangs = Array.isArray(hangsRaw) ? hangsRaw.filter(isObject) : [];

  let state = 'idle';
  let summary = `${role}: idle`;
  if (alive) {
    state = 'running';
    summary = `${role}: running (pid ${pid}${named(part.agentKind) ? `, ${part.agentKind}` : ''})`;
  } else if (hasExit) {
    state = 'exited';
    const why = exitRecord.signal ? `signal ${exitRecord.signal}` : `code ${exitRecord.code ?? 'null'}`;
    summary = `${role}: exited (${why})`;
  } else if (pid !== null) {
    state = 'stale';
    summary = `${role}: stale (pid ${pid} not running, no exit receipt)`;
  }

  const activityCandidates = [
    logStat?.mtimeMs,
    hasExit ? exitRecord.at : null,
    Number.isFinite(part.watch?.at) ? part.watch.at : null,
    Number.isFinite(part.started) ? part.started : null,
  ].filter(n => Number.isFinite(n) && n > 0);

  return {
    role,
    pid,
    agentKind: named(part.agentKind) ? part.agentKind : null,
    state,
    summary,
    logPath: typeof part.log === 'string' ? part.log : null,
    logSize: logStat?.size ?? 0,
    exit: hasExit ? exitRecord : null,
    hangCount: hangs.length,
    lastHang: hangs.at(-1) ?? null,
    startedAt: Number.isFinite(part.started) ? part.started : null,
    lastActivityAt: activityCandidates.length ? Math.max(...activityCandidates) : null,
  };
}

function classifySuite(job, coreRoot, { fs, env, readSuite }) {
  const hasSuiteField = isObject(job?.suite) || job?.phase === 'pr';
  if (!hasSuiteField) return null;
  const suiteCwd = named(job?.suite?.cwd)
    ? job.suite.cwd
    : (coreRoot && Number.isSafeInteger(job?.issue) ? join(coreRoot, 'worktrees', `${job.issue}-suite`) : null);
  if (!suiteCwd) return null;
  const canQuery = Boolean(isObject(job?.suite)) || Boolean(statInfo(fs, join(suiteCwd, 'package.json')));
  if (!canQuery && typeof readSuite !== 'function') return null;

  let progress = null;
  try {
    progress = readSuite({ cwd: suiteCwd, env });
  } catch {
    progress = null;
  }
  if (!isObject(progress)) return null;

  const logStat = typeof progress.logPath === 'string' ? statInfo(fs, progress.logPath) : null;
  const recordedCommit = progress.source?.commit ?? job.suite?.head ?? null;
  const headMismatch = named(job.head) && named(recordedCommit)
    && !String(job.head).startsWith(String(recordedCommit))
    && !String(recordedCommit).startsWith(String(job.head));
  const deadRunner = typeof progress.reason === 'string' && /runner ended|recorder_not_running/i.test(progress.reason);

  if (progress.state === 'unavailable') {
    return {
      kind: 'unavailable',
      detail: `full test suite queue unavailable (${oneLine(progress.reason || 'unreadable queue', 140)})`,
      position: null,
      childPid: null,
      logPath: null,
      receiptPath: null,
      lastActivityAt: null,
    };
  }
  if (deadRunner || (progress.state === 'finished' && headMismatch)) {
    const why = deadRunner
      ? oneLine(progress.reason, 140)
      : `receipt commit ${shortSha(recordedCommit)} differs from current PR head ${shortSha(job.head)}`;
    return {
      kind: 'stale-receipt',
      detail: `stale suite receipt (${why})`,
      position: null,
      childPid: null,
      logPath: typeof progress.logPath === 'string' ? progress.logPath : null,
      receiptPath: typeof progress.receiptPath === 'string' ? progress.receiptPath : null,
      lastActivityAt: logStat?.mtimeMs ?? progress.finishedAt ?? progress.queuedAt ?? null,
    };
  }
  if (progress.state === 'waiting') {
    const pos = Number.isSafeInteger(progress.position) ? progress.position : 1;
    return {
      kind: 'queued',
      detail: `queued in shared test-suite queue (position ${pos})`,
      position: pos,
      childPid: null,
      logPath: typeof progress.logPath === 'string' ? progress.logPath : null,
      receiptPath: typeof progress.receiptPath === 'string' ? progress.receiptPath : null,
      lastActivityAt: progress.queuedAt ?? logStat?.mtimeMs ?? null,
    };
  }
  if (progress.state === 'running') {
    const counts = isObject(progress.counts)
      && Number.isFinite(progress.counts.pass)
      && Number.isFinite(progress.counts.fail)
      ? ` [pass ${progress.counts.pass}, fail ${progress.counts.fail}]`
      : '';
    const pidPart = Number.isSafeInteger(progress.childPid) && progress.childPid > 0
      ? ` (pid ${progress.childPid})`
      : '';
    return {
      kind: 'running',
      detail: `running full test suite${pidPart}${counts}`,
      position: null,
      childPid: Number.isSafeInteger(progress.childPid) ? progress.childPid : null,
      logPath: typeof progress.logPath === 'string' ? progress.logPath : null,
      receiptPath: typeof progress.receiptPath === 'string' ? progress.receiptPath : null,
      lastActivityAt: logStat?.mtimeMs ?? progress.startedAt ?? null,
    };
  }
  return {
    kind: 'finished',
    detail: `full test suite finished (${oneLine(progress.outcome ?? `exit ${progress.exitCode ?? 'unknown'}`, 60)})`,
    position: null,
    childPid: null,
    logPath: typeof progress.logPath === 'string' ? progress.logPath : null,
    receiptPath: typeof progress.receiptPath === 'string' ? progress.receiptPath : null,
    lastActivityAt: progress.finishedAt ?? logStat?.mtimeMs ?? null,
  };
}

function collectIssueArtifacts(fs, logsDir, issue) {
  const prefix = `${issue}-`;
  const logs = [];
  const evidence = [];
  for (const name of listDir(fs, logsDir)) {
    if (!name.startsWith(prefix)) continue;
    const full = join(logsDir, name);
    if (name.endsWith('.log')) {
      const st = statInfo(fs, full);
      if (st) logs.push({ path: full, mtimeMs: st.mtimeMs, size: st.size });
    } else if (/^\d+-evidence-.*\.json$/.test(name)) {
      const st = statInfo(fs, full);
      if (st) evidence.push({ path: full, mtimeMs: st.mtimeMs });
    }
  }
  logs.sort((a, b) => b.mtimeMs - a.mtimeMs || b.path.localeCompare(a.path));
  evidence.sort((a, b) => b.mtimeMs - a.mtimeMs || b.path.localeCompare(a.path));
  return {
    logPaths: logs.map(item => item.path),
    latestLogMtimeMs: logs[0]?.mtimeMs ?? null,
    evidencePaths: evidence.map(item => item.path),
  };
}

function readMachineBlockers(machine, state, nowMs) {
  const blockers = [];
  if (Number.isFinite(machine?.pausedUntil) && machine.pausedUntil > nowMs) {
    blockers.push(`New jobs paused until ${new Date(machine.pausedUntil).toISOString()} (${machine.streak ?? 0} no-result runs in a row)`);
  }
  if (isObject(machine?.poolOut)) {
    const until = named(machine.poolOut.wakeAt)
      ? machine.poolOut.wakeAt
      : (Number.isFinite(machine.poolOut.resetAt) ? new Date(machine.poolOut.resetAt).toISOString() : null);
    blockers.push(`AI login pool exhausted${until ? ` until ${until}` : ''}`);
  }
  if (isObject(machine?.ciDown) && ['queued', 'billing'].includes(machine.ciDown.reason)) {
    blockers.push(`GitHub Actions hold (${machine.ciDown.reason}) since ${new Date(machine.ciDown.since).toISOString()}`);
  }
  const breaker = (isObject(state?.circuitBreaker) && state.circuitBreaker.active !== false ? state.circuitBreaker : null)
    ?? (isObject(machine?.circuitBreaker) && machine.circuitBreaker.active !== false ? machine.circuitBreaker : null);
  if (breaker && Number.isSafeInteger(breaker.pr)) {
    blockers.push(`Safety circuit breaker tripped on PR #${breaker.pr}: mode downgraded to observe (${oneLine(breaker.reason ?? breaker.code ?? 'post-merge regression', 120)})`);
  }
  return blockers;
}

function buildWorkerView(job, ctx) {
  const { fs, coreRoot, logsDir, isProcessAlive, env, readSuite, machineBlockers } = ctx;
  const issue = job.issue;
  const isIntake = job.__intake === true;
  const artifacts = collectIssueArtifacts(fs, logsDir, issue);

  const mainRole = isIntake ? 'intake' : (named(job.role) ? job.role : 'build');
  const mainPart = inspectPart(job.agent ?? (isIntake ? job : null), mainRole, { fs, isProcessAlive });
  const reviewPart = inspectPart(job.review?.agent, 'review', { fs, isProcessAlive });
  const suiteAgentPart = inspectPart(job.suite?.agent, 'suite-runner', { fs, isProcessAlive });
  const vectorsPart = inspectPart(job.vectors?.agent, 'vectors', { fs, isProcessAlive });
  const runtimePart = inspectPart(job.runtimeWait?.agent, 'interpreter-check', { fs, isProcessAlive });
  const suiteView = isIntake ? null : classifySuite(job, coreRoot, { fs, env, readSuite });

  const parts = [mainPart, reviewPart, suiteAgentPart, vectorsPart, runtimePart].filter(Boolean);
  const liveParts = parts.filter(part => part.state === 'running');
  const staleParts = parts.filter(part => part.state === 'stale');

  let stage = mainRole;
  let stageDetail = mainRole;
  if (isIntake) {
    stage = 'intake';
    stageDetail = 'read-only intake card worker';
  } else if (job.phase === 'ending') {
    stage = 'ending';
    stageDetail = `ending (${oneLine(job.end?.cause?.text ?? 'finishing cleanup', 140)})`;
  } else if (job.phase === 'released') {
    stage = 'release-pending';
    stageDetail = `release pending (retry pdd autopilot release ${issue})`;
  } else if (job.phase === 'pr') {
    const prLabel = Number.isSafeInteger(job.pr) ? `PR #${job.pr} (${shortSha(job.head)})` : 'PR check';
    if (suiteView?.kind === 'queued') {
      stage = 'suite-queued';
      stageDetail = `${prLabel}: ${suiteView.detail}`;
    } else if (suiteView?.kind === 'running') {
      stage = 'suite-running';
      stageDetail = `${prLabel}: ${suiteView.detail}`;
    } else if (suiteView?.kind === 'stale-receipt') {
      stage = 'suite-stale';
      stageDetail = `${prLabel}: ${suiteView.detail}`;
    } else if (reviewPart?.state === 'running') {
      stage = 'review';
      stageDetail = `${prLabel}: independent review running`;
    } else if (vectorsPart?.state === 'running') {
      stage = 'vectors';
      stageDetail = `${prLabel}: vector checks running`;
    } else if (runtimePart?.state === 'running') {
      stage = 'interpreter-check';
      stageDetail = `${prLabel}: PDD interpreter check running`;
    } else if (job.lane?.state === 'waiting') {
      stage = 'merge-lane';
      stageDetail = `${prLabel}: waiting in merge lane${job.lane.holder ? ` behind PR #${job.lane.holder}` : ''}`;
    } else if (job.lane?.state === 'final') {
      stage = 'merge-lane';
      stageDetail = `${prLabel}: final merge check`;
    } else {
      stage = 'pr-check';
      const reviewNote = named(job.review?.verdict) ? `review ${job.review.verdict}` : 'review pending';
      const suiteNote = suiteView?.detail ?? (job.suite ? 'suite started' : 'suite pending');
      stageDetail = `${prLabel}: ${reviewNote}, ${suiteNote}`;
    }
  } else if (mainRole === 'repair') {
    stage = 'repair';
    const attempt = Number.isSafeInteger(job.repairs) && job.repairs > 0 ? ` #${job.repairs}` : '';
    const prNote = Number.isSafeInteger(job.pr) ? ` on PR #${job.pr}` : '';
    stageDetail = `repair${attempt}${prNote}`;
  } else if (mainRole === 'conflict') {
    stage = 'conflict';
    stageDetail = `conflict resolution${Number.isSafeInteger(job.pr) ? ` on PR #${job.pr}` : ''}`;
  } else {
    stage = 'build';
    stageDetail = 'headless build';
  }

  // Owned process summary
  let processState = 'idle';
  let processSummary = 'no active worker process';
  if (suiteView?.kind === 'running' && (suiteView.childPid || suiteAgentPart?.state === 'running')) {
    processState = 'running';
    const pieces = [];
    if (suiteView.childPid) pieces.push(`suite pid ${suiteView.childPid}`);
    else if (suiteAgentPart?.pid) pieces.push(`suite wrapper pid ${suiteAgentPart.pid}`);
    if (reviewPart?.state === 'running') pieces.push(`review pid ${reviewPart.pid}`);
    processSummary = `running (${pieces.join(', ')})`;
  } else if (suiteView?.kind === 'queued' && suiteAgentPart?.state === 'running') {
    processState = 'waiting';
    processSummary = `waiting in suite queue (queue client pid ${suiteAgentPart.pid}${reviewPart?.state === 'running' ? `, review pid ${reviewPart.pid} running` : ''})`;
  } else if (liveParts.length > 0) {
    processState = 'running';
    processSummary = liveParts.map(part => part.summary).join('; ');
  } else if (staleParts.length > 0 || suiteView?.kind === 'stale-receipt') {
    processState = 'stale';
    const reasons = [
      ...staleParts.map(part => part.summary),
      ...(suiteView?.kind === 'stale-receipt' ? [suiteView.detail] : []),
    ];
    processSummary = reasons.join('; ');
  } else {
    const exitedParts = parts.filter(part => part.state === 'exited');
    if (exitedParts.length > 0) {
      processState = 'exited';
      processSummary = `${exitedParts.map(part => part.summary).join('; ')}; awaiting next Autopilot tick`;
    }
  }

  // Plain blockers
  const blockers = [];
  if (suiteView?.kind === 'queued') {
    blockers.push(`Queued in shared test-suite queue at position ${suiteView.position}`);
  }
  if (suiteView?.kind === 'stale-receipt') {
    blockers.push(`Stale test receipt: ${suiteView.detail}`);
  }
  if (staleParts.length > 0) {
    blockers.push(`Recorded worker process exited without a receipt (${staleParts.map(p => `${p.role} pid ${p.pid}`).join(', ')})`);
  }
  if (job.lane?.state === 'waiting') {
    blockers.push(`Waiting in merge lane${job.lane.holder ? ` for PR #${job.lane.holder}` : ''}${Number.isFinite(job.lane.since) ? ` since ${new Date(job.lane.since).toISOString()}` : ''}`);
  }
  if (job.runtimeWait?.state === 'waiting') {
    blockers.push(`Waiting on PDD interpreter maintenance${job.runtimeWait.until ? ` until ${new Date(job.runtimeWait.until).toISOString()}` : ''}`);
  }
  if (job.stepStop?.poolExhausted) {
    const wake = named(job.stepStop.wakeAt)
      ? job.stepStop.wakeAt
      : (Number.isFinite(job.stepStop.until) ? new Date(job.stepStop.until).toISOString() : null);
    blockers.push(`Waiting on AI quota / login pool${wake ? ` until ${wake}` : ''}`);
  }
  for (const part of parts) {
    if (part.hangCount > 0) {
      const cmd = oneLine(part.lastHang?.command ?? 'hung child command', 100);
      blockers.push(`Watchdog stopped ${part.hangCount} hung command${part.hangCount === 1 ? '' : 's'} (${cmd})`);
    }
  }
  if (named(job.lastError)) {
    blockers.push(`Last error: ${oneLine(job.lastError, 180)}`);
  }
  for (const mb of machineBlockers) {
    if (!blockers.includes(mb)) blockers.push(mb);
  }

  // Active streams to tail (prefer live suite validation log when running, plus active worker logs)
  const streams = [];
  const addStream = (label, filePath) => {
    if (!named(filePath)) return;
    if (streams.some(s => s.path === filePath)) return;
    if (statInfo(fs, filePath)) streams.push({ label, path: filePath });
  };
  if (job.phase === 'pr') {
    if (suiteView?.kind === 'running' && suiteView.logPath) addStream('suite', suiteView.logPath);
    if (reviewPart?.state === 'running') addStream('review', reviewPart.logPath);
    if (suiteAgentPart?.state === 'running' && suiteView?.kind !== 'running') addStream('suite-queue', suiteAgentPart.logPath);
    if (vectorsPart?.state === 'running') addStream('vectors', vectorsPart.logPath);
    if (runtimePart?.state === 'running') addStream('interpreter', runtimePart.logPath);
    // Fallback to latest finished PR sub-logs when nothing is currently live
    if (!streams.length) {
      if (suiteView?.logPath) addStream('suite', suiteView.logPath);
      addStream('suite-queue', suiteAgentPart?.logPath);
      addStream('review', reviewPart?.logPath);
      addStream(mainRole, mainPart?.logPath);
    }
  } else {
    addStream(mainRole, mainPart?.logPath);
  }
  if (!streams.length && artifacts.logPaths.length) {
    addStream('worker', artifacts.logPaths[0]);
  }

  const evidencePaths = [
    ...artifacts.evidencePaths,
    ...(named(suiteView?.receiptPath) && statInfo(fs, suiteView.receiptPath) ? [suiteView.receiptPath] : []),
  ];
  const allLogPaths = [
    ...new Set([
      ...streams.map(s => s.path),
      ...(named(suiteView?.logPath) && statInfo(fs, suiteView.logPath) ? [suiteView.logPath] : []),
      ...artifacts.logPaths,
    ]),
  ];

  const activityTimes = [
    ...parts.map(p => p.lastActivityAt),
    suiteView?.lastActivityAt,
    artifacts.latestLogMtimeMs,
    job.__fileMtimeMs,
    Number.isFinite(job.started) ? job.started : null,
  ].filter(n => Number.isFinite(n) && n > 0);
  const lastActivityAt = activityTimes.length ? Math.max(...activityTimes) : null;

  return {
    issue,
    issues: Array.isArray(job.issues) && job.issues.length ? job.issues : [issue],
    title: named(job.title) ? oneLine(job.title, 140) : null,
    pr: Number.isSafeInteger(job.pr) ? job.pr : null,
    head: named(job.head) ? job.head : null,
    active: true,
    liveProcess: processState === 'running' || processState === 'waiting',
    stage,
    stageDetail,
    processState,
    processSummary,
    suite: suiteView,
    blockers,
    lastActivityAt,
    startedAt: Number.isFinite(job.started) ? job.started : (mainPart?.startedAt ?? null),
    streams,
    logPaths: allLogPaths,
    evidencePaths,
  };
}

function readJobsFromDir(fs, dirPath, intake = false) {
  const rows = [];
  for (const name of listDir(fs, dirPath)) {
    if (!/^\d+\.json$/.test(name)) continue;
    const full = join(dirPath, name);
    const parsed = readJson(fs, full, null);
    if (!isObject(parsed)) continue;
    const issue = Number.isSafeInteger(parsed.issue) ? parsed.issue : Number(name.replace(/\.json$/, ''));
    if (!Number.isSafeInteger(issue) || issue <= 0) continue;
    const st = statInfo(fs, full);
    rows.push({
      ...parsed,
      issue,
      __intake: intake,
      __fileMtimeMs: st?.mtimeMs ?? null,
    });
  }
  return rows.sort((a, b) => a.issue - b.issue);
}

function readRecentHistory(fs, coreRoot, logsDir) {
  const historyPath = join(coreRoot, 'history.jsonl');
  let raw = '';
  try { raw = fs.readFileSync(historyPath, 'utf8'); } catch { return []; }
  const parsed = [];
  for (const line of raw.split('\n')) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    try {
      const row = JSON.parse(trimmed);
      if (isObject(row) && typeof row.outcome === 'string' && Number.isSafeInteger(row.issue) && row.issue > 0) {
        parsed.push(row);
      }
    } catch { /* Ignore partial/corrupt line. */ }
  }
  parsed.reverse();
  const seen = new Set();
  const unique = [];
  for (const row of parsed) {
    if (seen.has(row.issue)) continue;
    seen.add(row.issue);
    const artifacts = collectIssueArtifacts(fs, logsDir, row.issue);
    unique.push({
      issue: row.issue,
      outcome: oneLine(row.outcome, 40),
      at: Number.isFinite(row.at) ? row.at : null,
      pr: Number.isSafeInteger(row.pr) ? row.pr : null,
      text: named(row.text) ? oneLine(row.text, 180) : '',
      logPaths: artifacts.logPaths,
      evidencePaths: artifacts.evidencePaths,
    });
  }
  return unique;
}

function resolveEffectiveMode(fs, gitRoot, launcherState, machineState) {
  const repoConfig = readJson(fs, join(gitRoot, 'pdd.json'), null);
  const configMode = ['off', 'observe', 'auto'].includes(repoConfig?.autopilot?.mode)
    ? repoConfig.autopilot.mode
    : null;
  const breaker = (isObject(launcherState?.circuitBreaker) && launcherState.circuitBreaker.active !== false)
    || (isObject(machineState?.circuitBreaker) && machineState.circuitBreaker.active !== false);
  if (breaker) return { mode: 'observe', modeSource: 'circuit-breaker' };
  if (['off', 'observe', 'auto'].includes(launcherState?.mode)) {
    return { mode: launcherState.mode, modeSource: 'machine' };
  }
  if (configMode) return { mode: configMode, modeSource: 'pdd.json' };
  return { mode: 'off', modeSource: 'default' };
}

export async function inspectAutopilotWorkers(input = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const env = input.env ?? process.env;
  const cwd = input.cwd ?? process.cwd();
  const now = ports.now ?? Date.now;
  const nowMs = now();
  const git = ports.git ?? defaultGit;
  const isProcessAlive = ports.isProcessAlive ?? defaultIsProcessAlive;
  const readSuite = ports.readSuite ?? ((suiteInput) => readSuiteProgress(suiteInput));

  let gitRoot = ports.gitRoot ?? null;
  if (!gitRoot) {
    const reply = await git(['rev-parse', '--show-toplevel'], { cwd, env });
    if (reply.code !== 0 || !named(reply.stdout)) {
      const notRepo = /not a git repository/i.test(String(reply.stderr ?? ''));
      return {
        ok: false,
        exitCode: 1,
        message: notRepo
          ? 'This folder is not a Git repository. cd into the repo you want Autopilot to work on, then run pdd autopilot logs again.'
          : 'Autopilot logs could not read the Git repository; retry.',
      };
    }
    gitRoot = reply.stdout.trim();
  }

  const stateRoot = ports.stateRoot ?? join(env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
  const stateId = createHash('sha256').update(gitRoot).digest('hex').slice(0, 20);
  const stateFile = join(stateRoot, `${stateId}.json`);
  const coreRoot = ports.coreRoot ?? join(stateRoot, `${stateId}-core`);
  const logsDir = join(coreRoot, 'logs');

  const launcherState = readJson(fs, stateFile, null);
  const machineState = readJson(fs, join(coreRoot, 'core.json'), null);
  const { mode, modeSource } = resolveEffectiveMode(fs, gitRoot, launcherState, machineState);
  const machineBlockers = readMachineBlockers(machineState, launcherState, nowMs);

  const coreJobs = readJobsFromDir(fs, join(coreRoot, 'jobs'), false);
  const activeIssueIds = new Set(coreJobs.map(j => j.issue));
  const intakeJobs = readJobsFromDir(fs, join(coreRoot, 'intake', 'jobs'), true)
    .filter(j => !activeIssueIds.has(j.issue));

  const ctx = {
    fs,
    coreRoot,
    logsDir,
    isProcessAlive,
    env,
    readSuite,
    machineBlockers,
  };
  const workers = [...coreJobs, ...intakeJobs]
    .map(job => buildWorkerView(job, ctx))
    .sort((a, b) => a.issue - b.issue);
  const recent = readRecentHistory(fs, coreRoot, logsDir)
    .filter(row => !workers.some(w => w.issue === row.issue));

  return {
    ok: true,
    nowMs,
    repo: named(launcherState?.repo) ? launcherState.repo : null,
    gitRoot,
    stateId,
    stateFile,
    coreRoot,
    mode,
    modeSource,
    timerEnabled: Boolean(launcherState?.enabled),
    machineBlockers,
    workers,
    recent,
  };
}

function buildHistoricalWorkerView(issue, snapshot, fs) {
  const logsDir = join(snapshot.coreRoot, 'logs');
  const historyRow = snapshot.recent.find(row => row.issue === issue) ?? null;
  const artifacts = collectIssueArtifacts(fs, logsDir, issue);
  if (!historyRow && !artifacts.logPaths.length && !artifacts.evidencePaths.length) return null;

  const outcome = historyRow ? `${historyRow.outcome}${historyRow.text ? ` — ${historyRow.text}` : ''}` : 'saved log on disk';
  return {
    issue,
    issues: [issue],
    title: null,
    pr: historyRow?.pr ?? null,
    head: null,
    active: false,
    liveProcess: false,
    stage: 'finished',
    stageDetail: `finished (${outcome})`,
    processState: 'finished',
    processSummary: 'not running (completed)',
    suite: null,
    blockers: [],
    lastActivityAt: historyRow?.at ?? artifacts.latestLogMtimeMs ?? null,
    startedAt: null,
    streams: artifacts.logPaths.length ? [{ label: 'worker', path: artifacts.logPaths[0] }] : [],
    logPaths: artifacts.logPaths,
    evidencePaths: artifacts.evidencePaths,
  };
}

function modeBanner(snapshot) {
  const repoLabel = snapshot.repo ?? snapshot.gitRoot;
  const observeNote = snapshot.mode === 'observe' ? ' (read-only viewer; observe mode never approves or merges)' : ' (read-only viewer)';
  return `Autopilot logs: ${repoLabel} · mode ${snapshot.mode}${observeNote}`;
}

function renderWorkerList(snapshot) {
  const lines = [modeBanner(snapshot)];
  for (const blocker of snapshot.machineBlockers) {
    lines.push(`Blocker: ${blocker}`);
  }
  if (!snapshot.workers.length && !snapshot.recent.length) {
    lines.push('No active or recent Autopilot workers found for this repository.');
    lines.push('Start Autopilot with pdd autopilot start, or check configuration with pdd autopilot status.');
    return lines.join('\n');
  }
  if (snapshot.workers.length) {
    lines.push('', `Current workers (${snapshot.workers.length}):`);
    for (const worker of snapshot.workers) {
      const titlePart = worker.title ? ` "${worker.title}"` : '';
      lines.push(`  #${worker.issue}${titlePart}`);
      lines.push(`    Stage: ${worker.stageDetail}`);
      lines.push(`    Process: ${worker.processSummary}`);
      lines.push(`    Last activity: ${formatStamp(snapshot.nowMs, worker.lastActivityAt)}`);
      lines.push(`    Blockers: ${worker.blockers.length ? worker.blockers.join('; ') : 'none'}`);
      if (worker.logPaths[0]) lines.push(`    Log: ${worker.logPaths[0]}`);
      if (worker.evidencePaths[0]) lines.push(`    Evidence: ${worker.evidencePaths[0]}`);
    }
    const exampleIssue = snapshot.workers[0].issue;
    lines.push('', `Follow a worker live: pdd autopilot logs ${exampleIssue} --follow`);
  } else {
    lines.push('', 'Current workers: none active right now.');
  }
  if (snapshot.recent.length) {
    const shown = snapshot.recent.slice(0, 5);
    lines.push('', `Recent finished workers (${shown.length}):`);
    for (const row of shown) {
      const prText = row.pr ? ` (PR #${row.pr})` : '';
      const logHint = row.logPaths[0] ? ` · log: ${basename(row.logPaths[0])}` : '';
      lines.push(`  #${row.issue}${prText}: ${row.outcome} ${formatAge(snapshot.nowMs, row.at)}${row.text ? ` — ${row.text}` : ''}${logHint}`);
    }
    if (!snapshot.workers.length) {
      lines.push('', `Inspect a finished worker's saved log: pdd autopilot logs ${shown[0].issue}`);
    }
  }
  return lines.join('\n');
}

function renderWorkerHeader(snapshot, worker) {
  const lines = [
    modeBanner(snapshot),
    `Issue: #${worker.issue}${worker.title ? ` — ${worker.title}` : ''}${worker.pr ? ` (PR #${worker.pr})` : ''}`,
    `Stage: ${worker.stageDetail}`,
    `Process: ${worker.processSummary}`,
  ];
  if (worker.suite) {
    lines.push(`Suite queue: ${worker.suite.detail}`);
  }
  lines.push(`Last activity: ${formatStamp(snapshot.nowMs, worker.lastActivityAt)}`);
  lines.push(`Blockers: ${worker.blockers.length ? worker.blockers.join('; ') : 'none'}`);
  if (worker.logPaths.length) {
    lines.push(`Log: ${worker.logPaths[0]}`);
    for (const extra of worker.logPaths.slice(1, 3)) lines.push(`Saved log: ${extra}`);
  } else {
    lines.push('Log: (no log file written yet)');
  }
  for (const ev of worker.evidencePaths.slice(0, 3)) {
    lines.push(`Evidence: ${ev}`);
  }
  return lines;
}

function readAppendedCompleteLines(fs, filePath, offset) {
  let fd;
  try {
    fd = fs.openSync(filePath, 'r');
    const size = fs.fstatSync(fd).size;
    if (size < offset) offset = 0; // Handle log truncation cleanly.
    const length = Math.min(READ_CHUNK_LIMIT, size - offset);
    if (length <= 0) return { nextOffset: offset, lines: [] };
    const buffer = Buffer.alloc(length);
    const bytesRead = fs.readSync(fd, buffer, 0, length, offset);
    if (bytesRead <= 0) return { nextOffset: offset, lines: [] };
    const text = buffer.subarray(0, bytesRead).toString('utf8');
    const lastNewline = text.lastIndexOf('\n');
    if (lastNewline < 0) {
      if (bytesRead >= READ_CHUNK_LIMIT) {
        return { nextOffset: offset + bytesRead, lines: [text] };
      }
      return { nextOffset: offset, lines: [] };
    }
    const completeChunk = text.slice(0, lastNewline + 1);
    const usedBytes = Buffer.byteLength(completeChunk, 'utf8');
    return {
      nextOffset: offset + usedBytes,
      lines: completeChunk.slice(0, -1).split('\n'),
    };
  } catch {
    return { nextOffset: offset, lines: [] };
  } finally {
    if (fd !== undefined) {
      try { fs.closeSync(fd); } catch {}
    }
  }
}

export async function runAutopilotLogs(input = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const follow = Boolean(input.follow);
  const json = Boolean(input.json);
  const tailLines = input.lines === undefined ? DEFAULT_LINES : Number(input.lines);

  if (!Number.isInteger(tailLines) || tailLines < 1 || tailLines > MAX_LINES) {
    return { exitCode: 2, message: `Use --lines N with an integer from 1 to ${MAX_LINES}.` };
  }
  if (follow && json) {
    return { exitCode: 2, message: '--json prints one snapshot and cannot be combined with --follow.' };
  }
  if (input.positionalIssue !== undefined && input.optionIssue !== undefined && input.positionalIssue !== input.optionIssue) {
    return { exitCode: 2, message: 'Pass the issue once: pdd autopilot logs ISSUE or pdd autopilot logs --issue ISSUE.' };
  }
  const rawIssue = input.issue ?? input.positionalIssue ?? input.optionIssue;
  const parsedIssue = parseIssueSelector(rawIssue);
  if (!parsedIssue.ok) {
    return { exitCode: 2, message: `"${oneLine(rawIssue, 80)}" is not a valid issue number, owner/repo#N or GitHub issue URL.` };
  }
  if (follow && parsedIssue.issue === null) {
    return { exitCode: 2, message: 'Select an issue to follow: pdd autopilot logs ISSUE --follow.' };
  }

  const snapshot = await inspectAutopilotWorkers(input, ports);
  if (!snapshot.ok) return { exitCode: snapshot.exitCode, message: snapshot.message };

  if (parsedIssue.repo && snapshot.repo && parsedIssue.repo.toLowerCase() !== snapshot.repo.toLowerCase()) {
    return { exitCode: 1, message: `Issue ${parsedIssue.repo}#${parsedIssue.issue} does not belong to ${snapshot.repo}.` };
  }

  if (parsedIssue.issue === null) {
    if (json) {
      const payload = {
        schema: 'pdd.autopilot-logs.v1',
        repo: snapshot.repo,
        gitRoot: snapshot.gitRoot,
        mode: snapshot.mode,
        modeSource: snapshot.modeSource,
        timerEnabled: snapshot.timerEnabled,
        machineBlockers: snapshot.machineBlockers,
        workers: snapshot.workers,
        recent: snapshot.recent.slice(0, 10),
      };
      return { exitCode: 0, message: JSON.stringify(payload, null, 2), data: payload };
    }
    return { exitCode: 0, message: renderWorkerList(snapshot) };
  }

  const issue = parsedIssue.issue;
  const findTarget = snap => snap.workers.find(w => w.issue === issue || w.issues.includes(issue))
    ?? buildHistoricalWorkerView(issue, snap, fs);

  const initialWorker = findTarget(snapshot);
  if (!initialWorker) {
    return {
      exitCode: 1,
      message: `No active or saved Autopilot worker found for issue #${issue} in this repository. Run pdd autopilot logs to list workers.`,
    };
  }

  if (json) {
    const tail = initialWorker.streams[0]
      ? formatLogTail(fs, initialWorker.streams[0].path, tailLines)
      : [];
    const payload = {
      schema: 'pdd.autopilot-logs.v1',
      repo: snapshot.repo,
      gitRoot: snapshot.gitRoot,
      mode: snapshot.mode,
      modeSource: snapshot.modeSource,
      timerEnabled: snapshot.timerEnabled,
      worker: initialWorker,
      lines: tail,
    };
    return { exitCode: 0, message: JSON.stringify(payload, null, 2), data: payload };
  }

  if (!follow) {
    const out = renderWorkerHeader(snapshot, initialWorker);
    const multi = initialWorker.streams.length > 1;
    let printedAny = false;
    for (const stream of initialWorker.streams) {
      const tail = formatLogTail(fs, stream.path, tailLines);
      if (!tail.length) continue;
      printedAny = true;
      out.push('', `--- Recent progress${multi ? ` (${stream.label})` : ''} ---`);
      for (const line of tail) out.push(multi ? `[${stream.label}] ${line}` : line);
    }
    if (!printedAny) {
      out.push('', '--- Recent progress ---', '(no readable log output recorded yet)');
    }
    if (initialWorker.active) {
      out.push('', `Follow live output: pdd autopilot logs ${initialWorker.issue} --follow`);
    }
    return { exitCode: 0, message: out.join('\n') };
  }

  // Live --follow streaming mode (strictly read-only; detaches without signaling worker)
  const stdout = ports.stdout ?? process.stdout;
  const writeLine = text => stdout.write(`${text}\n`);
  for (const headerLine of renderWorkerHeader(snapshot, initialWorker)) writeLine(headerLine);

  if (!initialWorker.active) {
    const tail = initialWorker.streams[0] ? formatLogTail(fs, initialWorker.streams[0].path, tailLines) : [];
    if (tail.length) {
      writeLine('');
      writeLine('--- Saved progress ---');
      for (const l of tail) writeLine(l);
    }
    writeLine('');
    writeLine(`Worker #${initialWorker.issue} has already finished; nothing live to follow.`);
    return { exitCode: 0, message: '', streamed: true };
  }

  writeLine('Following live output (press Ctrl-C to detach without stopping the worker)...');
  writeLine('');

  const offsets = new Map();
  const multiInitial = initialWorker.streams.length > 1;
  for (const stream of initialWorker.streams) {
    const st = statInfo(fs, stream.path);
    const tail = formatLogTail(fs, stream.path, tailLines);
    for (const l of tail) writeLine(multiInitial ? `[${stream.label}] ${l}` : l);
    offsets.set(stream.path, st?.size ?? 0);
  }

  let lastStageSig = `${initialWorker.stageDetail}|${initialWorker.processSummary}`;
  let lastBlockersSig = initialWorker.blockers.join('; ');
  const pollMs = Math.max(10, Number.isFinite(ports.pollMs) ? ports.pollMs : DEFAULT_POLL_MS);

  let detached = false;
  let wakeSleep = null;
  const triggerDetach = () => {
    if (detached) return;
    detached = true;
    wakeSleep?.();
  };

  const signal = ports.signal ?? null;
  const onSigint = () => triggerDetach();
  const onSigterm = () => triggerDetach();
  if (signal) {
    if (signal.aborted) detached = true;
    else signal.addEventListener('abort', triggerDetach, { once: true });
  } else {
    process.once('SIGINT', onSigint);
    process.once('SIGTERM', onSigterm);
  }

  const waitNext = ports.sleep
    ? async ms => {
        if (detached) return;
        await ports.sleep(ms);
      }
    : ms => new Promise(resolveWait => {
        if (detached) { resolveWait(); return; }
        const timer = setTimeout(() => { wakeSleep = null; resolveWait(); }, ms);
        wakeSleep = () => { clearTimeout(timer); wakeSleep = null; resolveWait(); };
      });

  const maxPolls = Number.isInteger(ports.maxPolls) && ports.maxPolls > 0 ? ports.maxPolls : Infinity;
  let polls = 0;

  try {
    while (!detached && polls < maxPolls) {
      await waitNext(pollMs);
      if (detached) break;
      polls++;

      const currentSnap = await inspectAutopilotWorkers(input, ports);
      if (!currentSnap.ok) break;
      const currentWorker = findTarget(currentSnap);
      if (!currentWorker) {
        writeLine(`[stage] Worker #${issue} finished.`);
        return { exitCode: 0, message: '', streamed: true };
      }

      const stageSig = `${currentWorker.stageDetail}|${currentWorker.processSummary}`;
      if (stageSig !== lastStageSig) {
        lastStageSig = stageSig;
        writeLine(`[stage] ${currentWorker.stageDetail} · ${currentWorker.processSummary}`);
      }
      const blockersSig = currentWorker.blockers.join('; ');
      if (blockersSig !== lastBlockersSig) {
        lastBlockersSig = blockersSig;
        if (currentWorker.blockers.length) writeLine(`[blocker] ${blockersSig}`);
      }

      const multiNow = currentWorker.streams.length > 1;
      for (const stream of currentWorker.streams) {
        const isNewStream = !offsets.has(stream.path);
        if (isNewStream) {
          offsets.set(stream.path, 0);
          writeLine(`[stage] Streaming ${stream.label} log: ${stream.path}`);
        }
        const prevOffset = offsets.get(stream.path) ?? 0;
        const { nextOffset, lines } = readAppendedCompleteLines(fs, stream.path, prevOffset);
        offsets.set(stream.path, nextOffset);
        for (const raw of lines) {
          const rendered = formatWorkerLogLine(raw);
          if (!rendered) continue;
          for (const line of rendered.split('\n')) {
            if (line.trim()) writeLine(multiNow ? `[${stream.label}] ${line}` : line);
          }
        }
      }

      if (!currentWorker.active) {
        writeLine(`[stage] ${currentWorker.stageDetail}`);
        return { exitCode: 0, message: '', streamed: true };
      }
      if (!currentWorker.liveProcess && !currentSnap.timerEnabled) {
        writeLine(`[stage] Worker #${currentWorker.issue} has no live process and the Autopilot timer is stopped.`);
        return { exitCode: 0, message: '', streamed: true };
      }
    }
  } finally {
    if (signal) {
      try { signal.removeEventListener('abort', triggerDetach); } catch {}
    } else {
      process.removeListener('SIGINT', onSigint);
      process.removeListener('SIGTERM', onSigterm);
    }
  }

  if (detached) {
    writeLine(`Detached from issue #${initialWorker.issue} (background worker continues untouched).`);
  }
  return { exitCode: 0, message: '', streamed: true };
}
