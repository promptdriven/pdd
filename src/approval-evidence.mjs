// Generated from prompts/cli/approval-evidence.prompt.md (sha256: 26ec261b3bfc7a60d463ead4c0fcbcb70ad4f518caa2e1db145aa1a8c41b8d61).
import * as nodeFs from 'node:fs/promises';
import { join, isAbsolute } from 'node:path';
import { homedir } from 'node:os';

// Match a workflow stage to its agent session files.
const sessionFile = /^rollout-[^/]+\.jsonl$/;
const sessionId = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const epoch = value => {
  if (Number.isFinite(value)) return value;
  if (typeof value !== 'string' || !value.trim()) return null;
  const n = Number(value);
  if (Number.isFinite(n)) return n;
  const t = Date.parse(value);
  return Number.isFinite(t) ? t : null;
};
const escapedClaudeCwd = cwd => cwd.replace(/[^a-zA-Z0-9]/g, '-');
const messages = {
  invalid_request: 'Cannot verify chat approval without a valid stage, gate time and decision.',
  session_not_found: 'No native session matched this worktree and stage time window.',
  session_ambiguous: 'More than one native session matched this worktree and stage time window.',
  session_unreadable: 'Cannot verify chat approval because native session evidence could not be read.',
  user_message_missing: 'No user message was found after the gate question in this native session.',
};
const refuse = code => ({ ok: false, code, message: messages[code] });

function parseRows(text) {
  const lines = text.split('\n');
  lines.pop(); // An in-progress final write is not evidence, even if valid JSON.
  const rows = [];
  let malformed = false;
  for (const line of lines) {
    if (!line.trim()) continue;
    try {
      const row = JSON.parse(line);
      if (!row || typeof row !== 'object' || Array.isArray(row)) malformed = true;
      else rows.push(row);
    } catch { malformed = true; }
  }
  return { rows, malformed };
}

function identity(row, agent) {
  let meta;
  if (agent === 'codex') {
    if (row.type !== 'session_meta') return null;
    meta = row.payload;
    // A step subagent is not the person's chat, even though it shares the worktree cwd.
    if (meta?.thread_source === 'subagent' || meta?.parent_thread_id || meta?.source?.subagent) return null;
  } else {
    if (!['user', 'assistant'].includes(row.type) || row.isMeta === true || row.isSidechain === true) return null;
    meta = { id: row.sessionId, cwd: row.cwd, timestamp: row.timestamp };
  }
  if (!sessionId.test(meta?.id ?? '') || typeof meta?.cwd !== 'string') return null;
  const timestamp = epoch(meta.timestamp ?? row.timestamp);
  return timestamp === null ? null : { id: meta.id, cwd: meta.cwd, timestamp };
}

// Select user text and exclude generated Claude records.
function textBlocks(content, types) {
  if (typeof content === 'string') return content;
  if (!Array.isArray(content)) return '';
  return content.filter(block => types.includes(block?.type) && typeof block.text === 'string')
    .map(block => block.text).join('\n');
}

function generatedContext(text) {
  const value = text.trim();
  if (value.startsWith('# AGENTS.md instructions for ')) return true;
  const header = '# AGENTS.md instructions';
  if (value.startsWith(header)) {
    const rest = value.slice(header.length), marker = rest.indexOf('<INSTRUCTIONS>');
    if (marker >= 0 && rest.slice(0, marker).includes('\n') && !rest.slice(0, marker).trim()) return true;
  }
  // Each active kind can consume arbitrary inner text until a matching close.
  // A close creates a boundary where another wrapper may start. Keeping both
  // possible kinds avoids retries across ambiguous or nested closing tags.
  const active = new Set();
  let boundary = true, end = 0;
  for (const match of value.matchAll(/<\/?(?:environment_context|permissions instructions)>/g)) {
    const closing = match[0][1] === '/', kind = match[0].slice(closing ? 2 : 1, -1);
    if (!closing && boundary && !value.slice(end, match.index).trim()) active.add(kind);
    boundary = closing && active.has(kind);
    end = match.index + match[0].length;
  }
  return end > 0 && boundary && !value.slice(end).trim();
}

function userText(row, agent, meta) {
  if (agent === 'claude') {
    // Claude also writes user rows that no person typed: task notifications, messages from other agents,
    // compaction summaries and (in older versions, without origin) system reminders and local command output.
    if (row.type !== 'user' || row.message?.role !== 'user' || row.isMeta === true || row.isSidechain === true
      || row.isCompactSummary === true || row.isVisibleInTranscriptOnly === true
      || row.origin !== undefined && row.origin?.kind !== 'human'
      || row.sessionId !== meta.id || row.cwd !== meta.cwd) return '';
    const text = textBlocks(row.message.content, ['text']);
    return /^\s*<(?:task-notification|system-reminder|local-command-)/.test(text) ? '' : text;
  }
  const payload = row.payload;
  if (row.type === 'response_item' && payload?.type === 'message' && payload.role === 'user') {
    return textBlocks(payload.content, ['input_text', 'text']);
  }
  if (row.type === 'event_msg' && payload?.type === 'user_message' && typeof payload.message === 'string') {
    return payload.message;
  }
  return '';
}

async function sessionCandidates(stage, ports) {
  const fs = ports.fs ?? nodeFs;
  const env = ports.env ?? process.env;
  const home = ports.home ?? env.HOME ?? homedir();
  const root = stage.agent === 'codex'
    ? join(ports.codexHome ?? env.CODEX_HOME ?? join(home, '.codex'), 'sessions')
    : join(ports.claudeConfigDir ?? env.CLAUDE_CONFIG_DIR ?? join(home, '.claude'), 'projects', escapedClaudeCwd(stage.root));
  const files = [];
  async function walk(dir, depth = 0) {
    if (depth > 20) throw new Error('discovery_depth');
    let entries;
    try { entries = await fs.readdir(dir, { withFileTypes: true }); }
    catch (error) { if (error.code === 'ENOENT' && depth === 0) return; throw error; }
    for (const entry of entries) {
      if (entry.isSymbolicLink()) continue;
      const path = join(dir, entry.name);
      if (entry.isDirectory() && stage.agent === 'codex') await walk(path, depth + 1);
      else if (entry.isFile() && (stage.agent === 'codex' ? sessionFile.test(entry.name) : entry.name.endsWith('.jsonl'))
        && (!stage.sessionId || entry.name.includes(stage.sessionId))) files.push(path);
    }
  }
  await walk(root);
  const matches = [];
  for (const path of files) {
    // A file last written before the stage started cannot hold this session; skip it without reading.
    if ((await fs.stat(path)).mtimeMs < stage.startedAt) continue;
    const parsed = parseRows(await fs.readFile(path, 'utf8'));
    const identities = parsed.rows.map(row => identity(row, stage.agent)).filter(Boolean);
    const meta = identities[0];
    if (!meta) {
      // A damaged identity cannot safely be ruled out of the candidate set.
      if (parsed.malformed) throw new Error('unreadable_identity');
      continue;
    }
    if (meta.cwd !== stage.root || meta.timestamp < stage.startedAt || meta.timestamp > stage.endedAt) continue;
    if (stage.sessionId && meta.id !== stage.sessionId) continue;
    if (parsed.malformed || identities.some(item => item.id !== meta.id || item.cwd !== meta.cwd)) {
      throw new Error('unreadable_session');
    }
    matches.push({ meta, rows: parsed.rows });
  }
  return matches;
}

export async function readApprovalEvidence(request, ports = {}) {
  const { stage, gateAskedAt, decision, ignorePrefixes = [] } = request ?? {};
  const now = (ports.now ?? Date.now)();
  if (!stage || !['codex', 'claude'].includes(stage.agent) || typeof stage.root !== 'string' || !isAbsolute(stage.root)
    || !Number.isFinite(stage.startedAt) || !Number.isFinite(stage.endedAt) || stage.endedAt < stage.startedAt
    || !Number.isFinite(gateAskedAt) || gateAskedAt < stage.startedAt || !Number.isFinite(now)
    || gateAskedAt > now || stage.endedAt > now || !['approve', 'changes'].includes(decision)
    || stage.sessionId !== undefined && stage.sessionId !== null && !sessionId.test(stage.sessionId)
    || !Array.isArray(ignorePrefixes) || ignorePrefixes.some(prefix => typeof prefix !== 'string' || !prefix)) return refuse('invalid_request');
  try {
    const matches = await sessionCandidates(stage, ports);
    if (matches.length === 0) return refuse('session_not_found');
    // A resumed session can continue in another file with the same id; that is still one session.
    if (new Set(matches.map(match => match.meta.id)).size !== 1) return refuse('session_ambiguous');
    const { meta } = matches[0], rows = matches.flatMap(match => match.rows);
    let latest = null;
    for (const row of rows) {
      const at = epoch(row.timestamp);
      if (at === null || at <= gateAskedAt || at > now) continue;
      const text = userText(row, stage.agent, meta);
      const trimmed = text.trim();
      if (trimmed && !(stage.agent === 'codex' && generatedContext(text)) && !trimmed.startsWith('[Request interrupted')
        && !ignorePrefixes.some(prefix => trimmed.startsWith(prefix))
        && (!latest || at >= latest.at)) latest = { text, at };
    }
    if (!latest) return refuse('user_message_missing');
    return { ok: true, decision, agent: stage.agent, sessionId: meta.id,
      userMessage: latest.text, userMessageAt: latest.at };
  } catch {
    return refuse('session_unreadable');
  }
}

// Find the native session IDs that started in this worktree inside the window, for resuming a chat.
export async function findNativeSessions(stage, ports = {}) {
  if (!stage || !['codex', 'claude'].includes(stage.agent) || typeof stage.root !== 'string' || !isAbsolute(stage.root)
    || !Number.isFinite(stage.startedAt) || !Number.isFinite(stage.endedAt)) return [];
  try { return [...new Map((await sessionCandidates(stage, ports)).map(match => [match.meta.id, { id: match.meta.id, startedAt: match.meta.timestamp }])).values()]; }
  catch { return []; }
}
