// Contract: prompts/cli/approval-evidence.prompt.md.
import * as nodeFs from 'node:fs/promises';
import { join, isAbsolute } from 'node:path';
import { homedir } from 'node:os';

// Adapted from pdd-fleet workflow-run-records.mjs's stage-session matcher.
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
  } else {
    if (!['user', 'assistant'].includes(row.type) || row.isMeta === true || row.isSidechain === true) return null;
    meta = { id: row.sessionId, cwd: row.cwd, timestamp: row.timestamp };
  }
  if (!sessionId.test(meta?.id ?? '') || typeof meta?.cwd !== 'string') return null;
  const timestamp = epoch(meta.timestamp ?? row.timestamp);
  return timestamp === null ? null : { id: meta.id, cwd: meta.cwd, timestamp };
}

// Text selection and Claude exclusions adapted from pdd-workflow pane-transcript.mjs.
function textBlocks(content, types) {
  if (typeof content === 'string') return content;
  if (!Array.isArray(content)) return '';
  return content.filter(block => types.includes(block?.type) && typeof block.text === 'string')
    .map(block => block.text).join('\n');
}

function generatedContext(text) {
  const value = text.trim();
  return value.startsWith('# AGENTS.md instructions for ')
    || /^(?:<environment_context>[\s\S]*?<\/environment_context>\s*|<permissions instructions>[\s\S]*?<\/permissions instructions>\s*)+$/.test(value);
}

function userText(row, agent, meta) {
  if (agent === 'claude') {
    if (row.type !== 'user' || row.message?.role !== 'user' || row.isMeta === true || row.isSidechain === true
      || row.sessionId !== meta.id || row.cwd !== meta.cwd) return '';
    return textBlocks(row.message.content, ['text']);
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
      else if (entry.isFile() && (stage.agent === 'codex' ? sessionFile.test(entry.name) : entry.name.endsWith('.jsonl'))) files.push(path);
    }
  }
  await walk(root);
  const matches = [];
  for (const path of files) {
    const parsed = parseRows(await fs.readFile(path, 'utf8'));
    const identities = parsed.rows.map(row => identity(row, stage.agent)).filter(Boolean);
    const meta = identities[0];
    if (!meta) {
      // A damaged identity cannot safely be ruled out of the candidate set.
      if (parsed.malformed) throw new Error('unreadable_identity');
      continue;
    }
    if (meta.cwd !== stage.root || meta.timestamp < stage.startedAt || meta.timestamp > stage.endedAt) continue;
    if (parsed.malformed || identities.some(item => item.id !== meta.id || item.cwd !== meta.cwd)) {
      throw new Error('unreadable_session');
    }
    matches.push({ meta, rows: parsed.rows });
  }
  return matches;
}

export async function readApprovalEvidence(request, ports = {}) {
  const { stage, gateAskedAt, decision } = request ?? {};
  const now = (ports.now ?? Date.now)();
  if (!stage || !['codex', 'claude'].includes(stage.agent) || typeof stage.root !== 'string' || !isAbsolute(stage.root)
    || !Number.isFinite(stage.startedAt) || !Number.isFinite(stage.endedAt) || stage.endedAt < stage.startedAt
    || !Number.isFinite(gateAskedAt) || gateAskedAt < stage.startedAt || !Number.isFinite(now)
    || gateAskedAt > now || stage.endedAt > now || !['approve', 'changes'].includes(decision)) return refuse('invalid_request');
  try {
    const matches = await sessionCandidates(stage, ports);
    if (matches.length === 0) return refuse('session_not_found');
    if (matches.length !== 1) return refuse('session_ambiguous');
    const { meta, rows } = matches[0];
    let latest = null;
    for (const row of rows) {
      const at = epoch(row.timestamp);
      if (at === null || at <= gateAskedAt || at > now) continue;
      const text = userText(row, stage.agent, meta);
      if (text.trim() && !(stage.agent === 'codex' && generatedContext(text))
        && (!latest || at >= latest.at)) latest = { text, at };
    }
    if (!latest) return refuse('user_message_missing');
    return { ok: true, decision, agent: stage.agent, sessionId: meta.id,
      userMessage: latest.text, userMessageAt: latest.at };
  } catch {
    return refuse('session_unreadable');
  }
}
