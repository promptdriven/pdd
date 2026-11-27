// Layer-0 multi-provider read-only agent runner: OS sandbox flags, strict env scrubbing,
// bounded timeout/process-group cleanup, JSON-schema extraction/validation, and output redaction.
import { existsSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { runAgentProcess } from './agent-process.mjs';
import { causeText, readBoundedUtf8 } from './safe-read.mjs';

export const READONLY_PROVIDERS = Object.freeze(['codex', 'claude', 'gemini']);
export const CODEX_DISABLED_FEATURES = Object.freeze([
  'hooks', 'plugins', 'apps', 'browser_use', 'browser_use_external',
  'browser_use_full_cdp_access', 'computer_use', 'multi_agent', 'multi_agent_v2',
  'code_mode', 'code_mode_host',
]);
export const CODEX_TOOL_LOCKOUT_FEATURES = Object.freeze(['shell_tool', 'unified_exec']);
export const GEMINI_DENY_ALL_POLICY = '[[rule]]\ntoolName = "*"\ndecision = "deny"\npriority = 900\n';

const MAX_TIMER_MS = 2_147_483_647, DEFAULT_TIMEOUT_MS = 120_000, DEFAULT_MAX_BYTES = 262_144;
const STRIPPED_ENV_RE = /^(?:GH_.*|GITHUB_(?:.*TOKEN.*|PAT|APP_.*)|PDD_.*TOKEN.*|NPM_TOKEN|NODE_AUTH_TOKEN|HF_TOKEN|SLACK_.*TOKEN.*|AWS_SECRET.*|AWS_SESSION_TOKEN|AWS_ACCESS_KEY_ID|OPENAI_API_KEY|AZURE_OPENAI_API_KEY|CODEX_API_KEY|ANTHROPIC_API_KEY|ANTHROPIC_AUTH_TOKEN|GOOGLE_APPLICATION_CREDENTIALS|SSH_AUTH_SOCK|DATABASE_PASSWORD|PDD_AUTOPILOT_CONTEXT|PDD_AGENT_SESSION|HERDR_.*|CLAUDECODE|CLAUDE_CODE_.*|CLAUDE_PID|CODEX_THREAD_ID|CODEX_SANDBOX.*|GEMINI_CLI_SESSION.*|AGY_SESSION.*|BASH_ENV)$/i;
const GEMINI_KEY_RE = /^(?:GEMINI_API_KEY|GOOGLE_API_KEY)$/i;
const SECRET_ENV_NAME_RE = /(?:^|_)(?:token|secret|password|passwd|credential|authorization|cookie|api[_-]?key|key)$/i;
const URL_SECRET_PARAM_RE = /token|password|secret|api[_-]?key|authorization|cookie|credential|^(?:key|auth|signature)$/i;

export function normalizeReadonlyProvider(provider, { fallback = 'codex', strict = false } = {}) {
  if (provider === undefined || provider === null || provider === '') return fallback;
  const normalized = String(provider).trim().toLowerCase();
  if (READONLY_PROVIDERS.includes(normalized)) return normalized;
  if (strict) throw new Error(`Unsupported read-only agent provider "${provider}". Choose one of: ${READONLY_PROVIDERS.join(', ')}.`);
  return fallback;
}

function validateModel(model) {
  if (model === undefined || model === null || model === '') return null;
  if (typeof model !== 'string' || model !== model.trim() || /^-|[\x00-\x1f\x7f]/.test(model)) {
    throw new Error('Invalid model name: must be nonblank without control characters or a leading dash.');
  }
  return model;
}

export function scrubReadonlyEnv(env = {}, { provider = null, keepKeys = [], extraStrip = [] } = {}) {
  const keepSet = new Set(keepKeys), keepGeminiKeys = String(provider ?? '').trim().toLowerCase() === 'gemini', out = {};
  for (const [key, value] of Object.entries(env ?? {})) {
    if (value === undefined) continue;
    if (!keepSet.has(key) && (STRIPPED_ENV_RE.test(key) || (!keepGeminiKeys && GEMINI_KEY_RE.test(key))
      || extraStrip.some(r => (r instanceof RegExp ? r.test(key) : r === key)))) continue;
    out[key] = value;
  }
  return out;
}

export function collectEnvSecrets(env = {}, extraSecrets = []) {
  const values = new Set();
  for (const s of extraSecrets ?? []) if (typeof s === 'string' && s.length > 0) values.add(s);
  for (const [key, val] of Object.entries(env ?? {})) {
    if (SECRET_ENV_NAME_RE.test(key) && typeof val === 'string' && val.length > 0) values.add(val);
  }
  return [...values].sort((a, b) => b.length - a.length);
}

export function redactReadonlyOutput(value, { env = {}, secrets = [] } = {}) {
  let text = String(value ?? '');
  for (const secret of collectEnvSecrets(env, secrets)) {
    if (secret && text.includes(secret)) text = text.split(secret).join('[redacted]');
  }
  text = text.replace(/https?:\/\/[^\s"'<>]+/g, raw => {
    try {
      const url = new URL(raw);
      let changed = false;
      if (url.username || url.password) { url.username = ''; url.password = ''; changed = true; }
      for (const key of [...url.searchParams.keys()]) {
        if (URL_SECRET_PARAM_RE.test(key)) { url.searchParams.set(key, '[redacted]'); changed = true; }
      }
      return changed ? url.href : raw;
    } catch { return raw.replace(/(https?:\/\/)[^\s/@]+(?::[^\s/@]*)?@/gi, '$1[redacted]@'); }
  });
  return text
    .replace(/-----BEGIN [^-]*PRIVATE KEY-----[\s\S]*?(?:-----END [^-]*PRIVATE KEY-----|$)/g, '[redacted]')
    .replace(/\b(authorization)["']?\s*[:=]\s*[^\r\n]+/gi, '$1=[redacted]')
    .replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,}|pddg_[A-Za-z0-9_-]{12,}|rt_[A-Za-z0-9_.-]{12,}|eyJ[A-Za-z0-9_-]+\.eyJ[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+|AIza[A-Za-z0-9_-]+|ya29\.[A-Za-z0-9_.-]+)\b/g, '[redacted]')
    .replace(/\b(?:Bearer|Basic)\s+\S+/gi, '[redacted]')
    .replace(/\b(key|token|password|secret|api[_-]?key|authorization|cookie|credential)["']?\s*[:=]\s*(?:"(?:\\.|[^"\\])*(?:"|$)|'(?:\\.|[^'\\])*(?:'|$)|[^\s,;]+)/gi, '$1=[redacted]')
    .replace(/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g, '');
}

export function buildReadonlyAgentArgs({
  provider = 'codex', command = null, model = null, tools = 'Read,Glob,Grep', disableTools = false,
  outputFile = null, jsonSchema = null, ignoreRules = true, outputFormat = 'json',
  includeDirs = [], adminPolicy = null, sandbox = true,
} = {}) {
  const kind = normalizeReadonlyProvider(provider, { strict: true }), cleanModel = validateModel(model);
  const bin = typeof command === 'string' && command.trim() ? command.trim() : kind;
  const cleanDirs = (Array.isArray(includeDirs) ? includeDirs : []).filter(d => typeof d === 'string' && d.trim() && !/[\x00-\x1f\x7f]/.test(d));
  const cleanPolicy = typeof adminPolicy === 'string' && adminPolicy.trim() && !/[\x00-\x1f\x7f]/.test(adminPolicy) ? adminPolicy.trim() : null;

  if (kind === 'codex') {
    const disabled = disableTools ? [...CODEX_DISABLED_FEATURES, ...CODEX_TOOL_LOCKOUT_FEATURES] : CODEX_DISABLED_FEATURES;
    return {
      provider: kind, command: bin,
      args: [
        'exec', '--sandbox', 'read-only', '--skip-git-repo-check', '--ephemeral', '--color', 'never',
        ...(ignoreRules ? ['--ignore-rules'] : []),
        '-c', 'approval_policy="never"', '-c', 'web_search="disabled"', '-c', 'mcp_servers={}',
        ...disabled.flatMap(name => ['-c', `features.${name}=false`]),
        ...(cleanModel ? ['--model', cleanModel] : []),
        ...(outputFile ? ['--output-last-message', outputFile] : []), '--', '-',
      ],
    };
  }
  if (kind === 'claude') {
    const schemaStr = jsonSchema ? (typeof jsonSchema === 'string' ? jsonSchema : JSON.stringify(jsonSchema)) : null;
    return {
      provider: kind, command: bin,
      args: [
        '-p', '--safe-mode', '--permission-mode', 'plan', '--tools', disableTools ? '' : String(tools ?? 'Read,Glob,Grep'),
        '--permission-prompts', 'none', '--strict-mcp-config', '--no-chrome', '--no-session-persistence',
        '--output-format', outputFormat || 'json', ...(schemaStr ? ['--json-schema', schemaStr] : []),
        ...cleanDirs.flatMap(dir => ['--add-dir', dir]), ...(cleanModel ? ['--model', cleanModel] : []),
      ],
    };
  }
  return {
    provider: kind, command: bin,
    args: [
      '-p', '', '--output-format', outputFormat || 'json', ...(sandbox ? ['--sandbox'] : []),
      '--approval-mode', 'plan', '--extensions', 'none', '--allowed-mcp-server-names', 'pdd-disabled-none',
      ...cleanDirs.flatMap(dir => ['--include-directories', dir]),
      ...(cleanPolicy ? ['--admin-policy', cleanPolicy] : []), ...(cleanModel ? ['--model', cleanModel] : []),
    ],
  };
}

function collectFencedBlocksLinear(text, maxBlocks = 16) {
  const raw = String(text ?? ''), blocks = [];
  for (let pos = 0; pos < raw.length && blocks.length < maxBlocks;) {
    const open = raw.indexOf('```', pos);
    if (open < 0) break;
    let bodyStart = open + 3;
    if (raw.slice(bodyStart, bodyStart + 4).toLowerCase() === 'json') bodyStart += 4;
    while (bodyStart < raw.length && ' \t\r\n'.includes(raw[bodyStart])) bodyStart += 1;
    const close = raw.indexOf('```', bodyStart);
    if (close < 0) break;
    blocks.push(raw.slice(bodyStart, close).trim());
    pos = close + 3;
  }
  return blocks;
}

function scanBalancedJsonObjects(text, maxObjects = 16) {
  const out = [];
  let depth = 0, start = -1, inStr = false, esc = false;
  for (let i = 0; i < text.length && out.length < maxObjects; i += 1) {
    const ch = text[i];
    if (inStr) { if (esc) esc = false; else if (ch === '\\') esc = true; else if (ch === '"') inStr = false; continue; }
    if (ch === '"') { if (depth > 0) inStr = true; continue; }
    if (ch === '{') { if (depth === 0) start = i; depth += 1; }
    else if (ch === '}' && depth > 0) { depth -= 1; if (depth === 0 && start >= 0) { out.push(text.slice(start, i + 1)); start = -1; } }
  }
  return out;
}

export const extractFirstFencedBlockLinear = text => collectFencedBlocksLinear(text, 1)[0] ?? null;

function jsonCandidates(rawText) {
  const text = String(rawText ?? '').trim();
  if (!text) return [];
  const out = [...collectFencedBlocksLinear(text), text, ...scanBalancedJsonObjects(text)];
  const firstBrace = text.indexOf('{'), lastBrace = text.lastIndexOf('}');
  if (firstBrace >= 0 && lastBrace > firstBrace) out.push(text.slice(firstBrace, lastBrace + 1));
  return [...new Set(out.filter(Boolean))];
}

function parsePlainObject(text) {
  try { const v = JSON.parse(text); return v && typeof v === 'object' && !Array.isArray(v) ? v : null; } catch { return null; }
}

function unwrapEnvelope(obj, accept) {
  if (Object.hasOwn(obj, 'structured_output') && obj.structured_output && typeof obj.structured_output === 'object' && !Array.isArray(obj.structured_output)) {
    if (!accept || accept(obj.structured_output)) return obj.structured_output;
  }
  const keys = accept ? ['structured_output', 'output', 'result', 'response', 'text', 'message']
    : ['result', 'response', ...(Object.keys(obj).length === 1 ? ['output', 'text', 'message'] : [])];
  for (const key of keys) {
    if (!Object.hasOwn(obj, key)) continue;
    const val = obj[key];
    if (accept && val && typeof val === 'object' && !Array.isArray(val) && accept(val)) return val;
    if (typeof val === 'string' && val.trim()) {
      for (const cand of jsonCandidates(val)) {
        const inner = parsePlainObject(cand);
        if (inner && (!accept || accept(inner))) return inner;
      }
    }
  }
  return null;
}

export function extractJsonObject(rawText, { unwrapProviderEnvelope = true, accept = null } = {}) {
  for (const cand of jsonCandidates(rawText)) {
    const obj = parsePlainObject(cand);
    if (!obj) continue;
    if (accept) {
      if (accept(obj)) return obj;
      if (unwrapProviderEnvelope) { const inner = unwrapEnvelope(obj, accept); if (inner) return inner; }
      continue;
    }
    if (unwrapProviderEnvelope) { const inner = unwrapEnvelope(obj, null); if (inner) return inner; }
    return obj;
  }
  return null;
}

export function validateJsonAgainstSchema(value, schema, path = '$') {
  if (!schema || typeof schema !== 'object') return { ok: true, errors: [] };
  const errors = [];
  const check = (val, spec, loc, errList) => {
    if (!spec || typeof spec !== 'object') return;
    if (Array.isArray(spec.anyOf)) {
      const ok = spec.anyOf.some(branch => { const b = []; check(val, branch, loc, b); return b.length === 0; });
      if (!ok) { errList.push(`${loc}: value did not match anyOf`); return; }
    }
    if (Object.hasOwn(spec, 'const') && JSON.stringify(val) !== JSON.stringify(spec.const)) { errList.push(`${loc}: value must equal ${JSON.stringify(spec.const)}`); return; }
    if (Array.isArray(spec.enum) && !spec.enum.includes(val)) { errList.push(`${loc}: value must be one of ${JSON.stringify(spec.enum)}`); return; }
    if (spec.type) {
      const types = Array.isArray(spec.type) ? spec.type : [spec.type];
      const okType = types.some(t => (t === 'null' ? val === null : t === 'array' ? Array.isArray(val) : t === 'object' ? Boolean(val) && typeof val === 'object' && !Array.isArray(val) : t === 'integer' ? Number.isInteger(val) : t === 'number' ? typeof val === 'number' && Number.isFinite(val) : typeof val === t));
      if (!okType) { errList.push(`${loc}: expected ${types.join('|')}`); return; }
    }
    if (typeof val === 'string') {
      if (Number.isInteger(spec.minLength) && val.length < spec.minLength) errList.push(`${loc}: string length < ${spec.minLength}`);
      if (Number.isInteger(spec.maxLength) && val.length > spec.maxLength) errList.push(`${loc}: string length > ${spec.maxLength}`);
      if (typeof spec.pattern === 'string') {
        try { if (!new RegExp(spec.pattern).test(val)) errList.push(`${loc}: string does not match pattern ${spec.pattern}`); }
        catch { errList.push(`${loc}: invalid schema pattern`); }
      }
    }
    if (typeof val === 'number') {
      if (typeof spec.minimum === 'number' && val < spec.minimum) errList.push(`${loc}: value < ${spec.minimum}`);
      if (typeof spec.maximum === 'number' && val > spec.maximum) errList.push(`${loc}: value > ${spec.maximum}`);
    }
    if (Array.isArray(val)) {
      if (Number.isInteger(spec.minItems) && val.length < spec.minItems) errList.push(`${loc}: array length < ${spec.minItems}`);
      if (spec.items) val.forEach((item, idx) => check(item, spec.items, `${loc}[${idx}]`, errList));
    }
    if (val && typeof val === 'object' && !Array.isArray(val)) {
      for (const req of spec.required ?? []) if (!Object.hasOwn(val, req)) errList.push(`${loc}.${req}: required property missing`);
      const props = spec.properties && typeof spec.properties === 'object' ? spec.properties : null;
      if (props) {
        for (const [k, propSpec] of Object.entries(props)) if (Object.hasOwn(val, k)) check(val[k], propSpec, `${loc}.${k}`, errList);
        if (spec.additionalProperties === false) for (const k of Object.keys(val)) if (!Object.hasOwn(props, k)) errList.push(`${loc}.${k}: unexpected property`);
      }
    }
  };
  check(value, schema, path, errors);
  return { ok: errors.length === 0, errors };
}

export async function runReadonlyAgent({
  provider = 'codex', command = null, model = null, prompt = '', cwd = process.cwd(), env = process.env,
  timeoutMs = DEFAULT_TIMEOUT_MS, maxBytes = DEFAULT_MAX_BYTES, signal, jsonSchema = null,
  parseJson = Boolean(jsonSchema), acceptJson = null, tools = 'Read,Glob,Grep', disableTools = false,
  ignoreRules = true, outputFormat = 'json', includeDirs = [], adminPolicy = null, sandbox = true, secrets = [],
} = {}, ports = {}) {
  const redact = text => redactReadonlyOutput(text, { env, secrets });
  const reply = (fields, inv = { provider: String(provider ?? ''), command: null, args: [] }) => ({
    provider: inv.provider, command: inv.command, args: inv.args, ok: false, code: null,
    rawText: '', parsed: null, schemaErrors: [], stdout: '', stderr: '', error: null, ...fields,
  });

  let kind;
  try { kind = normalizeReadonlyProvider(provider, { strict: true }); validateModel(model); }
  catch (err) { return reply({ error: redact(err?.message ?? 'invalid read-only agent configuration') }); }

  const boundedTimeout = Math.min(MAX_TIMER_MS, Math.max(1, Number.isFinite(timeoutMs) ? Math.round(timeoutMs) : DEFAULT_TIMEOUT_MS));
  const boundedBytes = Math.max(1024, Number.isInteger(maxBytes) ? maxBytes : DEFAULT_MAX_BYTES);
  const childEnv = scrubReadonlyEnv(env, { provider: kind });
  const run = typeof ports.run === 'function' ? ports.run : runAgentProcess;

  const needTemp = kind === 'codex' || disableTools;
  const tempDir = needTemp ? mkdtempSync(join(tmpdir(), 'pdd-readonly-agent-')) : null;
  try {
    const outputFile = kind === 'codex' && tempDir ? resolve(tempDir, 'last-message.json') : null;
    let effectivePolicy = adminPolicy;
    if (kind === 'gemini' && disableTools && !effectivePolicy && tempDir) {
      effectivePolicy = resolve(tempDir, 'gemini-deny-all.toml');
      writeFileSync(effectivePolicy, GEMINI_DENY_ALL_POLICY, { mode: 0o600 });
    }
    let childCwd = cwd;
    if (disableTools && tempDir) { childCwd = resolve(tempDir, 'work'); mkdirSync(childCwd, { mode: 0o700 }); }
    const inv = buildReadonlyAgentArgs({
      provider: kind, command, model, tools, disableTools, outputFile, jsonSchema,
      ignoreRules, outputFormat, includeDirs, adminPolicy: effectivePolicy, sandbox,
    });

    let result;
    try {
      result = await run(inv.command, inv.args, { cwd: childCwd, env: childEnv, input: String(prompt ?? ''), signal, timeoutMs: boundedTimeout, maxBytes: boundedBytes });
    } catch (error) {
      return reply({ stdout: redact(error?.stdout ?? ''), stderr: redact(error?.stderr ?? ''), error: redact(causeText(error?.message ?? error)) || 'read-only agent process failed' }, inv);
    }

    let fileReply = '';
    if (outputFile && existsSync(outputFile)) { try { fileReply = readBoundedUtf8(outputFile, { maxBytes: boundedBytes, noFollow: true }); } catch {} }
    const rawStdout = String(result?.stdout ?? ''), rawStderr = String(result?.stderr ?? '');
    const stdout = redact(rawStdout), stderr = redact(rawStderr), rawText = redact(fileReply.trim() ? fileReply : rawStdout);
    const code = Number.isInteger(result?.code) ? result.code : 1;

    if (code !== 0 && !fileReply.trim()) {
      return reply({ code, rawText, stdout, stderr, error: redact(causeText(rawStderr || rawStdout || `exit code ${code}`)) }, inv);
    }

    let parsed = null;
    if (parseJson || jsonSchema || acceptJson) {
      parsed = extractJsonObject(fileReply, { accept: acceptJson }) ?? extractJsonObject(rawStdout, { accept: acceptJson });
      if (!parsed) return reply({ code, rawText, stdout, stderr, schemaErrors: ['unreadable JSON response'], error: 'unreadable JSON response' }, inv);
      if (jsonSchema) {
        const validation = validateJsonAgainstSchema(parsed, jsonSchema);
        if (!validation.ok) return reply({ code, rawText, parsed, stdout, stderr, schemaErrors: validation.errors, error: `JSON schema validation failed: ${validation.errors[0]}` }, inv);
      }
    }
    return reply({ ok: true, code, rawText, parsed, stdout, stderr }, inv);
  } finally {
    if (tempDir) { try { rmSync(tempDir, { recursive: true, force: true }); } catch {} }
  }
}
