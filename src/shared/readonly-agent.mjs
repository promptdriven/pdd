// Layer-0 multi-provider read-only agent runner: OS sandbox flags, strict env scrubbing,
// bounded timeout/process-group cleanup, JSON-schema extraction/validation, and output redaction.
import { existsSync, mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { runAgentProcess } from './agent-process.mjs';
import { causeText, readBoundedUtf8 } from './safe-read.mjs';

export const READONLY_PROVIDERS = Object.freeze(['codex', 'claude', 'gemini', 'agy']);
export const CODEX_DISABLED_FEATURES = Object.freeze([
  'hooks', 'plugins', 'apps', 'browser_use', 'browser_use_external',
  'browser_use_full_cdp_access', 'computer_use', 'multi_agent', 'multi_agent_v2',
  'shell_tool', 'unified_exec', 'code_mode', 'code_mode_host',
]);

const MAX_TIMER_MS = 2_147_483_647;
const DEFAULT_TIMEOUT_MS = 120_000;
const DEFAULT_MAX_BYTES = 262_144;
const STRIPPED_ENV_RE = /^(?:GH_.*|GITHUB_(?:.*TOKEN.*|PAT|APP_.*)|PDD_.*TOKEN.*|NPM_TOKEN|AWS_SECRET.*|AWS_SESSION_TOKEN|OPENAI_API_KEY|ANTHROPIC_API_KEY|GEMINI_API_KEY|GOOGLE_API_KEY|PDD_AUTOPILOT_CONTEXT|PDD_AGENT_SESSION|HERDR_.*|CLAUDECODE|CLAUDE_CODE_.*|CLAUDE_PID|CODEX_THREAD_ID|CODEX_SANDBOX.*|GEMINI_CLI_SESSION.*|AGY_SESSION.*|BASH_ENV)$/i;
const SECRET_ENV_NAME_RE = /token|secret|password|passwd|credential|authorization|cookie|api[_-]?key|_key$/i;
const URL_SECRET_PARAM_RE = /token|password|secret|api[_-]?key|authorization|cookie|credential|^(?:key|auth|signature)$/i;

export function normalizeReadonlyProvider(provider, { fallback = 'codex', strict = false } = {}) {
  if (provider === undefined || provider === null || provider === '') return fallback;
  const normalized = String(provider).trim().toLowerCase();
  if (READONLY_PROVIDERS.includes(normalized)) return normalized;
  if (strict) {
    throw new Error(`Unsupported read-only agent provider "${provider}". Choose one of: ${READONLY_PROVIDERS.join(', ')}.`);
  }
  return fallback;
}

function validateModel(model) {
  if (model === undefined || model === null || model === '') return null;
  if (typeof model !== 'string' || model !== model.trim() || /^-|[\x00-\x1f\x7f]/.test(model)) {
    throw new Error('Invalid model name: must be nonblank without control characters or a leading dash.');
  }
  return model;
}

export function scrubReadonlyEnv(env = {}, { keepKeys = [], extraStrip = [] } = {}) {
  const keepSet = new Set(keepKeys);
  const out = {};
  for (const [key, value] of Object.entries(env ?? {})) {
    if (value === undefined) continue;
    if (!keepSet.has(key) && (STRIPPED_ENV_RE.test(key) || extraStrip.some(r => (r instanceof RegExp ? r.test(key) : r === key)))) {
      continue;
    }
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
    } catch {
      return raw.replace(/(https?:\/\/)[^\s/@]+(?::[^\s/@]*)?@/gi, '$1[redacted]@');
    }
  });
  text = text
    .replace(/-----BEGIN [^-]*PRIVATE KEY-----[\s\S]*?(?:-----END [^-]*PRIVATE KEY-----|$)/g, '[redacted]')
    .replace(/\b(authorization)["']?\s*[:=]\s*[^\r\n]+/gi, '$1=[redacted]')
    .replace(/\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,}|pddg_[A-Za-z0-9_-]{12,}|rt_[A-Za-z0-9_.-]{12,}|eyJ[A-Za-z0-9_-]+\.eyJ[A-Za-z0-9_-]+\.[A-Za-z0-9_-]+|AIza[A-Za-z0-9_-]+|ya29\.[A-Za-z0-9_.-]+)\b/g, '[redacted]')
    .replace(/\b(?:Bearer|Basic)\s+\S+/gi, '[redacted]')
    .replace(/\b(key|token|password|secret|api[_-]?key|authorization|cookie|credential)["']?\s*[:=]\s*(?:"(?:\\.|[^"\\])*(?:"|$)|'(?:\\.|[^'\\])*(?:'|$)|[^\s,;]+)/gi, '$1=[redacted]');
  return text.replace(/[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]/g, '');
}

function redactDeep(value, redact) {
  if (typeof value === 'string') return redact(value);
  if (Array.isArray(value)) return value.map(item => redactDeep(item, redact));
  if (value && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, redactDeep(v, redact)]));
  }
  return value;
}

export function buildReadonlyAgentArgs({
  provider = 'codex', command = null, model = null, tools = 'Read,Glob,Grep', disableTools = false,
  outputFile = null, jsonSchema = null, ignoreRules = true, outputFormat = 'json', includeDirs = [], adminPolicy = null,
} = {}) {
  const kind = normalizeReadonlyProvider(provider, { strict: true });
  const cleanModel = validateModel(model);
  const bin = typeof command === 'string' && command.trim() ? command.trim() : kind;
  const cleanDirs = (Array.isArray(includeDirs) ? includeDirs : []).filter(d => typeof d === 'string' && d.trim() && !/[\x00-\x1f\x7f]/.test(d));
  const cleanPolicy = typeof adminPolicy === 'string' && adminPolicy.trim() && !/[\x00-\x1f\x7f]/.test(adminPolicy) ? adminPolicy.trim() : null;

  if (kind === 'codex') {
    return {
      provider: kind, command: bin,
      args: [
        'exec', '--sandbox', 'read-only', '--skip-git-repo-check', '--ephemeral', '--color', 'never',
        ...(ignoreRules ? ['--ignore-rules'] : []),
        '-c', 'approval_policy="never"', '-c', 'web_search="disabled"', '-c', 'mcp_servers={}',
        ...CODEX_DISABLED_FEATURES.flatMap(name => ['-c', `features.${name}=false`]),
        ...(cleanModel ? ['--model', cleanModel] : []),
        ...(outputFile ? ['--output-last-message', outputFile] : []),
        '--', '-',
      ],
    };
  }
  if (kind === 'claude') {
    const schemaStr = jsonSchema ? (typeof jsonSchema === 'string' ? jsonSchema : JSON.stringify(jsonSchema)) : null;
    return {
      provider: kind, command: bin,
      args: [
        '-p', '--safe-mode', '--permission-mode', 'plan',
        '--tools', disableTools ? '' : String(tools ?? 'Read,Glob,Grep'),
        '--permission-prompts', 'none', '--strict-mcp-config', '--no-chrome', '--no-session-persistence',
        '--output-format', outputFormat || 'json',
        ...(schemaStr ? ['--json-schema', schemaStr] : []),
        ...cleanDirs.flatMap(dir => ['--add-dir', dir]),
        ...(cleanModel ? ['--model', cleanModel] : []),
      ],
    };
  }
  if (kind === 'gemini') {
    return {
      provider: kind, command: bin,
      args: [
        '-p', '', '--output-format', outputFormat || 'json',
        '--sandbox', '--approval-mode', 'plan', '--extensions', 'none', '--allowed-mcp-server-names', 'pdd-disabled-none',
        ...cleanDirs.flatMap(dir => ['--include-directories', dir]),
        ...(cleanPolicy ? ['--admin-policy', cleanPolicy] : []),
        ...(cleanModel ? ['--model', cleanModel] : []),
      ],
    };
  }
  return {
    provider: kind, command: bin,
    args: [
      '--input-format', 'text', '--output-format', outputFormat || 'json',
      '--mode', 'plan', '--sandbox', '--disable-slash-commands',
      ...(cleanModel ? ['--model', cleanModel] : []),
    ],
  };
}

export function extractFirstFencedBlockLinear(text) {
  const raw = String(text ?? '');
  const open = raw.indexOf('```');
  if (open < 0) return null;
  let bodyStart = open + 3;
  if (raw.slice(bodyStart, bodyStart + 4).toLowerCase() === 'json') bodyStart += 4;
  while (bodyStart < raw.length && ' \t\r\n'.includes(raw[bodyStart])) bodyStart += 1;
  const close = raw.indexOf('```', bodyStart);
  return close < 0 ? null : raw.slice(bodyStart, close).trim();
}

function tryParseJsonCandidate(rawText, accept) {
  const text = String(rawText ?? '').trim();
  if (!text) return null;
  const candidates = [text];
  const fenced = extractFirstFencedBlockLinear(text);
  if (fenced) candidates.unshift(fenced);
  const firstBrace = text.indexOf('{');
  const lastBrace = text.lastIndexOf('}');
  if (firstBrace >= 0 && lastBrace > firstBrace) candidates.push(text.slice(firstBrace, lastBrace + 1));
  for (const candidate of candidates) {
    try {
      const parsed = JSON.parse(candidate);
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed) && (!accept || accept(parsed))) {
        return parsed;
      }
    } catch {}
  }
  return null;
}

export function extractJsonObject(rawText, { unwrapProviderEnvelope = true, accept = null } = {}) {
  const outer = tryParseJsonCandidate(rawText, null);
  if (!outer) return null;
  if (accept && accept(outer)) return outer;
  if (unwrapProviderEnvelope) {
    for (const key of ['structured_output', 'output', 'result', 'response', 'text', 'message']) {
      if (!Object.hasOwn(outer, key)) continue;
      const val = outer[key];
      if (val && typeof val === 'object' && !Array.isArray(val) && (!accept || accept(val))) return val;
      if (typeof val === 'string' && val.trim()) {
        const nested = tryParseJsonCandidate(val, accept);
        if (nested) return nested;
      }
    }
  }
  return accept ? null : outer;
}

export function validateJsonAgainstSchema(value, schema, path = '$') {
  if (!schema || typeof schema !== 'object') return { ok: true, errors: [] };
  const errors = [];
  const check = (val, spec, loc) => {
    if (!spec || typeof spec !== 'object') return;
    if (Array.isArray(spec.enum) && !spec.enum.includes(val)) {
      errors.push(`${loc}: value must be one of ${JSON.stringify(spec.enum)}`);
      return;
    }
    if (spec.type) {
      const types = Array.isArray(spec.type) ? spec.type : [spec.type];
      const matches = types.some(t => (
        t === 'null' ? val === null
          : t === 'array' ? Array.isArray(val)
          : t === 'object' ? Boolean(val) && typeof val === 'object' && !Array.isArray(val)
          : t === 'integer' ? Number.isInteger(val)
          : t === 'number' ? typeof val === 'number' && Number.isFinite(val)
          : typeof val === t
      ));
      if (!matches) { errors.push(`${loc}: expected ${types.join('|')}`); return; }
    }
    if (typeof val === 'string' && Number.isInteger(spec.minLength) && val.length < spec.minLength) {
      errors.push(`${loc}: string length < ${spec.minLength}`);
    }
    if (typeof val === 'number') {
      if (typeof spec.minimum === 'number' && val < spec.minimum) errors.push(`${loc}: value < ${spec.minimum}`);
      if (typeof spec.maximum === 'number' && val > spec.maximum) errors.push(`${loc}: value > ${spec.maximum}`);
    }
    if (Array.isArray(val)) {
      if (Number.isInteger(spec.minItems) && val.length < spec.minItems) errors.push(`${loc}: array length < ${spec.minItems}`);
      if (spec.items) val.forEach((item, idx) => check(item, spec.items, `${loc}[${idx}]`));
    }
    if (val && typeof val === 'object' && !Array.isArray(val)) {
      for (const req of spec.required ?? []) {
        if (!Object.hasOwn(val, req)) errors.push(`${loc}.${req}: required property missing`);
      }
      const props = spec.properties && typeof spec.properties === 'object' ? spec.properties : null;
      if (props) {
        for (const [k, propSpec] of Object.entries(props)) {
          if (Object.hasOwn(val, k)) check(val[k], propSpec, `${loc}.${k}`);
        }
        if (spec.additionalProperties === false) {
          for (const k of Object.keys(val)) if (!Object.hasOwn(props, k)) errors.push(`${loc}.${k}: unexpected property`);
        }
      }
    }
  };
  check(value, schema, path);
  return { ok: errors.length === 0, errors };
}

export async function runReadonlyAgent({
  provider = 'codex', command = null, model = null, prompt = '', cwd = process.cwd(), env = process.env,
  timeoutMs = DEFAULT_TIMEOUT_MS, maxBytes = DEFAULT_MAX_BYTES, signal, jsonSchema = null,
  parseJson = Boolean(jsonSchema), acceptJson = null, tools = 'Read,Glob,Grep', disableTools = false,
  ignoreRules = true, outputFormat = 'json', includeDirs = [], adminPolicy = null, secrets = [],
} = {}, ports = {}) {
  const kind = normalizeReadonlyProvider(provider, { strict: true });
  const boundedTimeout = Math.min(MAX_TIMER_MS, Math.max(1, Number.isFinite(timeoutMs) ? Math.round(timeoutMs) : DEFAULT_TIMEOUT_MS));
  const boundedBytes = Math.max(1024, Number.isInteger(maxBytes) ? maxBytes : DEFAULT_MAX_BYTES);
  const childEnv = scrubReadonlyEnv(env);
  const redact = text => redactReadonlyOutput(text, { env, secrets });
  const run = typeof ports.run === 'function' ? ports.run : runAgentProcess;

  const tempDir = kind === 'codex' ? mkdtempSync(join(tmpdir(), 'pdd-readonly-agent-')) : null;
  const outputFile = tempDir ? resolve(tempDir, 'last-message.json') : null;
  const inv = buildReadonlyAgentArgs({
    provider: kind, command, model, tools, disableTools, outputFile, jsonSchema, ignoreRules, outputFormat, includeDirs, adminPolicy,
  });
  const reply = fields => ({
    provider: kind, command: inv.command, args: inv.args, ok: false, code: null,
    rawText: '', parsed: null, schemaErrors: [], stdout: '', stderr: '', error: null, ...fields,
  });

  try {
    let result;
    try {
      result = await run(inv.command, inv.args, {
        cwd, env: childEnv, input: String(prompt ?? ''), signal, timeoutMs: boundedTimeout, maxBytes: boundedBytes,
      });
    } catch (error) {
      return reply({
        stdout: redact(error?.stdout ?? ''), stderr: redact(error?.stderr ?? ''),
        error: redact(causeText(error?.message ?? error)) || 'read-only agent process failed',
      });
    }

    let fileReply = '';
    if (outputFile && existsSync(outputFile)) {
      try { fileReply = readBoundedUtf8(outputFile, { maxBytes: boundedBytes, noFollow: true }); } catch {}
    }

    const rawStdout = String(result?.stdout ?? '');
    const rawStderr = String(result?.stderr ?? '');
    const stdout = redact(rawStdout);
    const stderr = redact(rawStderr);
    const rawText = redact(fileReply.trim() ? fileReply : rawStdout);
    const code = Number.isInteger(result?.code) ? result.code : 1;

    if (code !== 0 && !fileReply.trim()) {
      return reply({ code, rawText, stdout, stderr, error: redact(causeText(rawStderr || rawStdout || `exit code ${code}`)) });
    }

    let parsed = null;
    if (parseJson || jsonSchema || acceptJson) {
      const rawParsed = extractJsonObject(fileReply, { accept: acceptJson })
        ?? extractJsonObject(rawStdout, { accept: acceptJson });
      if (!rawParsed) {
        return reply({ code, rawText, stdout, stderr, schemaErrors: ['unreadable JSON response'], error: 'unreadable JSON response' });
      }
      parsed = redactDeep(rawParsed, redact);
      if (jsonSchema) {
        const validation = validateJsonAgainstSchema(parsed, jsonSchema);
        if (!validation.ok) {
          return reply({
            code, rawText, parsed, stdout, stderr, schemaErrors: validation.errors,
            error: `JSON schema validation failed: ${validation.errors[0]}`,
          });
        }
      }
    }

    return reply({ ok: true, code, rawText, parsed, stdout, stderr });
  } finally {
    if (tempDir) {
      try { rmSync(tempDir, { recursive: true, force: true }); } catch {}
    }
  }
}
