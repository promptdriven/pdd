// Generated from prompts/cli/autopilot-validator.prompt.md (sha256: 691dd6196bed4cd3f73c6e54357b81dbbd926f01249066f198c14749055ad53b).
// Delegates prompt metadata & file-owner parsing to core modules.
import { headerPrompts, promptClaims } from '../../file-owner.mjs';
import { extractRuntimeInterfaceObjects, findFrontmatterRange } from '../../core/lint/prompt-metadata.mjs';

export const MIN_REALISTIC_PAYLOAD_BYTES = 4096;
export const REAL_HOST_FAILURE_CLASSES = Object.freeze([
  'nested-sandbox',
  'host-tty-ownership',
  'multi-turn-cli-state',
  'full-size-payload',
]);

export const REAL_HOST_CLASS_SET = new Set(REAL_HOST_FAILURE_CLASSES);
export const REAL_HOST_CLASS_LABELS = Object.freeze({
  'nested-sandbox': 'nested OS sandbox execution (real child process inside sandbox, not mocked argv-prefix test)',
  'host-tty-ownership': 'real host device/TTY ownership (/dev/tty UID/permissions on host kernel, not mocked TTY helper)',
  'multi-turn-cli-state': 'multi-turn real CLI state side effects (Turn 1 -> Turn 2 state/containment check, not single-turn stub)',
  'full-size-payload': `full-size realistic payload handling (> ${MIN_REALISTIC_PAYLOAD_BYTES} bytes un-truncated payload, not tiny synthetic fixture)`,
});

export const REAL_E2E_KINDS = new Set([
  'subprocess-cli',
  'local-server-or-db',
  'browser-playwright',
  'live-binding',
  'real-host-smoke',
  'real-execution',
]);

export const NON_PRODUCTION_DIR_RE = /^(?:test|tests|__tests__|spec|fixtures|examples|prompts|user_stories|docs)\//i;
const DOC_FILE_RE = /(?:^docs\/|\.(?:txt|rst)$|(?:^|\/)(?:license|changelog)[^/]*$)/i;

const tokenMatch = (pattern) => new RegExp(`(?:^|[^a-z0-9])(?:${pattern})(?:$|[^a-z0-9])`, 'i');
const CLI_TOKEN_RE = tokenMatch('cli');
const API_TOKEN_RE = tokenMatch('server|router|api|http|https|ws|websocket|graphql|grpc');
const DB_TOKEN_RE = tokenMatch('postgres|postgresql|mysql|sqlite|mongo|mongodb|redis|db');
const EXTERNAL_TOKEN_RE = tokenMatch('gcloud|gcp|aws|azure|stripe|docker|kubernetes|k8s|oauth|auth|webhook|terraform');
const OS_BOUNDARY_TOKEN_RE = tokenMatch('sandbox|seatbelt|seccomp|landlock|bwrap|bubblewrap|chroot|cgroup|tty|pty|termios|ioctl|subprocess|child[-_]?process|spawn|posix|syscall|kernel|daemon|ipc|unix[-_]?socket|os[-_]?signal');

const REAL_HOST_CLASS_PATH_RULES = [
  { id: 'nested-sandbox', re: tokenMatch('sandbox|seatbelt|seccomp|landlock|bwrap|bubblewrap|chroot|cgroup') },
  { id: 'host-tty-ownership', re: tokenMatch('tty|pty|termios|ioctl') },
  { id: 'multi-turn-cli-state', re: tokenMatch('cli[-_]?session|cli[-_]?wrapper|session[-_]?state|containment') },
  { id: 'full-size-payload', re: tokenMatch('payload|preview|truncat(?:e|ed|es|ing|ion)|framing|wire[-_]?frame|stream[-_]?buffer') },
];

const SURFACE_MATCHERS = [
  {
    surface: 'cli',
    test: (norm, base) => /^(?:bin|cli|cmd|scripts)\//i.test(norm) || /\.sh$/i.test(norm) || CLI_TOKEN_RE.test(base),
  },
  {
    surface: 'api-server',
    test: (norm, base) => /^(?:api|server|routes|handlers|controllers)\//i.test(norm) || API_TOKEN_RE.test(base),
  },
  {
    surface: 'database',
    test: (norm, base) => /^(?:db|database|migrations|prisma|sql)\//i.test(norm) || /\.sql$/i.test(norm) || DB_TOKEN_RE.test(base),
  },
  {
    surface: 'web-ui',
    test: (norm) => /^(?:web|ui|frontend|pages|components|views|app)\//i.test(norm)
      || /\.(?:jsx|tsx|vue|svelte|html|css)$/i.test(norm)
      || /\.ui\.svg$/i.test(norm),
  },
  {
    surface: 'external-tool',
    test: (norm, base) => /^dockerfile(?:\.|$)/i.test(base)
      || base.startsWith('docker-compose')
      || EXTERNAL_TOKEN_RE.test(norm),
  },
  {
    surface: 'os-boundary',
    test: (norm, base) => /^(?:os|sandbox|tty|pty|subprocess)\//i.test(norm)
      || OS_BOUNDARY_TOKEN_RE.test(base),
  },
];

const SURFACE_TO_PROOF_KIND = {
  cli: 'subprocess-cli',
  'api-server': 'local-server-or-db',
  database: 'local-server-or-db',
  'web-ui': 'browser-playwright',
  'external-tool': 'live-binding',
  'os-boundary': 'real-host-smoke',
  'native-only': 'real-host-smoke',
};

const FM_NATIVE_KIND_LINE_RE = /^[ \t]*kind[ \t]*:[ \t]*(?:['"])?native-only(?:['"])?[ \t]*(?:#[^\r\n]*)?$/i;
const FM_REASON_LINE_RE = /^[ \t]*reason[ \t]*:[ \t]*(.+)$/i;

export const cleanText = (value) => (typeof value === 'string' ? value.trim() : '');
export const cleanTool = (value) => cleanText(value).toLowerCase();

export function normalizePath(value) {
  const raw = cleanText(value).replace(/\\/g, '/').replace(/\/+/g, '/');
  if (!raw) return '';
  const isAbs = raw.startsWith('/');
  const out = [];
  for (const part of raw.split('/')) {
    if (!part || part === '.') continue;
    if (part === '..') {
      if (out.length && out[out.length - 1] !== '..') out.pop();
      else if (!isAbs) out.push('..');
    } else {
      out.push(part);
    }
  }
  const joined = out.join('/');
  return isAbs ? `/${joined}` : joined;
}

export const isCanonicalRepoPath = (value) => typeof value === 'string'
  && value.length > 0
  && value.length <= 1000
  && !value.startsWith('/')
  && !/^[A-Za-z]:/.test(value)
  && !/[\\\x00-\x1f\x7f]/.test(value)
  && !value.split('/').some((part) => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

export function isDocPath(norm) {
  if (/\.prompt\.md$/i.test(norm) || /^user_stories\//i.test(norm)) return false;
  return /\.md$/i.test(norm) || DOC_FILE_RE.test(norm);
}

export function classifyProductionPathSurfaces(rawPath) {
  const norm = normalizePath(rawPath);
  if (!norm) return [];
  const lower = norm.toLowerCase();
  if (isDocPath(lower)) return ['docs'];
  if (NON_PRODUCTION_DIR_RE.test(lower)) return [];
  const base = lower.split('/').pop() || lower;
  const matched = [];
  for (const { surface, test } of SURFACE_MATCHERS) {
    if (test(lower, base)) matched.push(surface);
  }
  if (!matched.length) matched.push('runtime-code');
  return matched;
}

/**
 * Canonical module stem for matching production targets across imports and tests (e.g., api/orders.mjs -> api/orders).
 */
export function canonicalTargetPath(rawPath) {
  const norm = normalizePath(rawPath).toLowerCase();
  if (!norm) return '';
  return norm.replace(/\.(?:[cm]?[jt]sx?|py|go|rs|rb|java|kt|cs|php|swift|sh|sql|vue|svelte|html|css)$/i, '');
}

export function resolveRelativeTarget(fromPath, spec) {
  const cleanSpec = normalizePath(spec);
  if (!cleanSpec) return '';
  if (!spec.startsWith('.')) return cleanSpec;
  const resolved = normalizePath(fromPath).split('/').slice(0, -1);
  for (const part of spec.replace(/\\/g, '/').split('/')) {
    if (!part || part === '.') continue;
    if (part === '..') resolved.pop();
    else resolved.push(part);
  }
  return normalizePath(resolved.join('/'));
}

function parseNativeOnlyPromptMeta(raw) {
  const text = String(raw ?? '');
  if (!text) return null;
  const fm = findFrontmatterRange(text);
  const bodyOffset = fm ? fm.end : 0;
  if (fm) {
    let isNative = false;
    let reason = '';
    for (const line of text.slice(fm.bodyStart, fm.bodyEnd).split(/\r?\n/)) {
      if (!isNative && FM_NATIVE_KIND_LINE_RE.test(line)) isNative = true;
      else if (!reason) {
        const m = FM_REASON_LINE_RE.exec(line);
        if (m) reason = m[1].trim().replace(/^['"]|['"]$/g, '');
      }
    }
    if (isNative) return { nativeOnly: true, reason, bodyOffset };
  }
  for (const obj of extractRuntimeInterfaceObjects(text)) {
    if (obj.kind === 'native-only') {
      return { nativeOnly: true, reason: cleanText(obj.reason), bodyOffset };
    }
  }
  return null;
}

function extractHeaderRefsViaOwner(rawContent) {
  if (!rawContent) return [];
  const buf = Buffer.isBuffer(rawContent) ? rawContent : Buffer.from(String(rawContent), 'utf8');
  const headText = buf.subarray(0, 4096).toString('utf8').replace(/--!>(?=[ \t]*(?:\r?\n|$))/g, '-->');
  const refs = [];
  const seen = new Set();
  for (const ref of headerPrompts(headText)) {
    const norm = normalizePath(ref);
    const key = norm.toLowerCase();
    if (norm && !seen.has(key)) {
      seen.add(key);
      refs.push(norm);
    }
  }
  return refs;
}

/**
 * Resolve which changed production modules are owned by `kind: native-only` prompts
 * via `pdd-bindings.json`, `Generated from` / `Prompt:` headers, or opening-sentence prose claims.
 */
export function detectNativeOnlyModules({
  changedFiles = [],
  promptFiles = [],
  bindings = null,
  fileHeads = [],
} = {}) {
  const nativePromptsByKey = new Map();
  const rawPrompts = Array.isArray(promptFiles)
    ? promptFiles
    : (promptFiles && typeof promptFiles === 'object'
      ? Object.entries(promptFiles).map(([path, content]) => ({ path, content }))
      : []);

  for (const item of rawPrompts) {
    if (!item || typeof item !== 'object') continue;
    const p = normalizePath(item.path);
    if (!p || !p.endsWith('.prompt.md')) continue;
    const meta = parseNativeOnlyPromptMeta(item.content);
    if (!meta?.nativeOnly) continue;
    const body = String(item.content ?? '').slice(meta.bodyOffset, meta.bodyOffset + 65536);
    const claims = promptClaims(p, body).map((c) => normalizePath(c).toLowerCase()).filter(Boolean);
    nativePromptsByKey.set(p.toLowerCase(), {
      path: p,
      reason: meta.reason,
      claims: new Set(claims),
    });
  }

  const bindingMap = new Map();
  if (bindings) {
    let parsed = null;
    if (typeof bindings === 'string') {
      try { parsed = JSON.parse(bindings); } catch { parsed = null; }
    } else if (typeof bindings === 'object') {
      parsed = bindings;
    }
    if (parsed && Array.isArray(parsed.modules)) {
      for (const entry of parsed.modules) {
        if (!entry || typeof entry !== 'object') continue;
        const mod = normalizePath(entry.module).toLowerCase();
        const prmKey = normalizePath(entry.prompt).toLowerCase();
        if (mod && prmKey && nativePromptsByKey.has(prmKey)) {
          bindingMap.set(mod, nativePromptsByKey.get(prmKey));
        }
      }
    }
  }

  const headMap = new Map();
  if (Array.isArray(fileHeads)) {
    for (const entry of fileHeads) {
      if (!entry || typeof entry !== 'object') continue;
      const p = normalizePath(entry.path).toLowerCase();
      if (p && typeof entry.content === 'string') headMap.set(p, entry.content);
    }
  } else if (fileHeads instanceof Map) {
    for (const [k, v] of fileHeads.entries()) {
      const p = normalizePath(k).toLowerCase();
      if (p && typeof v === 'string') headMap.set(p, v);
    }
  } else if (fileHeads && typeof fileHeads === 'object') {
    for (const [k, v] of Object.entries(fileHeads)) {
      const p = normalizePath(k).toLowerCase();
      if (p && typeof v === 'string') headMap.set(p, v);
    }
  }

  const proseClaimsByModule = new Map();
  for (const entry of nativePromptsByKey.values()) {
    for (const claimKey of entry.claims) {
      if (!proseClaimsByModule.has(claimKey)) proseClaimsByModule.set(claimKey, entry);
    }
  }

  const matches = [];
  const moduleSet = new Set();
  const changedList = Array.isArray(changedFiles) ? [...new Set(changedFiles.map(normalizePath).filter(Boolean))].sort() : [];
  for (const file of changedList) {
    const lower = file.toLowerCase();
    if (isDocPath(lower) || NON_PRODUCTION_DIR_RE.test(lower)) continue;
    let promptEntry = null;
    let source = null;
    if (bindingMap.has(lower)) {
      promptEntry = bindingMap.get(lower);
      source = 'binding';
    } else if (headMap.has(lower)) {
      const refs = extractHeaderRefsViaOwner(headMap.get(lower));
      const matchedKey = refs.map((r) => r.toLowerCase()).find((k) => nativePromptsByKey.has(k));
      if (matchedKey) {
        promptEntry = nativePromptsByKey.get(matchedKey);
        source = 'header';
      }
    }
    if (!promptEntry && proseClaimsByModule.has(lower)) {
      promptEntry = proseClaimsByModule.get(lower);
      source = 'prose';
    }
    if (promptEntry) {
      moduleSet.add(file);
      matches.push({ module: file, prompt: promptEntry.path, source, reason: promptEntry.reason });
    }
  }

  return {
    nativeOnlyPrompts: [...nativePromptsByKey.values()].map((e) => e.path).sort(),
    nativeOnlyModules: [...moduleSet].sort(),
    matches,
  };
}

/**
 * Classify changed repository paths into validation surfaces and required E2E proof kinds.
 */
export function detectChangedSurfaces({ changedFiles = [], nativeOnlyFiles = [] } = {}) {
  const files = Array.isArray(changedFiles) ? changedFiles.map(normalizePath).filter(Boolean) : [];
  const nativeSet = new Set(Array.isArray(nativeOnlyFiles) ? nativeOnlyFiles.map((f) => normalizePath(f).toLowerCase()).filter(Boolean) : []);
  const surfaceSet = new Set();
  const matchedNativeFiles = new Set();
  const realHostClassSet = new Set();
  let allDocs = files.length > 0;

  for (const file of files) {
    const lower = file.toLowerCase();
    const fileSurfaces = classifyProductionPathSurfaces(file);
    const isNativeOnlyFile = nativeSet.has(lower) && !isDocPath(lower) && !NON_PRODUCTION_DIR_RE.test(lower);
    if (isNativeOnlyFile) {
      matchedNativeFiles.add(file);
      if (!fileSurfaces.includes('native-only')) fileSurfaces.push('native-only');
    }
    if (!fileSurfaces.length || fileSurfaces.some((s) => s !== 'docs')) allDocs = false;
    for (const s of fileSurfaces) surfaceSet.add(s);
    if (fileSurfaces.includes('os-boundary') || fileSurfaces.includes('native-only') || fileSurfaces.includes('cli')) {
      for (const rule of REAL_HOST_CLASS_PATH_RULES) {
        if (rule.re.test(lower)) realHostClassSet.add(rule.id);
      }
    }
  }

  const surfaces = [...surfaceSet].sort();
  const runtimeSurfaces = surfaces.filter((s) => s !== 'docs');
  const emptyChangedFiles = files.length === 0;
  const docsOnly = allDocs && runtimeSurfaces.length === 0;
  const requiresRealE2e = runtimeSurfaces.length > 0 || emptyChangedFiles;

  const proofKindSet = new Set();
  for (const surface of runtimeSurfaces) {
    if (SURFACE_TO_PROOF_KIND[surface]) proofKindSet.add(SURFACE_TO_PROOF_KIND[surface]);
  }
  if (emptyChangedFiles || (!proofKindSet.size && runtimeSurfaces.includes('runtime-code'))) {
    proofKindSet.add('real-execution');
  }

  return {
    surfaces,
    runtimeSurfaces,
    docsOnly,
    requiresRealE2e,
    requiredProofKinds: [...proofKindSet].sort(),
    nativeOnlyFiles: [...matchedNativeFiles].sort(),
    realHostBoundaryClasses: [...realHostClassSet].sort(),
  };
}
