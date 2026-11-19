// Generated from prompts/cli/autopilot-intake-preflight.prompt.md (sha256: 733a48b6d7f68913a0a9f77d6c53a1842869447585801a2a7475590a725786b4).

export const PREFLIGHT_REASON_CODES = Object.freeze([
  'cross_repo',
  'human_decision',
  'unverifiable_boundary',
]);

const REASON_CODE_SET = new Set(PREFLIGHT_REASON_CODES);

const DEFAULT_CAPABILITIES = Object.freeze({
  localTests: true,
  liveExternalServices: false,
  productionCredentials: false,
  humanManualQa: false,
  availableRecipes: Object.freeze([]),
});

const DEFAULT_LOCAL_TOP_DIRS = new Set([
  'src', 'prompts', 'test', 'tests', 'bin', 'scripts', 'docs', 'user_stories', 'skills',
]);

const GENERIC_ROOT_FILES = new Set([
  'package.json', 'package-lock.json', 'pnpm-lock.yaml', 'yarn.lock', 'bun.lock', 'bun.lockb',
  'readme.md', 'agents.md', 'claude.md', 'tsconfig.json', 'pyproject.toml', 'cargo.toml',
  'go.mod', '.gitignore', 'license',
]);

const PATH_PREFIX_RE = /^(?:src|prompts|test|tests|scripts|bin|docs|skills|user_stories|packages|apps|services|extensions|pdd_cloud|pdd-workflow|pdd_workflow|prompt-runtime|runtime-client|github_pdd_app|server|worker|api|lib|\.github)\/[A-Za-z0-9_./-]+$/;
const PATH_EXT_RE = /^(?:[A-Za-z0-9_.-]+\/)*[A-Za-z0-9_.-]+\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|java|kt|swift|sh|md|json|ya?ml|toml|sql|css|html)$/;
const IGNORE_SLASH_RE = /^(?:origin|refs|application|text|image|audio|video|multipart|http|https|read|write|pass|fail|true|false|yes|no|auto|observe|before|after|stdout|stderr|input|output|client|server)\//i;

const SIBLINGS = Object.freeze([
  {
    canonical: 'pdd_cloud',
    short: 'pdd_cloud',
    aliases: ['pdd_cloud', 'pdd-cloud'],
    roots: ['pdd_cloud'],
    prefixes: ['pdd_cloud/'],
    mentionRe: /\bpdd[_-]cloud\b(?!#\d|\.(?:mjs|cjs|js|ts|py|md|json))/i,
    framedRe: /(?:^\s*\[?pdd[_-]cloud\]?\s*[:\-]|\b(?:in|inside|for|on)\s+`?pdd[_-]cloud`?\b|`?pdd[_-]cloud`?\s+(?:service|backend|server|repo|repository))/im,
  },
  {
    canonical: 'pdd-workflow',
    short: 'pdd-workflow',
    aliases: ['pdd-workflow', 'pdd_workflow'],
    roots: ['pdd-workflow', 'pdd_workflow'],
    prefixes: ['pdd-workflow/', 'pdd_workflow/'],
    mentionRe: /\bpdd[_-]workflow\b(?!#\d|\.(?:mjs|cjs|js|ts|py|md|json))/i,
    framedRe: /(?:^\s*\[?pdd[_-]workflow\]?\s*[:\-]|\b(?:in|inside|for|on)\s+`?pdd[_-]workflow`?\b|`?pdd[_-]workflow`?\s+(?:service|repo|repository|scripts?|pipeline|workflow))/im,
  },
  {
    canonical: 'prompt-runtime',
    short: 'prompt-runtime',
    aliases: ['prompt-runtime', 'prompt_runtime'],
    roots: ['prompt-runtime'],
    prefixes: ['prompt-runtime/'],
    mentionRe: /\bprompt[_-]runtime\b(?!#\d|\.(?:mjs|cjs|js|ts|py|md|json))/i,
    framedRe: /(?:^\s*\[?prompt[_-]runtime\]?\s*[:\-]|\b(?:in|inside|for|on)\s+`?prompt[_-]runtime`?\b|`?prompt[_-]runtime`?\s+(?:service|server|worker|repo|repository|interpreter))/im,
  },
  {
    canonical: 'runtime-client',
    short: 'runtime-client',
    aliases: ['runtime-client', 'packages/runtime-client'],
    roots: ['runtime-client', 'packages/runtime-client'],
    prefixes: ['runtime-client/', 'packages/runtime-client/'],
    mentionRe: /\bruntime-client\b(?!#\d|\.(?:mjs|cjs|js|ts|py|md|json))/i,
    framedRe: /(?:^\s*\[?runtime-client\]?\s*[:\-]|\b(?:in|inside|for|on)\s+`?runtime-client`?\b|`?runtime-client`?\s+(?:package|repo|repository|sdk|client))/im,
  },
  {
    canonical: 'extensions/github_pdd_app',
    short: 'github_pdd_app',
    aliases: ['extensions/github_pdd_app', 'github_pdd_app', 'github-pdd-app'],
    roots: ['extensions/github_pdd_app', 'github_pdd_app'],
    prefixes: ['extensions/github_pdd_app/', 'github_pdd_app/'],
    mentionRe: /\bgithub[_-]pdd[_-]app\b(?!#\d|\.(?:mjs|cjs|js|ts|py|md|json))/i,
    framedRe: /(?:^\s*\[?github[_-]pdd[_-]app\]?\s*[:\-]|\b(?:in|inside|for|on)\s+`?github[_-]pdd[_-]app`?\b|`?github[_-]pdd[_-]app`?\s+(?:app|extension|service|repo|repository))/im,
  },
]);

const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const asText = value => typeof value === 'string' ? value : '';
const isPositiveInt = value => Number.isSafeInteger(value) && value > 0;
const escapeRegex = value => value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

function cleanSingleLine(value, max = 300) {
  return asText(value)
    .replace(/[\r\n\t]+/g, ' ')
    .replace(/[\u0000-\u001f\u007f-\u009f]/g, '')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, max);
}

/**
 * Strip HTML comments, CommonMark fenced code blocks (including indented list fences),
 * and Markdown blockquote lines so pasted logs and quoted examples never trigger skips.
 */
export function sanitizeIssueText(text) {
  if (typeof text !== 'string' || !text) return '';
  const withoutComments = text.replace(/\r\n?/g, '\n').replace(/<!--[\s\S]*?-->/g, '');
  const kept = [];
  let fence = null;
  for (const line of withoutComments.split('\n')) {
    if (fence) {
      const closeMatch = line.match(/^\s*(`{3,}|~{3,})\s*$/);
      if (closeMatch && closeMatch[1][0] === fence.char && closeMatch[1].length >= fence.len) {
        fence = null;
      }
      continue;
    }
    const btOpen = line.match(/^\s*(`{3,})([^`]*)$/);
    if (btOpen) {
      fence = { char: '`', len: btOpen[1].length };
      continue;
    }
    const tildeOpen = line.match(/^\s*(~{3,})(.*)$/);
    if (tildeOpen) {
      fence = { char: '~', len: tildeOpen[1].length };
      continue;
    }
    if (/^\s*>/.test(line)) continue;
    kept.push(line);
  }
  return kept.join('\n').trim();
}

function splitClauses(sanitizedText) {
  const clauses = [];
  for (const rawLine of asText(sanitizedText).split('\n')) {
    const line = rawLine.trim();
    if (!line) continue;
    if (/^#{1,6}\s+/.test(line)) {
      clauses.push(line);
      continue;
    }
    const parts = line.split(/(?<=[.!?])\s+(?=[A-Z0-9`"([])/);
    for (const part of parts) {
      const trimmed = part.trim();
      if (trimmed) clauses.push(trimmed);
    }
  }
  return clauses;
}

function normalizeCandidatePath(raw) {
  const cleaned = asText(raw)
    .trim()
    .replace(/^`+|`+$/g, '')
    .replace(/^[("'\[]+|[)"'\],.:;!?]+$/g, '')
    .replace(/^\.\//, '')
    .replace(/#L\d+(?:-L?\d+)?$/i, '')
    .replace(/:\d+(?::\d+)?$/, '');
  if (!cleaned || cleaned.startsWith('/') || cleaned.includes('..') || cleaned.includes('://') || cleaned.includes('*') || IGNORE_SLASH_RE.test(cleaned)) {
    return null;
  }
  if (PATH_EXT_RE.test(cleaned) || PATH_PREFIX_RE.test(cleaned)) return cleaned;
  return null;
}

/**
 * Extract repository-relative file path candidates from plain or sanitized issue text.
 */
export function extractReferencedPaths(fullText) {
  const stripped = asText(fullText).replace(/https?:\/\/[^\s)`"'>]+/gi, ' ');
  const found = new Set();
  for (const match of stripped.matchAll(/`([^`\n]{2,180})`/g)) {
    for (const part of match[1].split(/\s+/)) {
      const norm = normalizeCandidatePath(part);
      if (norm) found.add(norm);
    }
  }
  for (const match of stripped.matchAll(/(?:^|[\s(["'])([A-Za-z0-9_.-]+(?:\/[A-Za-z0-9_.-]+)+)(?=$|[\s)\]"',.:;!?])/gm)) {
    const norm = normalizeCandidatePath(match[1]);
    if (norm) found.add(norm);
  }
  return [...found];
}

function matchSiblingAlias(raw) {
  const lower = asText(raw).trim().replace(/^`+|`+$/g, '').replace(/^\[|\]$/g, '').toLowerCase();
  if (!lower) return null;
  return SIBLINGS.find(sib => sib.aliases.includes(lower) || sib.canonical.toLowerCase() === lower) ?? null;
}

function canonicalTargetRepo(raw) {
  const cleaned = asText(raw).trim().replace(/^`+|`+$/g, '').replace(/^\[|\]$/g, '');
  if (!cleaned) return 'external-service';
  const sib = matchSiblingAlias(cleaned);
  if (sib) return sib.canonical;
  return cleaned.toLowerCase();
}

function sameRepository(candidate, currentRepo, currentShort) {
  const lower = asText(candidate).trim().toLowerCase();
  if (!lower) return false;
  if (lower.includes('/')) return Boolean(currentRepo && lower === currentRepo);
  return Boolean(currentShort && lower === currentShort);
}

function createPathChecker(repoFiles) {
  if (!repoFiles) {
    return {
      hasInventory: false,
      pathExists: () => false,
      dirExists: topDir => DEFAULT_LOCAL_TOP_DIRS.has(asText(topDir).replace(/^\.\//, '').replace(/^\/+|\/+$/g, '')),
    };
  }
  const fileSet = new Set();
  const topDirs = new Set();
  for (const entry of repoFiles) {
    if (typeof entry !== 'string') continue;
    const clean = entry.replace(/^\.\//, '').replace(/^\/+/, '');
    if (!clean || clean.includes('..')) continue;
    const slash = clean.indexOf('/');
    if (slash > 0) topDirs.add(clean.slice(0, slash));
    if (!clean.endsWith('/.')) fileSet.add(clean);
  }
  const pathExists = rel => {
    const clean = asText(rel).replace(/^\.\//, '').replace(/^\/+/, '');
    if (!clean || clean.includes('..')) return false;
    if (fileSet.has(clean)) return true;
    const prefix = `${clean}/`;
    for (const item of fileSet) if (item.startsWith(prefix)) return true;
    return topDirs.has(clean);
  };
  const dirExists = topDir => {
    const clean = asText(topDir).replace(/^\.\//, '').replace(/^\/+|\/+$/g, '');
    return Boolean(clean && !clean.includes('..') && !clean.includes('/') && topDirs.has(clean));
  };
  return { hasInventory: true, pathExists, dirExists };
}

function isSiblingActive(sib, currentShort, pathExists) {
  if (currentShort && (currentShort === sib.short.toLowerCase() || sib.aliases.includes(currentShort))) return false;
  return !sib.roots.some(pathExists);
}

function findSiblingForPath(pathStr, currentShort, pathExists) {
  const lower = pathStr.toLowerCase();
  return SIBLINGS.find(sib => isSiblingActive(sib, currentShort, pathExists) && sib.prefixes.some(p => lower.startsWith(p))) ?? null;
}

const TITLE_NON_REPO_SEG0_RE = /^(?:feat|fix|bug|chore|docs|test|tests|ci|cli|ui|ux|api|web|ops|wip|rfc|perf|build|style|refactor|revert|alpha|beta|p[0-3]|pr|os|io|cd|qa)$/i;
const TITLE_NON_REPO_SEG1_RE = /^(?:cli|ui|ux|cd|ci|qa|pr|os|io)$/i;
const META_FILTER_CLAUSE_RE = /\b(?:filter|reject|park|skip|detect|classify|flag|route|ignore)\b[^.\n]{0,75}\b(?:issues?|tickets?|prs?|runs?)\b|\b(?:when\s+they|when\s+an\s+issue|issues?\s+(?:that|which|meant\s+for|belonging\s+to))\b|\b(?:another|other)\s+repo(?:sitory|sitories)?\s*\([^)]*,[^)]*\)/i;
const DEP_BUMP_CLAUSE_RE = /(?:\b(?:bump|pin|upgrade|package\.json|lockfile|npm\s+install)\b|@promptdriven\/[a-z0-9_.-]+|\b(?:have|already)\s+merged\s+to\b)/i;
const STRONG_COORD_RE = /\b(?:coordinat(?:e|ed|ing)\s+(?:changes?|edits?|prs?|updates?|work|releases?|deploys?)|changes?\s+in\s+both\b|edits?\s+in\s+both\b|both\s+repos(?:itories)?\b|across\s+(?:both\s+)?(?:repos(?:itories)?|`?[A-Za-z0-9_./-]+`?\s+and\s+`?[A-Za-z0-9_./-]+`?)|paired\s+(?:pr|pull\s+request|deploy(?:ment)?|change)|ships?\s+together\s+in\s+both|in\s+tandem\s+with|(?:update|edit|change|modify|fix|deploy|ship)\s+[^.\n]{1,65}\balongside\b)/i;
const CLAUSE_EDIT_VERB_RE = /\b(?:update|edit|modify|change|fix|add|create|implement|sync|ship|deploy|coordinate|touch|patch|refactor|remove|delete|expose)\b/i;
const PASSIVE_PATH_RE = /\b(?:already\s+exist(?:s)?\s+in|building\s+blocks?|error\s+(?:from|calling)|returned\s+by|returns?\s+http|calls?\s+`?[A-Za-z0-9_./-]+`?|mocks?|stubs?|documents?|for\s+reference|as\s+reference|for\s+context|as\s+context)\b/i;
const URL_REFERENCE_BEFORE_RE = /\b(?:see|ref(?:erence)?|cf\.?|compare|example|for\s+example|from|per|similar\s+to|inspired\s+by|documented\s+in|ported\s+from|upstream|like)\b/i;
const URL_REFERENCE_AFTER_RE = /^\s*\)?\s*(?:for\s+reference|as\s+reference|for\s+context|as\s+context)\b/i;
const PASSIVE_HEADING_RE = /\b(?:problem|background|context|motivation|overview|summary|notes?|references?|history|observed|already\s+exist)\b/i;
const EXTERNAL_SERVICE_EDIT_RE = /\b(?:requires?\s+(?:a\s+)?(?:paired\s+)?(?:pr|change|edit|update|deploy(?:ment)?)\s+(?:in|to)\s+(?:an?\s+)?(?:external\s+service|another\s+repo(?:sitory)?|other\s+repo(?:sitory)?)|(?:paired\s+(?:pr|deploy(?:ment)?)|coordinated\s+(?:changes?|edits?))\s+(?:in|with|to)\s+(?:an?\s+)?(?:external\s+service|another\s+repo(?:sitory)?))\b/i;

function isValidExplicitSlug(raw, pathExists, dirExists) {
  if (!/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(raw)) return false;
  if (IGNORE_SLASH_RE.test(raw) || PATH_EXT_RE.test(raw) || PATH_PREFIX_RE.test(raw)) return false;
  if (pathExists(raw)) return false;
  const [seg0, seg1] = raw.split('/');
  if (dirExists(seg0) || TITLE_NON_REPO_SEG0_RE.test(seg0) || TITLE_NON_REPO_SEG1_RE.test(seg1)) return false;
  return true;
}

function extractRepoHeader(title, body, currentRepo, currentShort, pathExists, dirExists) {
  const titlePrefix = title.match(/^\s*(?:\[([A-Za-z0-9_.-]+(?:\/[A-Za-z0-9_.-]+)?)\]\s*|([A-Za-z0-9_.-]+(?:\/[A-Za-z0-9_.-]+)?)\s*:\s+)/);
  if (titlePrefix) {
    const raw = (titlePrefix[1] || titlePrefix[2] || '').trim();
    const sib = matchSiblingAlias(raw);
    if (sib && isSiblingActive(sib, currentShort, pathExists)) {
      return { targetRepo: sib.canonical, declared: raw };
    }
    if (raw.includes('/') && isValidExplicitSlug(raw, pathExists, dirExists) && !sameRepository(raw, currentRepo, currentShort)) {
      return { targetRepo: canonicalTargetRepo(raw), declared: raw };
    }
  }
  for (const line of body.split('\n')) {
    const meta = line.match(/^\s*(?:[-*]\s*)?\*{0,2}(?:target\s+)?(repo(?:sitory)?|service)\*{0,2}\s*:\s*`?([A-Za-z0-9_.-]+(?:\/[A-Za-z0-9_.-]+)?)`?\s*$/i);
    if (!meta) continue;
    const fieldKind = meta[1].toLowerCase();
    const declared = meta[2].trim(), lower = declared.toLowerCase();
    if (['none', 'current', 'this', 'local', 'same', 'n/a'].includes(lower)) continue;
    if (sameRepository(declared, currentRepo, currentShort) || pathExists(declared)) continue;
    const sib = matchSiblingAlias(declared);
    if (fieldKind === 'service') {
      if (sib && isSiblingActive(sib, currentShort, pathExists)) return { targetRepo: sib.canonical, declared };
      if (declared.includes('/') && isValidExplicitSlug(declared, pathExists, dirExists)) return { targetRepo: canonicalTargetRepo(declared), declared };
      continue;
    }
    if (declared.includes('/') && !isValidExplicitSlug(declared, pathExists, dirExists) && !sib) continue;
    return { targetRepo: canonicalTargetRepo(declared), declared };
  }
  return null;
}

function extractForeignUrls(fullText, currentRepo, pathExists) {
  const urls = [];
  const re = /https?:\/\/github\.com\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\/(?:blob|tree)\/[^/\s]+\/([^\s)`"'>#?]+)/gi;
  for (const line of asText(fullText).split('\n')) {
    for (const m of line.matchAll(re)) {
      const slug = m[1], lower = slug.toLowerCase();
      const sub = normalizeCandidatePath(m[2]);
      if (currentRepo && lower === currentRepo) continue;
      if (sub && pathExists(sub)) continue;
      const idx = m.index ?? 0;
      const before = line.slice(0, idx);
      const after = line.slice(idx + m[0].length, idx + m[0].length + 36);
      const isReference = URL_REFERENCE_BEFORE_RE.test(before) || URL_REFERENCE_AFTER_RE.test(after);
      urls.push({ targetRepo: lower, path: sub, isReference, line });
    }
  }
  return urls;
}

function hasLocalCliOrModuleHint(fullText, hasInventory, pathExists) {
  if (/\bpdd\s+(?:autopilot|workflow|test|approve|owner|setup|accounts|doctor|init|metrics)\b/i.test(fullText) || /\bpdd\.json\b/i.test(fullText)) {
    return true;
  }
  if (!hasInventory) return false;
  for (const token of fullText.matchAll(/\b([a-z][a-z0-9-]{2,40})\b/gi)) {
    const mod = token[1].toLowerCase();
    if (['prompt-runtime', 'runtime-client', 'pdd-cloud', 'pdd-workflow'].includes(mod)) continue;
    if (pathExists(`src/${mod}.mjs`) || pathExists(`prompts/cli/${mod}.prompt.md`)) return true;
  }
  return false;
}

function analyzeRepositoryTargets({ repository, title, body, trustedText = '', repoFiles = null }) {
  const currentRepo = asText(repository).trim().toLowerCase();
  const [currentOwner, currentShort] = currentRepo.includes('/')
    ? [currentRepo.split('/')[0], currentRepo.split('/').at(-1)]
    : ['', currentRepo];
  const fullText = [title, body, trustedText].filter(Boolean).join('\n');
  const { hasInventory, pathExists, dirExists } = createPathChecker(repoFiles);
  const allPaths = extractReferencedPaths(fullText);
  const specificPaths = allPaths.filter(p => !GENERIC_ROOT_FILES.has(p.toLowerCase()));
  const existingLocal = hasInventory ? specificPaths.filter(pathExists) : [];
  const missingSpecific = hasInventory ? specificPaths.filter(p => !pathExists(p)) : specificPaths;

  const localGreenfield = [];
  const siblingHits = [];
  const foreignMissing = [];
  for (const p of missingSpecific) {
    const sib = findSiblingForPath(p, currentShort, pathExists);
    if (sib) {
      siblingHits.push({ path: p, sibling: sib });
      foreignMissing.push(p);
      continue;
    }
    const slash = p.indexOf('/');
    const topDir = slash > 0 ? p.slice(0, slash) : '';
    if (topDir && dirExists(topDir)) {
      localGreenfield.push(p);
    } else {
      foreignMissing.push(p);
    }
  }

  return {
    currentRepo,
    currentOwner,
    currentShort,
    fullText,
    hasInventory,
    pathExists,
    dirExists,
    existingLocal,
    localGreenfield,
    siblingHits,
    foreignMissing,
    missingSpecific,
    header: extractRepoHeader(title, `${body}\n${trustedText}`, currentRepo, currentShort, pathExists, dirExists),
    foreignUrls: extractForeignUrls(fullText, currentRepo, pathExists),
    namesLocalCli: hasLocalCliOrModuleHint(fullText, hasInventory, pathExists),
  };
}

/**
 * Extract absent foreign (non-local-greenfield, non-generic) paths across an issue's
 * title, sanitized body, and trusted comments for cross-repo routing explanations.
 */
export function extractForeignMissingPaths({ repository = '', title = '', body = '', comments = [], repoFiles = null } = {}) {
  const cleanTitle = cleanSingleLine(title, 500);
  const cleanBody = sanitizeIssueText(asText(body));
  const trustedText = (Array.isArray(comments) ? comments : [])
    .filter(c => isObject(c) && c.trusted !== false)
    .map(c => sanitizeIssueText(asText(c.body)))
    .filter(Boolean)
    .join('\n');
  const ctx = analyzeRepositoryTargets({ repository, title: cleanTitle, body: cleanBody, trustedText, repoFiles });
  const urlPaths = ctx.foreignUrls.filter(u => !u.isReference && u.path).map(u => u.path);
  return [...new Set([...ctx.foreignMissing, ...urlPaths])];
}

/**
 * Shared foreign-only wrong-repository detector used by detectWrongRepositoryIssue (#3500).
 * Returns null whenever any local existing or local-root greenfield path is present
 * (except when an explicit foreign Repo header appears with zero existing local files).
 */
export function detectForeignOnlyTarget({ repository = '', title = '', body = '', repoFiles = null } = {}) {
  const cleanTitle = cleanSingleLine(title, 500);
  const cleanBody = sanitizeIssueText(asText(body));
  if (!cleanTitle && !cleanBody) return null;

  const ctx = analyzeRepositoryTargets({ repository, title: cleanTitle, body: cleanBody, repoFiles });
  const { currentShort, fullText, hasInventory, pathExists, existingLocal, localGreenfield, siblingHits, foreignMissing, missingSpecific, header, foreignUrls, namesLocalCli } = ctx;

  if (header && existingLocal.length === 0) {
    return {
      targetRepo: header.targetRepo,
      signal: 'repo-header',
      missingPaths: foreignMissing.length ? foreignMissing : missingSpecific,
      reason: `Issue header targets repository ${header.declared}, and none of the referenced implementation paths exist in ${repository || 'this repository'}.`,
    };
  }
  if (existingLocal.length > 0 || localGreenfield.length > 0) return null;

  const targetUrls = foreignUrls.filter(u => !u.isReference);
  if (targetUrls.length > 0 && ctx.currentRepo && !namesLocalCli) {
    const first = targetUrls[0];
    const missing = [...new Set([...foreignMissing, ...(first.path ? [first.path] : [])])];
    return {
      targetRepo: first.targetRepo,
      signal: 'github-url',
      missingPaths: missing,
      reason: `Issue links code in ${first.targetRepo}, and none of the referenced paths exist in ${repository}.`,
    };
  }
  if (!hasInventory) return null;

  if (siblingHits.length > 0) {
    const first = siblingHits[0];
    const hits = siblingHits.filter(h => h.sibling === first.sibling).map(h => h.path);
    return {
      targetRepo: first.sibling.canonical,
      signal: 'external-root-path',
      missingPaths: foreignMissing,
      reason: `Issue targets ${first.sibling.canonical} paths (${hits.slice(0, 3).join(', ')}) that do not exist in ${repository || 'this repository'}.`,
    };
  }

  if (!namesLocalCli && !DEP_BUMP_CLAUSE_RE.test(fullText)) {
    for (const sib of SIBLINGS) {
      if (!isSiblingActive(sib, currentShort, pathExists) || !sib.mentionRe.test(fullText)) continue;
      if (foreignMissing.length > 0 || sib.framedRe.test(fullText)) {
        return {
          targetRepo: sib.canonical,
          signal: 'sibling-service',
          missingPaths: foreignMissing,
          reason: `Issue targets ${sib.canonical} implementation${foreignMissing.length ? ` (${foreignMissing.slice(0, 3).join(', ')})` : ''}, which is absent from ${repository || 'this repository'}.`,
        };
      }
    }
  }
  return null;
}

function findForeignHeadingTarget(clauses, currentOwner, currentRepo, currentShort, pathExists) {
  const ownerSlugRe = currentOwner
    ? new RegExp(`\\b(${escapeRegex(currentOwner)}\\/[A-Za-z0-9_.-]+)(?!#\\d)`, 'gi')
    : null;
  for (const clause of clauses) {
    const headingMatch = clause.match(/^#{1,6}\s+(.+)$/);
    if (!headingMatch) continue;
    const heading = headingMatch[1]
      .replace(/\b[A-Za-z0-9_.-]+(?:\/[A-Za-z0-9_.-]+)?#\d+\b/g, ' ')
      .replace(/(?:[A-Za-z0-9_.-]+\/)+[A-Za-z0-9_.-]+\.(?:mjs|cjs|js|ts|tsx|jsx|py|rs|go|rb|sh|md|json|ya?ml|toml|sql)(?::\d+(?:-\d+)?)?/gi, ' ');
    if (PASSIVE_HEADING_RE.test(heading) || DEP_BUMP_CLAUSE_RE.test(heading)) continue;
    if (ownerSlugRe) {
      for (const m of heading.matchAll(ownerSlugRe)) {
        const slug = m[1].toLowerCase();
        if (slug !== currentRepo) return canonicalTargetRepo(slug);
      }
    }
    for (const sib of SIBLINGS) {
      if (isSiblingActive(sib, currentShort, pathExists) && sib.mentionRe.test(heading)) {
        return sib.canonical;
      }
    }
  }
  return null;
}

function detectCrossRepo({ repository, title, body, trustedText, repoFiles }) {
  const ctx = analyzeRepositoryTargets({ repository, title, body, trustedText, repoFiles });
  const { currentRepo, currentOwner, currentShort, fullText, pathExists, existingLocal, localGreenfield, siblingHits, foreignMissing, header, foreignUrls, namesLocalCli } = ctx;
  if (!fullText.trim()) return null;

  const hasLocalTargets = existingLocal.length > 0 || localGreenfield.length > 0;
  const clauses = splitClauses(fullText);
  const reject = (targetRepo, signals, reason, missingPaths = foreignMissing) => ({
    decision: 'reject',
    reasonCode: 'cross_repo',
    intakeClass: 'elsewhere',
    label: 'needs-other-repo',
    targetRepo,
    reason: cleanSingleLine(reason),
    question: null,
    signals: [...new Set(signals)],
    ...(missingPaths.length ? { missingPaths } : {}),
  });

  // 1. Explicit foreign title prefix or Repo/Repository/Service header.
  if (header) {
    const signals = ['repo_header', ...(hasLocalTargets ? ['coordinated_multi_repo'] : [])];
    const reason = hasLocalTargets
      ? `Requires coordinated changes with ${header.targetRepo} alongside ${repository || 'this repository'}.`
      : `Issue targets repository ${header.targetRepo} rather than ${repository || 'this repository'}.`;
    return reject(header.targetRepo, signals, reason);
  }

  // 2. Absent foreign sibling root paths (foreign-only, or actively edited in the same clause).
  if (siblingHits.length > 0) {
    const primary = siblingHits[0];
    const citedPaths = siblingHits.slice(0, 3).map(h => h.path).join(', ');
    if (!hasLocalTargets) {
      return reject(
        primary.sibling.canonical,
        ['foreign_root_path'],
        `Targets ${primary.sibling.canonical} paths (${citedPaths}) absent from ${repository || 'this repository'}.`,
      );
    }
    const activeEditHit = siblingHits.find(hit => {
      const hitClauses = clauses.filter(c => c.includes(hit.path) && !META_FILTER_CLAUSE_RE.test(c));
      return hitClauses.some(c => !PASSIVE_PATH_RE.test(c) && (STRONG_COORD_RE.test(c) || CLAUSE_EDIT_VERB_RE.test(c)));
    });
    if (activeEditHit) {
      return reject(
        activeEditHit.sibling.canonical,
        ['foreign_root_path', 'coordinated_multi_repo'],
        `Requires coordinated edits in ${activeEditHit.sibling.canonical} (${citedPaths}) alongside ${repository || 'this repository'}.`,
      );
    }
  }

  // 3. Dedicated implementation section heading for another repo (e.g., "### 1. Server (promptdriven/pdd_cloud)").
  const headingTarget = findForeignHeadingTarget(clauses, currentOwner, currentRepo, currentShort, pathExists);
  if (headingTarget) {
    const signals = ['coordinated_multi_repo', ...(siblingHits.length ? ['foreign_root_path'] : ['sibling_service'])];
    return reject(
      headingTarget,
      signals,
      `Requires coordinated implementation changes in ${headingTarget} alongside ${repository || 'this repository'}.`,
    );
  }

  // 4. Non-reference foreign GitHub blob/tree URLs.
  const editUrls = foreignUrls.filter(u => !u.isReference);
  if (editUrls.length > 0) {
    if (!hasLocalTargets && !namesLocalCli) {
      const first = editUrls[0];
      return reject(
        first.targetRepo,
        ['foreign_url'],
        `Links code in ${first.targetRepo} with no local paths in ${repository || 'this repository'}.`,
        [...new Set([...foreignMissing, ...(first.path ? [first.path] : [])])],
      );
    }
    const editedUrl = editUrls.find(u => !META_FILTER_CLAUSE_RE.test(u.line) && (STRONG_COORD_RE.test(u.line) || CLAUSE_EDIT_VERB_RE.test(u.line)));
    if (editedUrl) {
      return reject(
        editedUrl.targetRepo,
        ['foreign_url', 'coordinated_multi_repo'],
        `Requires coordinated edits in ${editedUrl.targetRepo} alongside ${repository || 'this repository'}.`,
        [...new Set([...foreignMissing, ...(editedUrl.path ? [editedUrl.path] : [])])],
      );
    }
  }

  // 5. Clause-scoped coordinated-edit phrases bound directly to an active sibling, same-org foreign repo, or external service.
  const ownerSlugRe = currentOwner
    ? new RegExp(`\\b(${escapeRegex(currentOwner)}\\/[A-Za-z0-9_.-]+)(?!#\\d)`, 'gi')
    : null;
  for (const clause of clauses) {
    if (META_FILTER_CLAUSE_RE.test(clause) || DEP_BUMP_CLAUSE_RE.test(clause)) continue;
    if (STRONG_COORD_RE.test(clause)) {
      for (const sib of SIBLINGS) {
        if (isSiblingActive(sib, currentShort, pathExists) && sib.mentionRe.test(clause)) {
          return reject(
            sib.canonical,
            ['sibling_service', 'coordinated_multi_repo'],
            `Requires coordinated edits in ${sib.canonical} alongside ${repository || 'this repository'}.`,
          );
        }
      }
      if (ownerSlugRe) {
        for (const m of clause.matchAll(ownerSlugRe)) {
          const slug = m[1].toLowerCase();
          if (slug !== currentRepo) {
            return reject(
              canonicalTargetRepo(slug),
              ['coordinated_multi_repo'],
              `Requires coordinated changes across ${repository || 'this repository'} and ${canonicalTargetRepo(slug)}.`,
            );
          }
        }
      }
    }
    if (EXTERNAL_SERVICE_EDIT_RE.test(clause)) {
      return reject(
        'external-service',
        ['coordinated_multi_repo'],
        `Requires coordinated edits or deployment in an external service outside ${repository || 'this repository'}.`,
      );
    }
  }

  // 6. Foreign-only sibling framing when no local targets or local CLI/module references exist.
  if (!hasLocalTargets && !namesLocalCli && !DEP_BUMP_CLAUSE_RE.test(fullText)) {
    for (const sib of SIBLINGS) {
      if (!isSiblingActive(sib, currentShort, pathExists) || !sib.mentionRe.test(fullText)) continue;
      if (foreignMissing.length > 0 || sib.framedRe.test(fullText)) {
        return reject(
          sib.canonical,
          ['sibling_service'],
          `Targets ${sib.canonical}, which is outside ${repository || 'this repository'}.`,
        );
      }
    }
  }

  return null;
}

const EXPLICIT_DECISION_MARKER_RE = /\b(?:open\s+question|needs?\s+(?:a\s+)?(?:product|pricing|billing|ux|design|policy|human)?\s*decision|decision\s+needed|product\s+decision|pricing\s+decision|ux\s+decision|question\s+for\s+(?:product|design|leadership|maintainers?|serhan|team|humans?))\s*:/i;
const PROSE_DECISION_NEED_RE = /\bneeds?\s+(?:a\s+)?(?:product|pricing|billing|ux|design|policy)(?:\s+(?:and|or)\s+(?:product|pricing|billing|ux|design|policy))*\s+decision\b/i;
const POLICY_DOMAIN_RE = /\b(?:pric(?:e|ing)|billing\s+(?:tier|model|plan)|subscription\s+(?:tier|plan)|free\s+tier|pro\s+tier|paid\s+tier|per[- ]seat|seat\s+pric(?:e|ing)|monetiz(?:e|ation)|product\s+(?:direction|decision|policy)|ux\s+(?:policy|direction|decision)|user[- ]facing\s+(?:policy|ux|copy)|default\s+(?:output\s+)?view|onboarding\s+flow|branding|pricing\s+model)\b|\$\d+(?:\s*\/\s*(?:seat|month|mo|user|year))?/i;
const CHOICE_PROMPT_RE = /\bshould\s+(?:we|pdd|autopilot|[a-z0-9_`' -]{2,40})\b[^?\n]{2,140}\bor\b[^?\n]{1,100}\?|\boptions?\s*:\s*(?:\(?A\)?|1\))[\s\S]{1,200}(?:\(?B\)?|2\))/i;
const SETTLED_DECISION_RE = /(?:^\s*(?:[-*]\s*)?\*{0,2}(?:decision|resolved|approved|confirmed|locked[- ]?in|final\s+decision|answer)\*{0,2}\s*:|\b(?:go\s+with|let'?s\s+(?:go\s+with|use|do|ship|default\s+to|pick|choose|keep|make\s+it|set\s+it\s+to|charge)|use\s+option\s+[a-c]|pick\s+option\s+[a-c]|choose\s+option\s+[a-c]|option\s+[a-c]\s+(?:is\s+)?(?:approved|fine|good|works)|we\s+(?:decided|chose|picked|agreed)\b|will\s+default\s+to\b|proceed\s+with\b|yes,?\s+(?:use|do|go\s+with|default|charge|set)\b|sounds\s+good\b|lgtm\b)\b|^\s*default\s+to\b)/im;
const DIRECT_OPTION_REPLY_RE = /^\s*(?:option\s+)?[a-c]\s*[).]?\s*$/i;
const DEFERRAL_RE = /\b(?:still\s+thinking|not\s+sure|let\s+me\s+check|waiting\s+on|need\s+to\s+think|tbd|hold\s+on|can\s+someone\s+else)\b/i;
const PRICING_SIGNAL_RE = /\b(?:pric(?:e|ing)|billing|tier|seat|paid\s+tier|free\s+tier|pro\s+tier)\b|\$\d+/i;
const UX_SIGNAL_RE = /\b(?:ux|ui|default\s+(?:output\s+)?view|layout|onboarding|user[- ]facing)\b/i;

function extractDecisionQuestion(clause, markerMatch, choiceMatch) {
  if (markerMatch) {
    const tail = clause.slice(markerMatch.index + markerMatch[0].length).trim();
    const qEnd = tail.indexOf('?');
    const picked = qEnd >= 0 ? tail.slice(0, qEnd + 1) : tail;
    if (picked.length >= 10) return cleanSingleLine(picked, 300);
  }
  if (choiceMatch) {
    const picked = cleanSingleLine(choiceMatch[0], 300);
    if (picked.length >= 10) return picked;
  }
  if (clause.includes('?')) return cleanSingleLine(clause, 300);
  return 'Which product, pricing, or UX policy option should Autopilot implement before starting?';
}

function findDecisionTrigger(sanitizedText) {
  if (!sanitizedText) return null;
  let active = null;
  for (const clause of splitClauses(sanitizedText)) {
    if (META_FILTER_CLAUSE_RE.test(clause)) continue;
    const markerMatch = clause.match(EXPLICIT_DECISION_MARKER_RE);
    const proseMatch = clause.match(PROSE_DECISION_NEED_RE);
    const choiceMatch = CHOICE_PROMPT_RE.test(clause) && POLICY_DOMAIN_RE.test(clause)
      ? clause.match(CHOICE_PROMPT_RE)
      : null;
    if (markerMatch || proseMatch || choiceMatch) {
      const settledInSameClause = !clause.trim().endsWith('?') ? clause.match(SETTLED_DECISION_RE) : null;
      const triggerIdx = Math.max(markerMatch?.index ?? -1, proseMatch?.index ?? -1, choiceMatch?.index ?? -1);
      const lastQIdx = clause.lastIndexOf('?');
      if (settledInSameClause && (settledInSameClause.index ?? 0) > Math.max(triggerIdx, lastQIdx)) {
        active = null;
      } else {
        active = { question: extractDecisionQuestion(clause, markerMatch, choiceMatch), sourceText: clause };
      }
      continue;
    }
    if (active && SETTLED_DECISION_RE.test(clause) && !DEFERRAL_RE.test(clause) && !clause.trim().endsWith('?')) {
      active = null;
    }
  }
  return active;
}

function isNaturalResolutionComment(cText) {
  if (!cText || DEFERRAL_RE.test(cText) || cText.trim().endsWith('?')) return false;
  if (SETTLED_DECISION_RE.test(cText) || DIRECT_OPTION_REPLY_RE.test(cText)) return true;
  // Short direct maintainer choice answer (e.g. "$19/seat and 1 free account." or "Overview by default.")
  if (!cText.includes('?') && cText.length <= 220 && /(?:^\s*\$\d+|\$\d+\s*\/\s*(?:seat|month|mo|user|year)|\b(?:overview|full|charge|set\s+to|make\s+it|keep\s+it|ship\s+with|use\s+|allow\s+\d+))/i.test(cText)) {
    return true;
  }
  return false;
}

function detectHumanDecision({ title, body, trustedComments, decisionNote }) {
  if (typeof decisionNote === 'string' && decisionNote.trim().length > 0) return null;

  const baseText = [title, body].filter(Boolean).join('\n');
  let unresolved = findDecisionTrigger(baseText);

  for (const comment of trustedComments) {
    const cText = comment.sanitized;
    if (!cText) continue;
    const nextTrigger = findDecisionTrigger(cText);
    if (nextTrigger) {
      unresolved = nextTrigger;
      continue;
    }
    if (unresolved && isNaturalResolutionComment(cText)) {
      unresolved = null;
    }
  }

  if (!unresolved) return null;

  const combined = `${baseText}\n${unresolved.sourceText}`;
  const signals = [];
  if (PRICING_SIGNAL_RE.test(combined)) signals.push('pricing_policy_choice');
  if (UX_SIGNAL_RE.test(combined)) signals.push('ux_policy_choice');
  if (signals.length === 0 || /\b(?:product|open\s+question|policy|decision)\b/i.test(combined)) {
    signals.unshift('open_product_question');
  }

  return {
    decision: 'park',
    reasonCode: 'human_decision',
    intakeClass: 'person',
    label: 'pdd:needs-decision',
    targetRepo: null,
    reason: cleanSingleLine(`Requires an unanswered human decision before implementation: ${unresolved.question}`, 300),
    question: cleanSingleLine(unresolved.question, 300),
    signals: [...new Set(signals)],
  };
}

const NEGATED_LOCAL_VERIFY_RE = /\b(?:no|not|never|cannot|can't|without|don't|do\s+not)\s+(?:accept(?:ed)?\s+|use\s+|rely\s+on\s+|allow\s+)?(?:a\s+|any\s+)?(?:local\s+)?(?:unit\s+tests?|mocks?|fakes?|stubs?|dry[- ]?run|fixtures?)\b|\b(?:mocks?|fakes?|stubs?|local\s+tests?)\s+(?:are|is)\s+(?:not\s+accepted|disallowed|rejected|unacceptable|insufficient)\b/i;
const LOCAL_ALTERNATIVE_WAIVER_RE = /\b(?:or\s+(?:verify|test|prove|check)\s+(?:with|using|via)\s+(?:local\s+)?(?:unit|integration|fake|mock(?:ed)?|stub(?:bed)?|dry[- ]?run|fixture)|instead\s+of\s+(?:live|production|manual)|(?:local\s+(?:unit|integration)\s+tests?|fake\s+(?:http|api|service|server|port)|mock(?:ed)?\s+(?:http|api|service|server|port)|dry[- ]?run\s+fixtures?)\s+(?:are|is)\s+(?:enough|sufficient|acceptable|fine))\b/i;
const COMMENT_LOCAL_AUTH_RE = /\b(?:verify|test|check|prove|use)\s+(?:with|using|via)?\s*(?:local\s+)?(?:unit|integration|automated|fake|mock(?:ed)?|stub(?:bed)?|dry[- ]?run|fixture)\b|\b(?:instead|sufficient|acceptable|fine\s+to\s+(?:mock|stub|use\s+local))\b/i;
const VERIFY_FRAME_RE = /\b(?:acceptance\s+criteria|done\s+when|verif(?:y|ied|ication)|prove|confirm|validate|test(?:ing|ed)?|check|trigger|run|execute|sign[- ]?off|must\s+(?:pass|run|trigger|verify|confirm|publish|be\s+(?:tested|verified|reviewed|signed))|require[ds]?\s+(?:a\s+)?(?:human|manual|physical|live|production|real|to\s+(?:verify|test|run|trigger|confirm|prove|sign[- ]?off|publish)))\b/i;
const REDACTION_DEFENSE_RE = /\b(?:never\s+(?:log|print|leak|expose|write|store|save|commit)|redact|strip|scrub|remove\s+plaintext|avoid\s+leaking|mask|sanitize|without\s+(?:leaving|writing|storing)|zero\s+(?:plaintext|residual))\b/i;
const PROD_CREDS_RE = /\b(?:production\s+credentials?|prod(?:uction)?\s+(?:secrets?|api\s+keys?|tokens?|account)|maintainer\s+2fa|2fa\s+credentials?|live\s+(?:api\s+keys?|stripe\s+keys?|registry\s+publish|npm\s+publish))\b/i;
const LIVE_EXTERNAL_RE = /\b(?:live\s+(?:stripe|payment|checkout|webhook|production|dashboard\s+receipt|third[- ]party|external\s+service)|real\s+\$\d+[^.\n]*(?:charge|checkout|payment)|in\s+production\s+with\b|against\s+(?:live|production)\s+(?:stripe|api|service|environment|server))\b/i;
const MANUAL_QA_RE = /\b(?:manual\s+(?:human\s+)?(?:qa|visual)\s+(?:sign[- ]?off|review|check|verification)|manual\s+human\s+qa|physical\s+(?:hardware|device|iphone|android)|real\s+(?:iphone|android|mobile)\s+device|requires?\s+a\s+human\s+to\s+(?:visually|manually)\s+(?:verify|inspect|test))\b/i;
const NAMED_RECIPE_RE = /\b(?:external\s+e2e|verification|e2e)\s+recipe\s*[:`"]+\s*([A-Za-z0-9_.:/-]+)/gi;

function normalizeCapabilities(raw) {
  if (!isObject(raw)) return DEFAULT_CAPABILITIES;
  return {
    localTests: typeof raw.localTests === 'boolean' ? raw.localTests : DEFAULT_CAPABILITIES.localTests,
    liveExternalServices: typeof raw.liveExternalServices === 'boolean' ? raw.liveExternalServices : DEFAULT_CAPABILITIES.liveExternalServices,
    productionCredentials: typeof raw.productionCredentials === 'boolean' ? raw.productionCredentials : DEFAULT_CAPABILITIES.productionCredentials,
    humanManualQa: typeof raw.humanManualQa === 'boolean' ? raw.humanManualQa : DEFAULT_CAPABILITIES.humanManualQa,
    availableRecipes: Array.isArray(raw.availableRecipes)
      ? raw.availableRecipes.filter(r => typeof r === 'string' && r.trim()).map(r => r.trim().toLowerCase())
      : [],
  };
}

function resolveLocalBoundaryOverride(bodyText, trustedComments, caps) {
  if (!caps.localTests) return false;
  let commentState = 'none';
  for (const comment of trustedComments) {
    const cText = comment.sanitized;
    if (!cText) continue;
    if (NEGATED_LOCAL_VERIFY_RE.test(cText)) {
      commentState = 'local_rejected';
    } else if (COMMENT_LOCAL_AUTH_RE.test(cText) || LOCAL_ALTERNATIVE_WAIVER_RE.test(cText)) {
      commentState = 'local_authorized';
    }
  }
  if (commentState === 'local_authorized') return true;
  if (commentState === 'local_rejected') return false;
  return !NEGATED_LOCAL_VERIFY_RE.test(bodyText) && LOCAL_ALTERNATIVE_WAIVER_RE.test(bodyText);
}

function detectUnverifiableBoundary({ title, body, trustedComments, workerCapabilities, decisionNote }) {
  if (typeof decisionNote === 'string' && decisionNote.trim().length > 0) return null;
  const caps = normalizeCapabilities(workerCapabilities);
  const bodyText = [title, body].filter(Boolean).join('\n');
  const fullText = [bodyText, ...trustedComments.map(c => c.sanitized)].filter(Boolean).join('\n');
  if (!fullText.trim()) return null;

  if (resolveLocalBoundaryOverride(bodyText, trustedComments, caps)) return null;

  const signals = [];
  const reasons = [];
  const clauses = splitClauses(fullText);

  let hasProdCreds = false;
  let hasLiveExternal = false;
  let hasManualQa = false;
  const missingRecipes = new Set();

  for (const clause of clauses) {
    if (META_FILTER_CLAUSE_RE.test(clause) || REDACTION_DEFENSE_RE.test(clause)) continue;
    const framed = VERIFY_FRAME_RE.test(clause);
    if (!caps.productionCredentials && framed && PROD_CREDS_RE.test(clause)) hasProdCreds = true;
    if (!caps.liveExternalServices && framed && LIVE_EXTERNAL_RE.test(clause)) hasLiveExternal = true;
    if (!caps.humanManualQa && framed && MANUAL_QA_RE.test(clause)) {
      hasManualQa = true;
    }
    for (const m of clause.matchAll(NAMED_RECIPE_RE)) {
      const recipe = m[1].trim();
      if (recipe && !caps.availableRecipes.includes(recipe.toLowerCase())) {
        missingRecipes.add(recipe);
      }
    }
  }

  if (hasProdCreds) {
    signals.push('missing_prod_credentials');
    reasons.push('production credentials or 2FA unavailable to the worker');
  }
  if (hasLiveExternal) {
    signals.push('unavailable_external_e2e');
    reasons.push('live external or production service verification unavailable to the worker');
  }
  for (const recipe of missingRecipes) {
    signals.push('unavailable_external_e2e');
    reasons.push(`external verification recipe "${recipe}" is not available on this worker`);
  }
  if (hasManualQa) {
    signals.push('manual_human_qa_only');
    reasons.push('manual human QA or physical device verification unavailable to the worker');
  }

  if (signals.length === 0) return null;

  return {
    decision: 'park',
    reasonCode: 'unverifiable_boundary',
    intakeClass: 'person',
    label: 'pdd:needs-decision',
    targetRepo: null,
    reason: cleanSingleLine(`Required verification depends on ${reasons.join(' and ')}.`, 300),
    question: cleanSingleLine('Can Autopilot verify this change with local automated or stubbed tests instead, or should a person handle the external/manual verification?', 300),
    signals: [...new Set(signals)],
  };
}

function normalizeTrustedComments(comments) {
  if (!Array.isArray(comments)) return [];
  const trusted = comments
    .filter(c => isObject(c) && c.trusted !== false)
    .map((c, idx) => ({
      idx,
      ts: typeof c.at === 'string' ? Date.parse(c.at) : Number.NaN,
      sanitized: sanitizeIssueText(asText(c.body)),
    }))
    .filter(c => c.sanitized.length > 0);
  const allDated = trusted.length > 1 && trusted.every(c => Number.isFinite(c.ts));
  return allDated ? trusted.sort((a, b) => a.ts - b.ts || a.idx - b.idx) : trusted;
}

/**
 * Deterministically classify an open GitHub issue before Autopilot claims it or spends build tokens.
 */
export function classifyPreflightIssue({
  repository = '',
  issue = null,
  repoFiles = null,
  decisionNote = null,
  workerCapabilities = null,
} = {}) {
  const allow = {
    decision: 'allow',
    reasonCode: null,
    intakeClass: null,
    label: null,
    targetRepo: null,
    reason: null,
    question: null,
    signals: [],
  };
  if (!isObject(issue)) return allow;

  const title = cleanSingleLine(issue.title, 500);
  const body = sanitizeIssueText(asText(issue.body));
  const trustedComments = normalizeTrustedComments(issue.comments);
  const trustedText = trustedComments.map(c => c.sanitized).join('\n');

  const crossRepo = detectCrossRepo({ repository, title, body, trustedText, repoFiles });
  if (crossRepo) {
    const { missingPaths: _ignored, ...publicResult } = crossRepo;
    return publicResult;
  }

  const humanDecision = detectHumanDecision({ title, body, trustedComments, decisionNote });
  if (humanDecision) return humanDecision;

  const unverifiable = detectUnverifiableBoundary({ title, body, trustedComments, workerCapabilities, decisionNote });
  if (unverifiable) return unverifiable;

  return allow;
}

function runStatusRank(status) {
  const normalized = asText(status).trim().toLowerCase();
  if (normalized === 'merged' || normalized === 'would-merge') return 3;
  if (normalized === 'running') return 2;
  if (normalized === 'needs-person') return 1;
  return 0;
}

/**
 * Roll up recorded pre-flight skip reasons alongside Classifier Conversion (Merged / Taken)
 * so metrics can report intake filter precision.
 */
export function summarizeIntakeFilterPrecision({ skips = [], runs = [] } = {}) {
  const latestSkips = new Map();
  if (Array.isArray(skips)) {
    for (const rec of skips) {
      if (!isObject(rec) || !isPositiveInt(rec.issue) || !REASON_CODE_SET.has(rec.reasonCode)) continue;
      const repoKey = asText(rec.repo).trim().toLowerCase();
      const key = `${repoKey}#${rec.issue}`;
      const ts = typeof rec.at === 'string' ? Date.parse(rec.at) : Number.NaN;
      const prev = latestSkips.get(key);
      if (!prev || !Number.isFinite(ts) || !Number.isFinite(prev.ts) || ts >= prev.ts) {
        latestSkips.set(key, { reasonCode: rec.reasonCode, ts });
      }
    }
  }

  const byReasonCode = { cross_repo: 0, human_decision: 0, unverifiable_boundary: 0 };
  for (const entry of latestSkips.values()) byReasonCode[entry.reasonCode] += 1;
  const skipped = latestSkips.size;

  const takenRank = new Map();
  if (Array.isArray(runs)) {
    for (const run of runs) {
      if (!isObject(run)) continue;
      const repoKey = asText(run.repo).trim().toLowerCase();
      const issueList = Array.isArray(run.issues) && run.issues.some(isPositiveInt)
        ? run.issues.filter(isPositiveInt)
        : (isPositiveInt(run.issue) ? [run.issue] : []);
      const rank = runStatusRank(run.status);
      for (const issueNum of issueList) {
        const key = `${repoKey}#${issueNum}`;
        if (rank > (takenRank.get(key) ?? -1)) takenRank.set(key, rank);
      }
    }
  }

  const taken = takenRank.size;
  let merged = 0;
  for (const rank of takenRank.values()) if (rank === 3) merged += 1;
  const unmerged = taken - merged;
  const classifierConversionPct = taken === 0 ? null : Math.round((merged / taken) * 1000) / 10;
  const classifierConversionDisplay = taken === 0
    ? '0/0 (n/a)'
    : `${merged}/${taken} (${classifierConversionPct.toFixed(1)}%)`;

  const nonZeroParts = PREFLIGHT_REASON_CODES
    .filter(code => byReasonCode[code] > 0)
    .map(code => `${byReasonCode[code]} ${code}`);
  const skipSummary = skipped === 0
    ? 'Pre-flight skipped (0): none'
    : `Pre-flight skipped (${skipped}): ${nonZeroParts.join(' · ')}`;

  return {
    skipped,
    byReasonCode,
    taken,
    merged,
    unmerged,
    classifierConversionPct,
    classifierConversionDisplay,
    skipSummary,
  };
}
