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
    mentionRe: /\bpdd[_-]cloud\b/i,
    framedRe: /(?:^\s*\[?pdd[_-]cloud\]?\s*[:\-]|\bin\s+`?pdd[_-]cloud`?\b|\bfor\s+`?pdd[_-]cloud`?\b|\bon\s+`?pdd[_-]cloud`?\b|`?pdd[_-]cloud`?\s+(?:service|backend|server|repo|repository))/im,
  },
  {
    canonical: 'pdd-workflow',
    short: 'pdd-workflow',
    aliases: ['pdd-workflow', 'pdd_workflow'],
    roots: ['pdd-workflow', 'pdd_workflow'],
    prefixes: ['pdd-workflow/', 'pdd_workflow/'],
    mentionRe: /\bpdd[_-]workflow\b/i,
    framedRe: /(?:^\s*\[?pdd[_-]workflow\]?\s*[:\-]|\bin\s+`?pdd[_-]workflow`?\b|\bfor\s+`?pdd[_-]workflow`?\b|\bon\s+`?pdd[_-]workflow`?\b|`?pdd[_-]workflow`?\s+(?:service|repo|repository|scripts?|pipeline|workflow))/im,
  },
  {
    canonical: 'prompt-runtime',
    short: 'prompt-runtime',
    aliases: ['prompt-runtime', 'prompt_runtime'],
    roots: ['prompt-runtime'],
    prefixes: ['prompt-runtime/'],
    mentionRe: /\bprompt[_-]runtime\b/i,
    framedRe: /(?:^\s*\[?prompt[_-]runtime\]?\s*[:\-]|\bin\s+`?prompt[_-]runtime`?\b|\bfor\s+`?prompt[_-]runtime`?\b|\bon\s+`?prompt[_-]runtime`?\b|`?prompt[_-]runtime`?\s+(?:service|server|worker|repo|repository|interpreter))/im,
  },
  {
    canonical: 'runtime-client',
    short: 'runtime-client',
    aliases: ['runtime-client', 'packages/runtime-client'],
    roots: ['runtime-client', 'packages/runtime-client'],
    prefixes: ['runtime-client/', 'packages/runtime-client/'],
    mentionRe: /\bruntime-client\b/i,
    framedRe: /(?:^\s*\[?runtime-client\]?\s*[:\-]|\bin\s+`?runtime-client`?\b|\bfor\s+`?runtime-client`?\b|\bon\s+`?runtime-client`?\b|`?runtime-client`?\s+(?:package|repo|repository|sdk|client))/im,
  },
  {
    canonical: 'extensions/github_pdd_app',
    short: 'github_pdd_app',
    aliases: ['extensions/github_pdd_app', 'github_pdd_app', 'github-pdd-app'],
    roots: ['extensions/github_pdd_app', 'github_pdd_app'],
    prefixes: ['extensions/github_pdd_app/', 'github_pdd_app/'],
    mentionRe: /\bgithub[_-]pdd[_-]app\b/i,
    framedRe: /(?:^\s*\[?github[_-]pdd[_-]app\]?\s*[:\-]|\bin\s+`?github[_-]pdd[_-]app`?\b|\bfor\s+`?github[_-]pdd[_-]app`?\b|\bon\s+`?github[_-]pdd[_-]app`?\b|`?github[_-]pdd[_-]app`?\s+(?:app|extension|service|repo|repository))/im,
  },
]);

const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const asText = value => typeof value === 'string' ? value : '';
const isPositiveInt = value => Number.isSafeInteger(value) && value > 0;

function cleanSingleLine(value, max = 300) {
  return asText(value)
    .replace(/[\r\n\t]+/g, ' ')
    .replace(/[\u0000-\u001f\u007f-\u009f]/g, '')
    .replace(/\s+/g, ' ')
    .trim()
    .slice(0, max);
}

/**
 * Strip HTML comments, fenced Markdown code blocks, and Markdown blockquote lines
 * so pasted logs and quoted examples never trigger pre-flight skips.
 */
export function sanitizeIssueText(text) {
  if (typeof text !== 'string' || !text) return '';
  const withoutComments = text.replace(/\r\n?/g, '\n').replace(/<!--[\s\S]*?-->/g, '');
  const kept = [];
  let fence = null;
  for (const line of withoutComments.split('\n')) {
    if (fence) {
      const closeMatch = line.match(/^\s{0,3}(`{3,}|~{3,})\s*$/);
      if (closeMatch && closeMatch[1][0] === fence.char && closeMatch[1].length >= fence.len) {
        fence = null;
      }
      continue;
    }
    const openMatch = line.match(/^\s{0,3}(`{3,}|~{3,})/);
    if (openMatch) {
      fence = { char: openMatch[1][0], len: openMatch[1].length };
      continue;
    }
    if (/^\s*>/.test(line)) continue;
    kept.push(line);
  }
  return kept.join('\n').trim();
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

function extractReferencedPaths(fullText) {
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
  const lower = cleaned.toLowerCase();
  if (/^[a-z0-9_.-]+\/[a-z0-9_.-]+$/.test(lower)) return lower;
  return lower;
}

function sameRepository(candidate, currentRepo, currentShort) {
  const lower = asText(candidate).trim().toLowerCase();
  if (!lower) return false;
  if (currentRepo && lower === currentRepo) return true;
  if (currentShort && (lower === currentShort || lower.endsWith(`/${currentShort}`))) return true;
  return false;
}

function buildFileInventory(repoFiles) {
  if (!repoFiles) return { fileSet: null, topDirs: null };
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
  return { fileSet, topDirs };
}

function createPathChecker(repoFiles) {
  const { fileSet, topDirs } = buildFileInventory(repoFiles);
  const hasInventory = fileSet !== null;
  const pathExists = rel => {
    const clean = asText(rel).replace(/^\.\//, '').replace(/^\/+/, '');
    if (!clean || clean.includes('..') || !hasInventory) return false;
    if (fileSet.has(clean)) return true;
    const prefix = `${clean}/`;
    for (const item of fileSet) if (item.startsWith(prefix)) return true;
    return topDirs.has(clean);
  };
  const dirExists = topDir => {
    const clean = asText(topDir).replace(/^\.\//, '').replace(/^\/+|\/+$/g, '');
    if (!clean || clean.includes('..') || clean.includes('/')) return false;
    return hasInventory ? topDirs.has(clean) : DEFAULT_LOCAL_TOP_DIRS.has(clean);
  };
  return { hasInventory, pathExists, dirExists };
}

function isSiblingActive(sib, currentShort, pathExists) {
  if (currentShort && (currentShort === sib.short.toLowerCase() || sib.aliases.includes(currentShort))) return false;
  return !sib.roots.some(pathExists);
}

function findSiblingForPath(pathStr, currentShort, pathExists) {
  const lower = pathStr.toLowerCase();
  return SIBLINGS.find(sib => isSiblingActive(sib, currentShort, pathExists) && sib.prefixes.some(p => lower.startsWith(p))) ?? null;
}

const COORDINATED_EDIT_RE = /\b(?:coordinat(?:e|ed|ing)\s+(?:changes?|edits?|prs?|updates?|work|releases?|deploys?)|changes?\s+in\s+both\b|edits?\s+in\s+both\b|both\s+repos(?:itories)?\b|across\s+(?:both\s+)?repos(?:itories)?|paired\s+(?:pr|pull\s+request|deploy(?:ment)?|change)|ships?\s+together\s+in\s+both|alongside\s+`?[A-Za-z0-9_./-]+`?|in\s+tandem\s+with|requires?\s+(?:a\s+)?(?:paired\s+)?(?:pr|change|edit|update|deploy(?:ment)?)\s+(?:in|to)\b)/i;
const PATH_EDIT_VERB_RE = /\b(?:update|edit|modify|change|fix|add|create|implement|sync|ship|deploy|coordinate|touch|patch|refactor|remove|delete)\b/i;
const PASSIVE_CONTEXT_RE = /\b(?:error\s+(?:from|calling)|returned\s+by|returns?\s+http|calls?\s+`?[A-Za-z0-9_./-]+`?|mocks?|stubs?|documents?|for\s+reference|as\s+reference|for\s+context|as\s+context)\b/i;
const URL_REFERENCE_BEFORE_RE = /(?:see|ref(?:erence)?|cf\.?|compare|example|from|per)\s*[:(\[]?\s*$/i;
const URL_REFERENCE_AFTER_RE = /^\s*(?:for\s+reference|as\s+reference|for\s+context|as\s+context)\b/i;

function extractRepoHeader(title, body, currentRepo, currentShort, pathExists) {
  const titlePrefix = title.match(/^\s*(?:\[([A-Za-z0-9_.-]+(?:\/[A-Za-z0-9_.-]+)?)\]\s*|([A-Za-z0-9_.-]+(?:\/[A-Za-z0-9_.-]+)?)\s*:\s+)/);
  if (titlePrefix) {
    const raw = (titlePrefix[1] || titlePrefix[2] || '').trim();
    const sib = matchSiblingAlias(raw);
    const isExplicitSlug = raw.includes('/');
    if ((sib && isSiblingActive(sib, currentShort, pathExists)) || (isExplicitSlug && !sameRepository(raw, currentRepo, currentShort))) {
      return { targetRepo: canonicalTargetRepo(raw), signal: 'repo_header', declared: raw };
    }
  }
  for (const line of body.split('\n')) {
    const meta = line.match(/^\s*(?:[-*]\s*)?\*{0,2}(?:target\s+)?(?:repo(?:sitory)?|service)\*{0,2}\s*:\s*`?([A-Za-z0-9_.-]+(?:\/[A-Za-z0-9_.-]+)?)`?\s*$/i);
    if (!meta) continue;
    const declared = meta[1].trim(), lower = declared.toLowerCase();
    if (['none', 'current', 'this', 'local', 'same', 'n/a'].includes(lower)) continue;
    if (!sameRepository(declared, currentRepo, currentShort) && !pathExists(declared)) {
      return { targetRepo: canonicalTargetRepo(declared), signal: 'repo_header', declared };
    }
  }
  return null;
}

function extractForeignUrls(fullText, currentRepo, pathExists) {
  const urls = [];
  const re = /https?:\/\/github\.com\/([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\/(?:blob|tree)\/[^/\s]+\/([^\s)`"'>#?]+)/gi;
  for (const m of fullText.matchAll(re)) {
    const slug = m[1], lower = slug.toLowerCase();
    const sub = normalizeCandidatePath(m[2]);
    if (currentRepo && lower === currentRepo) continue;
    if (sub && pathExists(sub)) continue;
    const idx = m.index ?? 0;
    const lineStart = fullText.lastIndexOf('\n', idx) + 1;
    const before = fullText.slice(Math.max(lineStart, idx - 32), idx);
    const after = fullText.slice(idx + m[0].length, idx + m[0].length + 24);
    const isReference = URL_REFERENCE_BEFORE_RE.test(before) || URL_REFERENCE_AFTER_RE.test(after);
    urls.push({ targetRepo: lower, path: sub, isReference });
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

function detectCrossRepo({ repository, title, body, trustedText, repoFiles }) {
  const currentRepo = asText(repository).trim().toLowerCase();
  const currentShort = currentRepo.includes('/') ? currentRepo.split('/').at(-1) : currentRepo;
  const fullText = [title, body, trustedText].filter(Boolean).join('\n');
  if (!fullText.trim()) return null;

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

  const hasLocalTargets = existingLocal.length > 0 || localGreenfield.length > 0;
  const hasCoordinatedPhrase = COORDINATED_EDIT_RE.test(fullText);
  const hasEditVerb = PATH_EDIT_VERB_RE.test(fullText);
  const header = extractRepoHeader(title, `${body}\n${trustedText}`, currentRepo, currentShort, pathExists);
  const foreignUrls = extractForeignUrls(fullText, currentRepo, pathExists);
  const editUrls = foreignUrls.filter(u => !u.isReference);
  const namesLocalCli = hasLocalCliOrModuleHint(fullText, hasInventory, pathExists);

  const reject = (targetRepo, signals, reason) => ({
    decision: 'reject',
    reasonCode: 'cross_repo',
    intakeClass: 'elsewhere',
    label: 'needs-other-repo',
    targetRepo,
    reason: cleanSingleLine(reason),
    question: null,
    signals: [...new Set(signals)],
  });

  // 1. Explicit foreign header (foreign-only or coordinated alongside local paths).
  if (header) {
    const signals = ['repo_header', ...(hasLocalTargets || hasCoordinatedPhrase ? ['coordinated_multi_repo'] : [])];
    const reason = hasLocalTargets
      ? `Requires coordinated changes with ${header.targetRepo} alongside ${repository || 'this repository'}.`
      : `Issue targets repository ${header.targetRepo} rather than ${repository || 'this repository'}.`;
    return reject(header.targetRepo, signals, reason);
  }

  // 2. Absent foreign sibling root paths (foreign-only or coordinated alongside local paths).
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
    const lineForHit = fullText.split('\n').find(line => line.includes(primary.path)) ?? fullText;
    const isPassiveOnly = !hasCoordinatedPhrase && PASSIVE_CONTEXT_RE.test(lineForHit) && !PATH_EDIT_VERB_RE.test(lineForHit);
    if (!isPassiveOnly && (hasCoordinatedPhrase || hasEditVerb)) {
      return reject(
        primary.sibling.canonical,
        ['foreign_root_path', 'coordinated_multi_repo'],
        `Requires coordinated edits in ${primary.sibling.canonical} (${citedPaths}) alongside ${repository || 'this repository'}.`,
      );
    }
  }

  // 3. Foreign GitHub blob/tree URLs.
  if (foreignUrls.length > 0) {
    if (!hasLocalTargets && !namesLocalCli) {
      const first = foreignUrls[0];
      return reject(
        first.targetRepo,
        ['foreign_url'],
        `Links code in ${first.targetRepo} with no local paths in ${repository || 'this repository'}.`,
      );
    }
    if (editUrls.length > 0 && (hasCoordinatedPhrase || hasEditVerb)) {
      const first = editUrls[0];
      return reject(
        first.targetRepo,
        ['foreign_url', 'coordinated_multi_repo'],
        `Requires coordinated edits in ${first.targetRepo} alongside ${repository || 'this repository'}.`,
      );
    }
  }

  // 4. Sibling repository mentions (foreign-only framing or coordinated multi-repo phrasing).
  for (const sib of SIBLINGS) {
    if (!isSiblingActive(sib, currentShort, pathExists)) continue;
    if (!sib.mentionRe.test(fullText)) continue;
    if (hasCoordinatedPhrase) {
      return reject(
        sib.canonical,
        ['sibling_service', 'coordinated_multi_repo'],
        `Requires coordinated edits in ${sib.canonical} alongside ${repository || 'this repository'}.`,
      );
    }
    if (!hasLocalTargets && !namesLocalCli && (foreignMissing.length > 0 || sib.framedRe.test(fullText))) {
      return reject(
        sib.canonical,
        ['sibling_service'],
        `Targets ${sib.canonical}, which is outside ${repository || 'this repository'}.`,
      );
    }
  }

  // 5. Explicit coordinated multi-repo / external-service edits without a known sibling alias.
  if (hasCoordinatedPhrase) {
    for (const slugMatch of fullText.matchAll(/\b([A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+)\b/g)) {
      const slug = slugMatch[1];
      if (IGNORE_SLASH_RE.test(slug) || PATH_EXT_RE.test(slug) || PATH_PREFIX_RE.test(slug)) continue;
      if (sameRepository(slug, currentRepo, currentShort)) continue;
      if (dirExists(slug.split('/')[0])) continue;
      return reject(
        canonicalTargetRepo(slug),
        ['coordinated_multi_repo'],
        `Requires coordinated changes across ${repository || 'this repository'} and ${canonicalTargetRepo(slug)}.`,
      );
    }
    if (/\b(?:external\s+service|another\s+repo(?:sitory)?|other\s+repo(?:sitory)?|both\s+repos(?:itories)?)\b/i.test(fullText)) {
      return reject(
        'external-service',
        ['coordinated_multi_repo'],
        `Requires coordinated edits or deployment in an external service outside ${repository || 'this repository'}.`,
      );
    }
  }

  return null;
}

const EXPLICIT_DECISION_MARKER_RE = /\b(?:open\s+question|needs?\s+(?:a\s+)?(?:product|pricing|billing|ux|design|policy|human)?\s*decision|decision\s+needed|product\s+decision|pricing\s+decision|ux\s+decision|question\s+for\s+(?:product|design|leadership|maintainers?|serhan|team|humans?))\s*:/i;
const PROSE_DECISION_NEED_RE = /\bneeds?\s+(?:a\s+)?(?:product|pricing|billing|ux|design|policy)(?:\s+(?:and|or)\s+(?:product|pricing|billing|ux|design|policy))*\s+decision\b/i;
const POLICY_DOMAIN_RE = /\b(?:pric(?:e|ing)|tier|plan|seat|cost|billing|free\s+tier|pro\s+tier|paid|quota|limit|default(?:\s+(?:view|mode|output|behavior|option))?|ux|ui|copy|onboarding|product\s+direction|policy|publish(?:ing)?|deprecat(?:e|ion))\b|\$\d+/i;
const CHOICE_PROMPT_RE = /\bshould\s+(?:we|pdd|autopilot|[a-z0-9_`' -]{2,40})\b[^?\n]{2,140}\bor\b[^?\n]{1,100}\?|\boptions?\s*:\s*(?:\(?A\)?|1\))[\s\S]{1,200}(?:\(?B\)?|2\))/i;
const SETTLED_DECISION_RE = /(?:^\s*(?:[-*]\s*)?\*{0,2}(?:decision|resolved|approved|confirmed|locked[- ]?in|final\s+decision|answer)\*{0,2}\s*:|\b(?:go\s+with|let'?s\s+go\s+with|we\s+decided\s+to|choose\s+option\s+[a-c]|pick\s+option\s+[a-c]|option\s+[a-c]\s+(?:is\s+)?approved)\b)/im;
const PRICING_SIGNAL_RE = /\b(?:pric(?:e|ing)|billing|tier|seat|cost|paid|free\s+tier|pro\s+tier)\b|\$\d+/i;
const UX_SIGNAL_RE = /\b(?:ux|ui|default\s+(?:view|mode|output)|layout|onboarding|copy|user[- ]facing)\b/i;

function findDecisionTrigger(sanitizedText) {
  if (!sanitizedText) return null;
  const markerMatch = sanitizedText.match(EXPLICIT_DECISION_MARKER_RE);
  const proseMatch = sanitizedText.match(PROSE_DECISION_NEED_RE);
  const choiceMatch = CHOICE_PROMPT_RE.test(sanitizedText) && POLICY_DOMAIN_RE.test(sanitizedText)
    ? sanitizedText.match(CHOICE_PROMPT_RE)
    : null;
  if (!markerMatch && !proseMatch && !choiceMatch) return null;

  const lastTriggerIdx = Math.max(
    markerMatch ? markerMatch.index : -1,
    proseMatch ? proseMatch.index : -1,
    choiceMatch ? choiceMatch.index : -1,
  );
  const settledMatch = sanitizedText.match(SETTLED_DECISION_RE);
  if (settledMatch && (settledMatch.index ?? 0) > lastTriggerIdx) {
    return null;
  }

  const question = extractDecisionQuestion(sanitizedText, markerMatch, choiceMatch);
  return { question, sourceText: sanitizedText };
}

function extractDecisionQuestion(sanitizedText, markerMatch, choiceMatch) {
  if (markerMatch) {
    const tail = sanitizedText.slice(markerMatch.index + markerMatch[0].length).trim();
    const firstSentence = tail.split(/\n+/)[0]?.trim() ?? '';
    const qEnd = firstSentence.indexOf('?');
    const picked = qEnd >= 0 ? firstSentence.slice(0, qEnd + 1) : firstSentence;
    if (picked.length >= 10) return cleanSingleLine(picked, 300);
  }
  if (choiceMatch) {
    const picked = cleanSingleLine(choiceMatch[0], 300);
    if (picked.length >= 10) return picked;
  }
  const qLine = sanitizedText.split('\n').find(line => line.includes('?'));
  if (qLine) return cleanSingleLine(qLine, 300);
  return 'Which product, pricing, or UX policy option should Autopilot implement before starting?';
}

function detectHumanDecision({ title, body, trustedComments, decisionNote }) {
  if (typeof decisionNote === 'string' && decisionNote.trim().length > 0) return null;

  const baseText = [title, body].filter(Boolean).join('\n');
  let unresolved = findDecisionTrigger(baseText);

  for (const comment of trustedComments) {
    const cText = comment.sanitized;
    if (!cText) continue;
    const nextTrigger = findDecisionTrigger(cText);
    if (SETTLED_DECISION_RE.test(cText) && !nextTrigger) {
      unresolved = null;
      continue;
    }
    if (nextTrigger) {
      unresolved = nextTrigger;
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

  const reason = `Requires an unanswered human decision before implementation: ${unresolved.question}`;
  return {
    decision: 'park',
    reasonCode: 'human_decision',
    intakeClass: 'person',
    label: 'pdd:needs-decision',
    targetRepo: null,
    reason: cleanSingleLine(reason, 300),
    question: cleanSingleLine(unresolved.question, 300),
    signals: [...new Set(signals)],
  };
}

const NEGATED_LOCAL_VERIFY_RE = /\b(?:no|not|never|cannot|can't|without|don't|do\s+not)\s+(?:accept(?:ed)?\s+|use\s+|rely\s+on\s+|allow\s+)?(?:a\s+|any\s+)?(?:local\s+)?(?:unit\s+tests?|mocks?|fakes?|stubs?|dry[- ]?run|fixtures?)\b|\b(?:mocks?|fakes?|stubs?|local\s+tests?)\s+(?:are|is)\s+(?:not\s+accepted|disallowed|rejected|unacceptable|insufficient)\b/i;
const POSITIVE_LOCAL_VERIFY_RE = /\b(?:verify|test|check|prove|covered?)\s+(?:with|using|via|by)\s+(?:local\s+)?(?:unit|integration|automated|fake|mock(?:ed)?|stub(?:bed)?|dry[- ]?run|fixture)\b|\b(?:fake\s+(?:http|api|service|server|port)|mock(?:ed)?\s+(?:http|api|service|server|port)|dry[- ]?run\s+fixture|pdd\s+test|npm\s+test|node\s+--test)\b/i;

const PROD_CREDS_VERIFY_RE = /\b(?:production\s+credentials?|prod(?:uction)?\s+(?:secrets?|api\s+keys?|tokens?|account)|maintainer\s+2fa|2fa\s+credentials?|live\s+(?:api\s+keys?|stripe\s+keys?|registry\s+publish|npm\s+publish))\b/i;
const LIVE_EXTERNAL_VERIFY_RE = /\b(?:live\s+(?:stripe|payment|checkout|webhook|production|dashboard\s+receipt|third[- ]party|external\s+service)|real\s+\$\d+[^.\n]*(?:charge|checkout|payment)|in\s+production\s+with\b|against\s+(?:live|production)\s+(?:stripe|api|service|environment|server))\b/i;
const MANUAL_QA_VERIFY_RE = /\b(?:manual\s+(?:human\s+)?(?:qa|visual)\s+(?:sign[- ]?off|review|check|verification)|manual\s+human\s+qa|physical\s+(?:hardware|device|iphone|android)|real\s+(?:iphone|android|mobile)\s+device|requires?\s+a\s+human\s+to\s+(?:visually|manually)\s+(?:verify|inspect|test))\b/i;
const NAMED_RECIPE_RE = /\b(?:external\s+e2e|verification|e2e)\s+recipe\s*[:`"]+\s*([A-Za-z0-9_.:/-]+)/i;

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

function hasAuthorizedLocalBoundary(fullText, trustedComments, caps) {
  if (!caps.localTests) return false;
  // A later trusted comment explicitly authorizing a local/mocked boundary overrides earlier restrictions.
  for (const comment of [...trustedComments].reverse()) {
    if (POSITIVE_LOCAL_VERIFY_RE.test(comment.sanitized) && !NEGATED_LOCAL_VERIFY_RE.test(comment.sanitized)) {
      return true;
    }
  }
  if (NEGATED_LOCAL_VERIFY_RE.test(fullText)) return false;
  return POSITIVE_LOCAL_VERIFY_RE.test(fullText);
}

function detectUnverifiableBoundary({ title, body, trustedComments, workerCapabilities }) {
  const caps = normalizeCapabilities(workerCapabilities);
  const fullText = [title, body, ...trustedComments.map(c => c.sanitized)].filter(Boolean).join('\n');
  if (!fullText.trim()) return null;

  if (hasAuthorizedLocalBoundary(fullText, trustedComments, caps)) return null;

  const signals = [];
  const reasons = [];

  if (!caps.productionCredentials && PROD_CREDS_VERIFY_RE.test(fullText)) {
    signals.push('missing_prod_credentials');
    reasons.push('production credentials or 2FA unavailable to the worker');
  }
  if (!caps.liveExternalServices && LIVE_EXTERNAL_VERIFY_RE.test(fullText)) {
    signals.push('unavailable_external_e2e');
    reasons.push('live external or production service verification unavailable to the worker');
  }
  const recipeMatch = fullText.match(NAMED_RECIPE_RE);
  if (recipeMatch) {
    const recipe = recipeMatch[1].trim().toLowerCase();
    if (!caps.availableRecipes.includes(recipe)) {
      signals.push('unavailable_external_e2e');
      reasons.push(`external verification recipe "${recipeMatch[1].trim()}" is not available on this worker`);
    }
  }
  if (!caps.humanManualQa && MANUAL_QA_VERIFY_RE.test(fullText)) {
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
  if (crossRepo) return crossRepo;

  const humanDecision = detectHumanDecision({ title, body, trustedComments, decisionNote });
  if (humanDecision) return humanDecision;

  const unverifiable = detectUnverifiableBoundary({ title, body, trustedComments, workerCapabilities });
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
      if (!prev) {
        latestSkips.set(key, { reasonCode: rec.reasonCode, ts });
      } else if (Number.isFinite(ts) && Number.isFinite(prev.ts)) {
        if (ts >= prev.ts) latestSkips.set(key, { reasonCode: rec.reasonCode, ts });
      } else {
        latestSkips.set(key, { reasonCode: rec.reasonCode, ts });
      }
    }
  }

  const byReasonCode = {
    cross_repo: 0,
    human_decision: 0,
    unverifiable_boundary: 0,
  };
  for (const entry of latestSkips.values()) {
    byReasonCode[entry.reasonCode] += 1;
  }
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
        const prev = takenRank.get(key) ?? -1;
        if (rank > prev) takenRank.set(key, rank);
      }
    }
  }

  const taken = takenRank.size;
  let merged = 0;
  for (const rank of takenRank.values()) {
    if (rank === 3) merged += 1;
  }
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
