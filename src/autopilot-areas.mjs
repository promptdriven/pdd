// Generated from prompts/cli/autopilot-areas.prompt.md (sha256: e629ad6481d3cd0248a8e0765b0405bc0f98d7d97beef9ee6f2d1ca17bd20c5a).
const login = x => typeof x === 'string' && /^[a-z\d](?:[a-z\d-]{0,38})$/i.test(x);
const repo = x => typeof x === 'string' && /^[\w.-]+\/[\w.-]+$/.test(x);
const owner = x => x === 'autopilot' || login(x) || typeof x === 'string' && x.startsWith('repo:') && repo(x.slice(5));
const validAreas = areas => !(!Array.isArray(areas) || !areas.length || new Set(areas.map(a => a?.name)).size !== areas.length || areas.some(a => !a || typeof a.name !== 'string' || !a.name.trim() || !owner(a.owner) || a.mixed !== undefined && !['whole','split'].includes(a.mixed) || !a.match || Object.keys(a.match).some(k => !['paths','keywords','labels','repositories'].includes(k) || !Array.isArray(a.match[k]) || a.match[k].some(v => typeof v !== 'string' || !v))));
const unsure = source => ({ state: 'unsure', area: '', owner: '', source });
function glob(pattern, path) {
  if (typeof pattern !== 'string' || /[!\[\]\\]/.test(pattern)) return false;
  let value = pattern.replace(/^\//, '');
  if (value.endsWith('/')) value += '**';
  const anchored = pattern.startsWith('/') || value.includes('/');
  const expression = value.split(/(\*\*\/|\*\*|\*|\?)/).map(x => x === '**/' ? '(?:.*/)?' : x === '**' ? '.*' : x === '*' ? '[^/]*' : x === '?' ? '[^/]' : x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('');
  return new RegExp(`${anchored ? '^' : '(?:^|/)'}${expression}(?:/.*)?$`).test(path);
}
export function parseCodeowners(text = '') {
  return text.split(/\r?\n/).map(line => line.replace(/\s*#.*$/, '').trim()).filter(Boolean).flatMap(line => {
    const [pattern, ...owners] = line.split(/\s+/);
    return /[!\[\]\\]/.test(pattern) ? [] : [{ pattern, owners: owners.map(x => x.replace(/^@/, '')) }];
  });
}
export function resolveArea({ areas, codeowners = '', evidence = {} }) {
  const { paths = [], keywords = [], labels = [], repository = '', area = '' } = evidence;
  const resolved = (name, who, source) => ({ state: 'resolved', area: name, owner: who, source });
  if (areas !== undefined) {
    if (!validAreas(areas)) return unsure('config');
    const matches = areas.filter(a => (a.match.paths ?? []).some(rule => paths.some(path => glob(rule, path)))
      || (a.match.keywords ?? []).some(rule => keywords.some(text => text.toLowerCase().includes(rule.toLowerCase())))
      || (a.match.labels ?? []).some(rule => labels.includes(rule))
      || (a.match.repositories ?? []).some(rule => rule.toLowerCase() === repository.toLowerCase()));
    if (matches.length > 1) return unsure('config');
    const selected = matches[0] ?? areas.find(a => a.name === area);
    return selected ? resolved(selected.name, selected.owner, 'config') : unsure('config');
  }
  const entries = parseCodeowners(codeowners);
  const matches = paths.map(path => entries.filter(entry => glob(entry.pattern, path)).at(-1)).filter(Boolean);
  if (matches.length) {
    if (matches.some(row => row.owners.length !== 1 || !login(row.owners[0])) || new Set(matches.flatMap(row => row.owners)).size !== 1) return unsure('codeowners');
    return resolved('codeowners', matches[0].owners[0], 'codeowners');
  }
  if (repository) return unsure('evidence');
  return resolved('default', 'autopilot', 'default');
}
export function draftAreas({ codeowners = '', folders = [], labels = [], assignees = [] }) {
  const areas = parseCodeowners(codeowners).filter(row => row.owners.length === 1 && login(row.owners[0])).map((row, i) => ({ name: `area-${i + 1}`, match: { paths: [row.pattern] }, owner: row.owners[0] }));
  if (!areas.length) for (const folder of folders) areas.push({ name: folder, match: { paths: [`/${folder}/`] }, owner: 'autopilot' });
  if (!areas.length) areas.push({ name: 'default', match: { paths: ['**'] }, owner: 'autopilot' });
  return { areas, signals: { folders, labels, assignees } };
}

// Keep the single-area interface conservative while mixed routing retains all matches.
export function resolveAreas(input) {
  if (input.areas !== undefined) {
    if (!validAreas(input.areas)) return [];
    const matches = input.areas.map(a => resolveArea({ ...input, areas: [a], evidence: { ...input.evidence, area: '' } })).filter(a => a.state === 'resolved');
    if (matches.length) return matches;
  }
  const one = resolveArea(input);
  return one.state === 'resolved' ? [one] : [];
}

const TOP_BUCKETS = new Set(['src', 'lib', 'bin', 'test', 'tests', 'test/helpers', 'tests/helpers', 'test/runtime', 'tests/runtime', 'prompts', 'prompts/cli', 'docs', 'scripts', 'user_stories']);
const CODE_ROOTS = new Set(['src', 'app']);
const MAX_AREAS = 24;
const GENERIC_STEMS = new Set(['index', 'main', 'cli', 'utils', 'helpers', 'types', 'config', 'constants', 'readme', 'agents', 'package']);
const NON_CODE_EXT = /\.(?:mdx?|rst|txt|json|jsonl|ndjson|ya?ml|toml|ini|cfg|conf|lock|csv|tsv|xml|svg|png|jpe?g|gif|webp|ico|pdf|woff2?)$/i;
const stripCtl = text => String(text).replace(/\x1b(?:\[[0-9;?]*[ -/]*[@-~]|\][^\u0007\x1b]*(?:\u0007|\x1b\\)|[@-Z\\-_])/g, '').replace(/[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f-\u009f]/g, '');
const isToken = path => Boolean(path) && (path.startsWith('area:') || path.startsWith('owner:') || path.startsWith('uncertain:'));

function normalizePlainPath(raw) {
  if (typeof raw !== 'string') return null;
  let value = stripCtl(raw).trim().replace(/^[`'"]+|[`'"]+$/g, '').trim().replaceAll('\\', '/');
  if (/^[a-z]+:/i.test(value)) return null;
  value = value.replace(/^(?:\.\/|\/)+/, '').replace(/\/+/g, '/').replace(/\/+$/, '');
  if (!value || value === '.' || value === '..' || value.startsWith('../') || value.endsWith('/..') || value.includes('/../') || /\s/.test(value)) return null;
  return value.slice(0, 120);
}

export function normalizeAreaPath(raw) {
  if (typeof raw !== 'string') return null;
  const value = stripCtl(raw).trim().replace(/^[`'"]+|[`'"]+$/g, '').trim().replaceAll('\\', '/');
  if (/^area:\s*[a-z0-9_./-]+$/i.test(value)) return `area:${value.slice(5).trim().toLowerCase()}`.slice(0, 120);
  if (/^owner:\s*/i.test(value)) {
    const inner = normalizePlainPath(value.slice(value.indexOf(':') + 1));
    return inner ? `owner:${inner}` : null;
  }
  if (/^uncertain:\s*/i.test(value)) {
    const inner = normalizePlainPath(value.slice(value.indexOf(':') + 1));
    return inner ? `uncertain:${inner}` : null;
  }
  return normalizePlainPath(value);
}

export function normalizeAreaList(values, limit = 6) {
  if (!Array.isArray(values)) return [];
  const out = [], seen = new Set();
  for (const item of values) {
    const norm = normalizeAreaPath(item);
    if (!norm || seen.has(norm)) continue;
    seen.add(norm); out.push(norm);
    if (out.length >= limit) break;
  }
  return out;
}

function areaLabelsOf(row) {
  return (row?.labels ?? []).map(l => typeof l === 'string' ? l : l?.name).filter(Boolean)
    .filter(name => /^area:\s*\S+/i.test(name)).map(name => `area:${name.slice(5).trim().toLowerCase()}`);
}

export function parseGitHubIssueUrl(raw) {
  if (typeof raw !== 'string') return null;
  const trimmed = stripCtl(raw).trim().replace(/[.,;:!?)'"\]]+$/, '');
  const candidate = /^https?:\/\//i.test(trimmed)
    ? trimmed
    : /^github\.com\//i.test(trimmed) ? `https://${trimmed}` : null;
  if (!candidate) return null;
  try {
    const parsed = new URL(candidate);
    if ((parsed.protocol !== 'https:' && parsed.protocol !== 'http:')
      || parsed.hostname.toLowerCase() !== 'github.com'
      || parsed.username || parsed.password || parsed.port) return null;
    const m = /^\/([\w.-]+\/[\w.-]+)\/issues\/([1-9]\d*)\/?$/.exec(parsed.pathname);
    if (!m) return null;
    const issue = Number(m[2]);
    return Number.isSafeInteger(issue) ? { repository: m[1].toLowerCase(), issue } : null;
  } catch {
    return null;
  }
}

function textPathsOf(text) {
  const withoutUrls = String(text ?? '').slice(0, 32000).replace(/https?:\/\/[^\s<>)"'`]+/gi, ' ');
  const out = [];
  for (const m of withoutUrls.matchAll(/(?<![/\w.:-])((?:\.[\w-]+|[A-Za-z_][\w-]*)(?:\/[\w.-]+)+(?:\.[A-Za-z0-9]{1,8})?)(?![\w/-])/g)) {
    out.push(m[1].replace(/\.+$/, ''));
  }
  return out;
}

function expandImpliedPaths(paths) {
  const out = [];
  for (const p of paths) {
    out.push(p);
    if (p === 'src/command-catalog.mjs') out.push('docs/cli.md');
  }
  return out;
}

function isSrcOrAppCodePath(path) {
  if (!path || isToken(path) || /\.prompt\.md$/i.test(path) || !path.includes('/')) return false;
  const first = path.slice(0, path.indexOf('/')).toLowerCase();
  if (!CODE_ROOTS.has(first)) return false;
  if (/(?:^|\/)(?:tests?|__tests__|fixtures|examples)\//i.test(path)) return false;
  const base = path.split('/').at(-1) ?? '';
  if (!base || base.startsWith('.') || !/\.[a-z0-9]{1,8}$/i.test(base) || NON_CODE_EXT.test(base)) return false;
  if (/\.(?:test|spec)\.[a-z0-9]+$/i.test(base) || /^(?:test_[^/]+|.+_test)\.[a-z0-9]+$/i.test(base)) return false;
  return true;
}

function parseOwnerEntry(entry) {
  if (!entry) return { prompts: [], uncertain: false };
  if (typeof entry === 'string') {
    const trimmed = entry.trim();
    if (/^(?:uncertain|unsure|unknown)$/i.test(trimmed)) return { prompts: [], uncertain: true };
    const norm = normalizePlainPath(trimmed.replace(/^owner:\s*/i, ''));
    return { prompts: norm ? [norm] : [], uncertain: false };
  }
  if (Array.isArray(entry)) {
    const prompts = entry.map(x => typeof x === 'string' ? normalizePlainPath(x.replace(/^owner:\s*/i, '')) : null).filter(Boolean);
    return { prompts: [...new Set(prompts)], uncertain: false };
  }
  if (typeof entry === 'object') {
    const rawPrompts = [
      ...(Array.isArray(entry.owners) ? entry.owners : []),
      ...(typeof entry.prompt === 'string' ? [entry.prompt] : []),
      ...(typeof entry.owner === 'string' ? [entry.owner] : []),
    ];
    const prompts = [...new Set(rawPrompts.map(x => normalizePlainPath(x.replace(/^owner:\s*/i, ''))).filter(Boolean))];
    const stateUncertain = typeof entry.state === 'string' && /^(?:uncertain|unsure|unknown)$/i.test(entry.state.trim());
    const uncheckedUncertain = entry.certain === false && prompts.length === 0;
    return { prompts, uncertain: stateUncertain || uncheckedUncertain };
  }
  return { prompts: [], uncertain: false };
}

function buildOwnerLookup(owners) {
  if (!owners || typeof owners !== 'object') return null;
  const map = new Map();
  const put = (rawPath, rawEntry) => {
    const key = normalizePlainPath(rawPath);
    if (!key) return;
    const parsed = parseOwnerEntry(rawEntry);
    const prev = map.get(key);
    if (!prev) map.set(key, parsed);
    else map.set(key, {
      prompts: [...new Set([...prev.prompts, ...parsed.prompts])],
      uncertain: prev.uncertain || parsed.uncertain,
    });
  };
  if (owners instanceof Map) {
    for (const [k, v] of owners.entries()) put(k, v);
    return map;
  }
  if (Array.isArray(owners)) {
    for (const row of owners) if (row && typeof row === 'object') put(row.path, row);
    return map;
  }
  const isOwnerReadShape = (owners.owners instanceof Map || (owners.owners && typeof owners.owners === 'object' && !Array.isArray(owners.owners)))
    && ('unchecked' in owners || 'bindings' in owners || owners.owners instanceof Map);
  if (isOwnerReadShape) {
    if (owners.owners instanceof Map) {
      for (const [k, v] of owners.owners.entries()) put(k, v);
    } else {
      for (const [k, v] of Object.entries(owners.owners)) put(k, v);
    }
    if (owners.unchecked instanceof Map) {
      for (const k of owners.unchecked.keys()) put(k, { state: 'uncertain' });
    } else if (owners.unchecked instanceof Set || Array.isArray(owners.unchecked)) {
      for (const k of owners.unchecked) put(k, { state: 'uncertain' });
    } else if (owners.unchecked && typeof owners.unchecked === 'object') {
      for (const k of Object.keys(owners.unchecked)) put(k, { state: 'uncertain' });
    }
    return map;
  }
  if (Array.isArray(owners.files) && ('schema_version' in owners || Object.keys(owners).every(k => k === 'files' || k === 'schema_version'))) {
    for (const row of owners.files) if (row && typeof row === 'object') put(row.path, row);
    return map;
  }
  for (const [k, v] of Object.entries(owners)) put(k, v);
  return map;
}

function stemOf(path) {
  if (!path || isToken(path)) return null;
  const base = path.split('/').at(-1) ?? '';
  const isPrompt = base.endsWith('.prompt.md');
  const stem = base
    .replace(/\.prompt\.md$/i, '')
    .replace(/\.(?:vectors|formal|e2e)\.test\.[a-z0-9]+$/i, '')
    .replace(/(?:\.test|_test)\.[a-z0-9]+$/i, '')
    .replace(/\.[a-z0-9]{1,8}$/i, '')
    .toLowerCase();
  if (!stem || GENERIC_STEMS.has(stem)) return null;
  return { stem, isPrompt };
}

function dirOf(path, ignoreCodeRoots = false) {
  if (!path || isToken(path) || !path.includes('/')) return null;
  const dir = path.slice(0, path.lastIndexOf('/'));
  const lower = dir.toLowerCase();
  if (TOP_BUCKETS.has(lower) || (ignoreCodeRoots && CODE_ROOTS.has(lower))) return null;
  return dir;
}

export function ownerAreas(paths, owners = null) {
  const normalized = expandImpliedPaths(normalizeAreaList(paths, Infinity));
  const lookup = buildOwnerLookup(owners);
  const out = [];
  for (const item of normalized) {
    if (item.startsWith('area:')) continue;
    if (item.startsWith('owner:') || item.startsWith('uncertain:')) {
      out.push(item);
      continue;
    }
    if (/\.prompt\.md$/i.test(item)) {
      out.push(`owner:${item}`);
      continue;
    }
    if (!lookup) continue;
    const found = lookup.get(item);
    if (found?.prompts.length) {
      for (const prompt of found.prompts) out.push(`owner:${prompt}`);
      if (found.uncertain) out.push(`uncertain:${dirOf(item, true) || 'root'}`);
    } else if (found?.uncertain || isSrcOrAppCodePath(item)) {
      out.push(`uncertain:${dirOf(item, true) || 'root'}`);
    }
  }
  return normalizeAreaList(out, Infinity);
}

const isAreaOptions = value => Boolean(value) && typeof value === 'object' && !(value instanceof Map) && !Array.isArray(value)
  && ('owners' in value) && !('areas' in value) && !('area_hint' in value) && !('class' in value);

export function issueAreas(row, card = null, options = undefined) {
  const opts = options === undefined && isAreaOptions(card) ? card : (options ?? {});
  const resolvedCard = options === undefined && isAreaOptions(card) ? (row?.card ?? null) : card;
  const cardPaths = [...(Array.isArray(resolvedCard?.areas) ? resolvedCard.areas : []), ...(Array.isArray(resolvedCard?.area_hint) ? resolvedCard.area_hint : [])];
  const candidates = [...cardPaths, ...areaLabelsOf(row), ...textPathsOf(`${row?.title ?? ''}\n${row?.body ?? ''}`)];
  const raw = [], seen = new Set();
  let pathCount = 0;
  for (const item of candidates) {
    const norm = normalizeAreaPath(item);
    if (!norm || seen.has(norm)) continue;
    if (!isToken(norm)) {
      if (pathCount >= MAX_AREAS) continue;
      pathCount += 1;
    }
    seen.add(norm);
    raw.push(norm);
  }
  const expanded = normalizeAreaList(expandImpliedPaths(raw), Infinity);
  if (opts?.owners === undefined || opts?.owners === null) return expanded;
  return normalizeAreaList([...expanded, ...ownerAreas(expanded, opts.owners)], Infinity);
}

function expandForOverlap(values, owners) {
  const base = expandImpliedPaths(normalizeAreaList(values, Infinity));
  return normalizeAreaList([...base, ...ownerAreas(base, owners)], Infinity);
}

const hasExplicitOwnerTokens = values => Array.isArray(values) && values.some(x => typeof x === 'string' && /^(?:owner|uncertain):/i.test(x.trim()));

export function areasOverlap(left, right, options = {}) {
  const hasOwners = options?.owners !== undefined && options?.owners !== null;
  const ignoreCodeRoots = hasOwners || (hasExplicitOwnerTokens(left) && hasExplicitOwnerTokens(right));
  const owners = hasOwners ? options.owners : null;
  const aList = expandForOverlap(left, owners), bList = expandForOverlap(right, owners);
  for (const a of aList) for (const b of bList) {
    if (a === b) return { overlap: true, reason: a };
    if (a.startsWith('area:') || b.startsWith('area:')) continue;
    if (a.startsWith('owner:') || b.startsWith('owner:')) continue;
    if (a.startsWith('uncertain:') || b.startsWith('uncertain:')) {
      const ua = a.startsWith('uncertain:') ? a.slice(10) : null;
      const ub = b.startsWith('uncertain:') ? b.slice(10) : null;
      if (ua && ub) {
        if (ua === 'root') return { overlap: true, reason: a };
        if (ub === 'root') return { overlap: true, reason: b };
        if (ub.startsWith(`${ua}/`)) return { overlap: true, reason: a };
        if (ua.startsWith(`${ub}/`)) return { overlap: true, reason: b };
        continue;
    }
      const scope = ua ?? ub, plain = ua ? b : a, token = ua ? a : b;
      if (scope !== 'root' && (plain === scope || plain.startsWith(`${scope}/`) || scope.startsWith(`${plain}/`))) {
        return { overlap: true, reason: token };
      }
      continue;
    }
    if (b.startsWith(`${a}/`)) return { overlap: true, reason: a };
    if (a.startsWith(`${b}/`)) return { overlap: true, reason: b };
    const da = dirOf(a, ignoreCodeRoots), db = dirOf(b, ignoreCodeRoots);
    if (da && da === db) return { overlap: true, reason: da };
    const sa = stemOf(a), sb = stemOf(b);
    if (sa && sb && sa.stem === sb.stem && (sa.stem.length >= 3 || sa.isPrompt !== sb.isPrompt)) {
      return { overlap: true, reason: b.startsWith('src/') ? b : a };
    }
  }
  return { overlap: false, reason: null };
}

export function isSmallCard(card) {
  if (!card || card.class !== 'ready') return false;
  if (card.size === 'medium' || card.size === 'large') return false;
  if (card.size === 'small') return true;
  const paths = card.areas ?? card.area_hint ?? [];
  return paths.length <= 2 && !/\b(?:large|major|rewrite|architecture)\b/i.test(String(card.reason ?? ''));
}

const cardFor = (cards, row) => {
  const n = row?.number;
  const raw = cards instanceof Map
    ? cards.get(n)
    : Array.isArray(cards)
      ? cards.find(c => (c?.issue ?? c?.number) === n)
      : cards?.[n];
  return raw?.card ?? raw ?? row?.card ?? (row?.class ? row : null);
};

const isGroupOptions = value => Boolean(value) && typeof value === 'object' && !(value instanceof Map) && !Array.isArray(value)
  && ('owners' in value || 'maxGroupSize' in value || 'cards' in value);

const singleOwnerOf = areaList => {
  if (areaList.some(x => x.startsWith('uncertain:'))) return null;
  const owners = areaList.filter(x => x.startsWith('owner:'));
  return owners.length === 1 ? owners[0] : null;
};

export function groupReadyIssues(rows, cards = null, options = undefined) {
  const opts = options === undefined && isGroupOptions(cards) ? cards : (options ?? {});
  const cardMap = options === undefined && isGroupOptions(cards) ? (cards.cards ?? null) : cards;
  const cap = Math.max(1, Math.min(3, Number(opts.maxGroupSize) || 3));
  const withOwners = opts.owners !== undefined && opts.owners !== null;
  const areaOpts = withOwners ? { owners: opts.owners } : {};
  const list = Array.isArray(rows) ? rows : [], used = new Set(), groups = [];
  for (let i = 0; i < list.length; i++) {
    const primary = list[i], n = primary?.number;
    if (!Number.isSafeInteger(n) || used.has(n)) continue;
    used.add(n);
    const primaryCard = cardFor(cardMap, primary);
    let areas = issueAreas(primary, primaryCard, areaOpts);
    if (cap <= 1 || !isSmallCard(primaryCard)) {
      groups.push({ primary, companions: [], issues: [n], areas });
      continue;
      }
    const members = [n], companions = [];
    const hints = new Set((primaryCard?.group_with ?? []).filter(x => Number.isSafeInteger(x) && x > 0));
    for (let j = i + 1; j < list.length && companions.length < cap - 1; j++) {
      const other = list[j], m = other?.number;
      if (!Number.isSafeInteger(m) || used.has(m)) continue;
      const otherCard = cardFor(cardMap, other);
      if (!isSmallCard(otherCard)) continue;
      const otherHints = (otherCard?.group_with ?? []).filter(x => Number.isSafeInteger(x) && x > 0);
      const linked = hints.has(m) || otherHints.some(x => members.includes(x) || hints.has(x));
      const otherAreas = issueAreas(other, otherCard, areaOpts);
      let sameArea = false;
      if (withOwners) {
        const ownerA = singleOwnerOf(areas), ownerB = singleOwnerOf(otherAreas);
        sameArea = Boolean(ownerA && ownerA === ownerB);
      } else {
        const nonLabelA = areas.filter(x => !x.startsWith('area:')), nonLabelB = otherAreas.filter(x => !x.startsWith('area:'));
        sameArea = (nonLabelA.length > 0 && nonLabelB.length > 0 && areasOverlap(nonLabelA, nonLabelB).overlap)
          || (areas.some(x => x.startsWith('area:')) && areasOverlap(areas, otherAreas).overlap);
      }
      if (!linked && !sameArea) continue;
      used.add(m); members.push(m); companions.push(other);
      for (const h of otherHints) hints.add(h);
      areas = normalizeAreaList([...areas, ...otherAreas], Infinity);
    }
    groups.push({ primary, companions, issues: members, areas });
  }
  return groups;
}
