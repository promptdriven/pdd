// Generated from prompts/cli/autopilot-areas.prompt.md (sha256: 8eb9fa135100da8394e52ed9deecd1ba95fb248653860de00d98a8b1cb0e1c19).
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
const GENERIC_STEMS = new Set(['index', 'main', 'cli', 'utils', 'helpers', 'types', 'config', 'constants', 'readme', 'agents', 'package']);
const stripCtl = text => String(text).replace(/\x1b(?:\[[0-9;?]*[ -/]*[@-~]|\][^\u0007\x1b]*(?:\u0007|\x1b\\)|[@-Z\\-_])/g, '').replace(/[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f-\u009f]/g, '');

export function normalizeAreaPath(raw) {
  if (typeof raw !== 'string') return null;
  let value = stripCtl(raw).trim().replace(/^[`'"]+|[`'"]+$/g, '').trim().replaceAll('\\', '/');
  if (/^area:\s*[a-z0-9_./-]+$/i.test(value)) return `area:${value.slice(5).trim().toLowerCase()}`.slice(0, 120);
  if (/^[a-z]+:\/\//i.test(value)) return null;
  value = value.replace(/^(?:\.\/|\/)+/, '').replace(/\/+/g, '/').replace(/\/+$/, '');
  if (!value || value === '.' || value === '..' || value.startsWith('../') || value.endsWith('/..') || value.includes('/../') || /\s/.test(value)) return null;
  return value.slice(0, 120);
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

function textPathsOf(text) {
  const s = String(text ?? '').slice(0, 32000), out = [];
  for (const m of s.matchAll(/(?<![/\w.-])([\w.-]+(?:\/[\w.-]+)+(?:\.[A-Za-z0-9]{1,8})?)(?![\w/-])/g)) {
    const p = m[1];
    if (!p.startsWith('http') && !p.includes('github.com') && !/^\d+\.\d+/.test(p)) out.push(p);
  }
  return out;
}

export function issueAreas(row, card = null) {
  const cardPaths = [...(Array.isArray(card?.areas) ? card.areas : []), ...(Array.isArray(card?.area_hint) ? card.area_hint : [])];
  return normalizeAreaList([...cardPaths, ...areaLabelsOf(row), ...textPathsOf(`${row?.title ?? ''}\n${row?.body ?? ''}`)], 16);
}

function stemOf(path) {
  if (!path || path.startsWith('area:')) return null;
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

function dirOf(path) {
  if (!path || path.startsWith('area:') || !path.includes('/')) return null;
  const dir = path.slice(0, path.lastIndexOf('/'));
  return TOP_BUCKETS.has(dir.toLowerCase()) ? null : dir;
}

export function areasOverlap(left, right) {
  const aList = normalizeAreaList(left, 32), bList = normalizeAreaList(right, 32);
  for (const a of aList) for (const b of bList) {
    if (a === b) return { overlap: true, reason: a };
    if (a.startsWith('area:') || b.startsWith('area:')) continue;
    if (b.startsWith(`${a}/`)) return { overlap: true, reason: a };
    if (a.startsWith(`${b}/`)) return { overlap: true, reason: b };
    const da = dirOf(a), db = dirOf(b);
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

const cardFor = (cards, n) => {
  const raw = cards instanceof Map ? cards.get(n) : cards?.[n];
  return raw?.card ?? raw ?? null;
};

export function groupReadyIssues(rows, cards, { maxGroupSize = 3 } = {}) {
  const cap = Math.max(1, Math.min(3, Number(maxGroupSize) || 3));
  const list = Array.isArray(rows) ? rows : [], used = new Set(), groups = [];
  for (let i = 0; i < list.length; i++) {
    const primary = list[i], n = primary?.number;
    if (!Number.isSafeInteger(n) || used.has(n)) continue;
    used.add(n);
    const primaryCard = cardFor(cards, n);
    let areas = issueAreas(primary, primaryCard);
    if (cap <= 1 || !isSmallCard(primaryCard)) {
      groups.push({ primary, companions: [], issues: [n], areas });
      continue;
    }
    const members = [n], companions = [];
    const hints = new Set((primaryCard?.group_with ?? []).filter(x => Number.isSafeInteger(x) && x > 0));
    for (let j = i + 1; j < list.length && companions.length < cap - 1; j++) {
      const other = list[j], m = other?.number;
      if (!Number.isSafeInteger(m) || used.has(m)) continue;
      const otherCard = cardFor(cards, m);
      if (!isSmallCard(otherCard)) continue;
      const otherHints = (otherCard?.group_with ?? []).filter(x => Number.isSafeInteger(x) && x > 0);
      const linked = hints.has(m) || otherHints.some(x => members.includes(x) || hints.has(x));
      const otherAreas = issueAreas(other, otherCard);
      const nonLabelA = areas.filter(x => !x.startsWith('area:')), nonLabelB = otherAreas.filter(x => !x.startsWith('area:'));
      const sameArea = (nonLabelA.length > 0 && nonLabelB.length > 0 && areasOverlap(nonLabelA, nonLabelB).overlap)
        || (areas.some(x => x.startsWith('area:')) && areasOverlap(areas, otherAreas).overlap);
      if (!linked && !sameArea) continue;
      used.add(m); members.push(m); companions.push(other);
      for (const h of otherHints) hints.add(h);
      areas = normalizeAreaList([...areas, ...otherAreas], 16);
    }
    groups.push({ primary, companions, issues: members, areas });
  }
  return groups;
}
