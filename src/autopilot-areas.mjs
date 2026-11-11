// Generated from prompts/cli/autopilot-areas.prompt.md (sha256: 91960b80d7896ac6a5f24c94b43d1645c56ad3bd199ad5389505c8571cd4b9c0).
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
