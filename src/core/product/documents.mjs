// Generated from prompts/cli/product.prompt.md.
// Pure product map/plan/world-writer parser and topological wave planner (Layer 1 core).
import {
  SHARED_SURFACE_COLS,
  THROUGH,
  clean,
  csv,
  duplicate,
  findSectionLines,
  invalid,
  isSeparatorRow,
  rows,
  rowsWithMeta,
  tableCells,
  unwrapHeadingToken,
} from './markdown-utils.mjs';
import { parsePlanBoundaryOperations, parsePlanPrompts } from './plan-audit.mjs';

function parsePlanThrough(plan) {
  const preamble = plan.split(/^##\s+/m, 1)[0];
  const matches = [...preamble.matchAll(/^Through:[ \t]*(.*)$/gim)];
  if (!matches.length) return undefined;
  if (matches.length > 1) invalid('product/plan.md: duplicate Through declaration.');
  const token = clean(matches[0][1].trim().split(/\s+/)[0] ?? '').toLowerCase();
  if (!THROUGH.includes(token)) invalid(`product/plan.md: invalid Through value ${token || '(empty)'}; use prompt-pr or code.`);
  return token;
}

function parsePlanBase(plan) {
  const preamble = plan.split(/^##\s+/m, 1)[0];
  const matches = [...preamble.matchAll(/^Base:[ \t]*(.*)$/gim)];
  if (!matches.length) return undefined;
  if (matches.length > 1) invalid('product/plan.md: duplicate Base declaration.');
  const token = clean(matches[0][1].trim().split(/\s+/)[0] ?? '');
  return token || undefined;
}

function parsePlanIssue(plan) {
  const preamble = plan.split(/^##\s+/m, 1)[0];
  const match = /^Issue:[ \t]*#?([1-9][0-9]*)\b/im.exec(preamble);
  if (!match) return undefined;
  const n = Number(match[1]);
  return Number.isSafeInteger(n) && n > 0 ? n : undefined;
}

function parseRulesToCheck(mapText) {
  const sec = findSectionLines(mapText, 'Rules to check', { caseInsensitive: true });
  if (!sec) return { hasSection: false, rules: [] };

  const tables = [];
  let current = [];
  for (const item of sec.lines) {
    if (/^\s*\|/.test(item.text)) current.push({ lineNo: item.lineNo, cells: tableCells(item.text) });
    else if (current.length) { tables.push(current); current = []; }
  }
  if (current.length) tables.push(current);

  if (tables.length > 0) {
    const findCol = (heading, names) => heading.findIndex(col => names.includes(col.toLowerCase()));
    const parseCols = heading => ({
      idIdx: findCol(heading, ['id']),
      ownerIdx: findCol(heading, ['owner']),
      ruleIdx: findCol(heading, ['rule']),
      verifiedIdx: findCol(heading, ['verified by', 'verified_by', 'verified']),
    });
    const rules = [];
    for (const block of tables) {
      let cols = parseCols(block[0].cells);
      if (cols.idIdx < 0) invalid('product/map.md: Rules to check is missing column Id.');
      if (cols.ownerIdx < 0) invalid('product/map.md: Rules to check is missing column Owner.');
      if (cols.ruleIdx < 0) invalid('product/map.md: Rules to check is missing column Rule.');
      if (cols.verifiedIdx < 0) invalid('product/map.md: Rules to check is missing column Verified By.');
      for (let i = 1; i < block.length; i++) {
        const cells = block[i].cells;
        if (isSeparatorRow(cells)) continue;
        if (i + 1 < block.length && isSeparatorRow(block[i + 1].cells)) {
          const nextCols = parseCols(cells);
          if (nextCols.idIdx >= 0 && nextCols.ownerIdx >= 0 && nextCols.ruleIdx >= 0 && nextCols.verifiedIdx >= 0) {
            cols = nextCols; continue;
          }
        }
        const rawVerified = cells[cols.verifiedIdx] ?? '';
        rules.push({
          id: cells[cols.idIdx] ?? '',
          owner: cells[cols.ownerIdx] ?? '',
          rule: cells[cols.ruleIdx] ?? '',
          verifiedBy: rawVerified === '-' ? '' : rawVerified,
        });
      }
    }
    duplicate(rules, 'id', 'product/map.md');
    for (const entry of rules) {
      if (entry.id === '-') invalid('product/map.md: Rules to check row has invalid Id -.');
      const owners = csv(entry.owner).filter(o => o !== '-');
      if (!entry.owner || entry.owner === '-' || owners.length === 0) invalid(`product/map.md: Rules to check row ${entry.id} is missing Owner.`);
      if (!entry.rule || entry.rule === '-') invalid(`product/map.md: Rules to check row ${entry.id} is missing Rule.`);
    }
    return { hasSection: true, rules };
  }

  const bulletRules = [], proseRules = [];
  for (const item of sec.lines) {
    const trimmed = item.text.trim();
    if (!trimmed || /^#{3,6}\s+/.test(trimmed)) continue;
    const bullet = /^(?:[-*+]|\d+[.)])\s+(.+)$/.exec(trimmed);
    if (bullet) {
      const text = clean(bullet[1]);
      if (text && text !== '-' && !/^none\.?$/i.test(text)) bulletRules.push({ id: '', owner: 'all', rule: text, verifiedBy: '' });
    } else if (trimmed !== '-' && !/^none\.?$/i.test(trimmed)) {
      proseRules.push({ id: '', owner: 'all', rule: clean(trimmed), verifiedBy: '' });
    }
  }
  return { hasSection: true, rules: bulletRules.length ? bulletRules : proseRules };
}

function parseSharedSurfaceRunLines(runSection, runs) {
  if (!runSection) return new Map();
  const byRun = new Map(runs.map(r => [r.run, r]));
  const perRun = new Map();
  let currentRun = null;
  const addFor = (runName, list) => {
    if (!byRun.has(runName)) invalid(`product/plan.md: unknown run ${runName}.`);
    if (!perRun.has(runName)) perRun.set(runName, []);
    perRun.get(runName).push(...list);
  };
  const stripLeadingBold = s => String(s ?? '').replace(/^\*\*[ \t]*/, '');

  for (const item of runSection.lines) {
    const trimmed = item.text.trim();
    if (!trimmed || /^\s*\|/.test(item.text)) continue;
    const sub = /^#{3,6}[ \t]+(.+)$/.exec(trimmed);
    if (sub) {
      const candidate = unwrapHeadingToken(unwrapHeadingToken(sub[1].trim().split(/\s+/)[0] ?? '').split(/[:(—–,]/)[0] ?? '');
      currentRun = byRun.has(candidate) ? candidate : null;
      continue;
    }
    const line = trimmed.replace(/^(?:[-*+]|\d+[.)])[ \t]+/, '');
    const paren = /^(?:\*\*)?(?:Shared[ \t]+surfaces?|Also[ \t]+updates)[ \t]*\(([^()\r\n]+)\)(?:\*\*)?[ \t]*:[ \t]*(.*)$/i.exec(line);
    if (paren) { addFor(unwrapHeadingToken(paren[1]), csv(stripLeadingBold(paren[2]))); continue; }
    const prefixed = /^([*`]{0,3}[A-Za-z0-9._-]+[*`]{0,3})[ \t]*:[ \t]*(?:\*\*)?(?:Shared[ \t]+surfaces?|Also[ \t]+updates)(?:\*\*)?[ \t]*:[ \t]*(.*)$/i.exec(line);
    if (prefixed) { addFor(unwrapHeadingToken(prefixed[1]), csv(stripLeadingBold(prefixed[2]))); continue; }
    const plain = /^(?:\*\*)?(?:Shared[ \t]+surfaces?|Also[ \t]+updates)(?:\*\*)?[ \t]*:[ \t]*(.*)$/i.exec(line);
    if (plain && currentRun) addFor(currentRun, csv(stripLeadingBold(plain[1])));
  }
  return perRun;
}

/** Group planned runs into deterministic topological waves (`Wave 1`, `Wave 2`, ...). */
export function computeProductWaves(runs = []) {
  const list = Array.isArray(runs) ? runs : [];
  const names = new Set(list.map(r => r.run));
  const placed = new Set();
  const waves = [];
  while (placed.size < list.length) {
    const waveRuns = list
      .filter(r => !placed.has(r.run) && (r.needs ?? []).filter(n => n !== 'plan PR' && names.has(n)).every(n => placed.has(n)))
      .map(r => r.run);
    if (!waveRuns.length) break;
    waves.push({ wave: waves.length + 1, runs: waveRuns });
    for (const name of waveRuns) placed.add(name);
  }
  const cyclic = list.filter(r => !placed.has(r.run)).map(r => r.run);
  if (cyclic.length) waves.push({ wave: waves.length + 1, runs: cyclic, cyclic: true });
  return waves;
}

export function parseProductDocuments({ mapText, planText = '' }) {
  const map = String(mapText), plan = String(planText);
  const name = /^#\s+(.+?)(?::\s*map)?\s*$/m.exec(map)?.[1];
  const size = /^Size:\s*(small|medium|large)\b/im.exec(map)?.[1].toLowerCase();
  if (!name || !size) invalid('product/map.md: name or Size is missing.');
  const through = parsePlanThrough(plan);
  const base = parsePlanBase(plan);
  const planIssue = parsePlanIssue(plan);
  const mapRows = section => rows(map, section, 'product/map.md');
  const planRows = section => rows(plan, section, 'product/plan.md');
  const parts = mapRows('Parts').map(row => ({ part: row.Part, folder: row.Folder, description: row['What it is'] }));
  const stories = mapRows('Stories').map(row => ({ id: row.Id, part: row.Part, story: row.Story, tag: row.Tag }));
  const journeys = mapRows('Journeys').map(row => ({ id: row.Id, journey: row.Journey, stories: csv(row.Stories) }));
  const rulesInfo = parseRulesToCheck(map);
  duplicate(parts, 'part', 'product/map.md');
  duplicate(stories, 'id', 'product/map.md');
  duplicate(journeys, 'id', 'product/map.md');
  for (const story of stories) if (!parts.some(part => part.part === story.part)) invalid(`product/map.md: unknown part ${story.part}.`);
  for (const journey of journeys) for (const id of journey.stories) if (!stories.some(story => story.id === id)) invalid(`product/map.md: unknown Story ${id}.`);

  const runsMeta = rowsWithMeta(plan, 'Runs', 'product/plan.md');
  const sharedCol = (runsMeta.heading ?? []).find(col => SHARED_SURFACE_COLS.has(col.toLowerCase()));
  let runs = runsMeta.rows.map(({ values: row }) => {
    const partTokens = csv(row.Part);
    return {
      run: row.Run,
      part: partTokens[0] ?? '',
      slice: row.Slice,
      stories: csv(row.Stories),
      needs: csv(row.Needs),
      _rawShared: [...partTokens.slice(1), ...(sharedCol ? csv(row[sharedCol]) : [])],
    };
  });
  if (!plan.trim() && size === 'small' && parts.length === 1) {
    runs = [{ run: parts[0].part, part: parts[0].part, slice: '1', stories: stories.filter(s => s.tag === 'CORE').map(s => s.id), needs: [], _rawShared: [] }];
  }
  if (!runs.length) invalid('product/plan.md: no planned runs.');
  duplicate(runs, 'run', 'product/plan.md');

  const perRunShared = parseSharedSurfaceRunLines(runsMeta.section, runs);
  runs = runs.map(entry => {
    const sharedSurfaces = [];
    for (const surface of [...entry._rawShared, ...(perRunShared.get(entry.run) ?? [])]) {
      if (surface === entry.part) continue;
      if (surface === 'all' || !parts.some(part => part.part === surface)) invalid(`product/plan.md: unknown shared surface ${surface}.`);
      if (!sharedSurfaces.includes(surface)) sharedSurfaces.push(surface);
    }
    return {
      run: entry.run, part: entry.part, slice: entry.slice, stories: entry.stories, needs: entry.needs,
      ...(sharedSurfaces.length ? { sharedSurfaces } : {}),
    };
  });

  for (const run of runs) {
    if (run.part !== 'all' && !parts.some(part => part.part === run.part)) invalid(`product/plan.md: unknown part ${run.part}.`);
    const allowedParts = new Set([run.part, ...(run.sharedSurfaces ?? [])]);
    for (const id of run.stories) {
      const ok = run.part === 'all'
        ? journeys.some(j => j.id === id) || stories.some(s => s.id === id && (run.sharedSurfaces ?? []).includes(s.part))
        : stories.some(s => s.id === id && allowedParts.has(s.part));
      if (!ok) invalid(`product/plan.md: unknown Story ${id}.`);
    }
    for (const need of run.needs) if (need !== 'plan PR' && !runs.some(other => other.run === need)) invalid(`product/plan.md: unknown need ${need}.`);
  }

  const promptsInfo = parsePlanPrompts(plan, parts);
  const boundariesInfo = parsePlanBoundaryOperations(plan, parts);
  const boundaries = planRows('Boundaries');
  const product = {
    name, size,
    ...(through ? { through } : {}),
    ...(base ? { base } : {}),
    ...(planIssue ? { issue: planIssue } : {}),
    parts, stories, journeys, runs,
    questions: mapRows('Questions').filter(row => !row.Answer || row.Answer === '-').map(row => row.Id),
    ...(rulesInfo.rules.length ? { rulesToCheck: rulesInfo.rules } : {}),
    ...(promptsInfo.prompts.length ? { prompts: promptsInfo.prompts.map(({ path, part }) => ({ path, part })) } : {}),
  };
  return { product, boundaries, prompts: promptsInfo.prompts, boundaryOperations: boundariesInfo.operations };
}

export function parseProductWorldWriters({ worldText }) {
  const tables = []; let fence = null, table = [];
  const flush = () => { if (table.length) tables.push(table); table = []; };
  for (const line of String(worldText).split(/\r?\n/)) {
    const mark = /^ {0,3}(`{3,}|~{3,})/.exec(line);
    if (mark) { flush(); if (!fence) fence = mark[1]; else if (mark[1][0] === fence[0] && mark[1].length >= fence.length) fence = null; continue; }
    if (fence) continue;
    if (/^\s*\|/.test(line)) table.push(tableCells(line)); else flush();
  }
  flush();
  const matches = tables.filter(rows => rows[0].includes('Key') && rows[0].includes('Writer'));
  if (matches.length > 1) invalid('contracts/world.md: ambiguous writer tables.');
  if (!matches.length) return [];
  const [heading, ...data] = matches[0], writers = new Map(), result = [];
  for (const row of data.filter(row => !row.every(cell => /^:?-+:?$/.test(cell)))) {
    const key = row[heading.indexOf('Key')], writer = row[heading.indexOf('Writer')];
    if (!key || !writer) invalid('contracts/world.md: declaration has an empty Key or Writer.');
    if (writers.has(key) && writers.get(key) !== writer) throw Object.assign(Error(`${key} has two writers.`), { code: 'world-writer-conflict' });
    writers.set(key, writer); result.push({ key, writer });
  }
  return result;
}
