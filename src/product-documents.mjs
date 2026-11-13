// Generated from prompts/cli/product.prompt.md (sha256: cef023803dd7da9161cadd59566990dcc67af086f476c5db8919ddc4728c6278).
export const invalid = message => { throw Object.assign(Error(message), { code: 'invalid-product' }); };
const clean = value => String(value ?? '').trim().replace(/^`(.*)`$/, '$1');
const csv = value => !value || value === '-' ? [] : value.split(',').map(clean).filter(Boolean);
const columns = {
  Parts: ['Part', 'Folder', 'What it is'], Stories: ['Id', 'Part', 'Story', 'Tag'],
  Journeys: ['Id', 'Journey', 'Stories'], Questions: ['Id', 'Question', 'Recommendation', 'Example', 'Answer'],
  Runs: ['Run', 'Part', 'Slice', 'Stories', 'Needs'], Boundaries: ['From', 'To', 'What crosses', 'Contract'],
};
function tableCells(line) {
  const text = line.trim(), cells = [''];
  for (const character of text) {
    const last = cells.length - 1;
    if (character !== '|') cells[last] += character;
    else if (/\\*$/.exec(cells[last])[0].length % 2) cells[last] = cells[last].slice(0, -1) + '|';
    else cells.push('');
  }
  if (text.startsWith('|')) cells.shift();
  if (cells.at(-1) === '') cells.pop();
  return cells.map(clean);
}
const rows = (text, section, file) => {
  const body = text.split(/^##\s+/m).find(piece => piece.split(/\r?\n/, 1)[0].trim() === section);
  if (!body) return [];
  const table = body.split(/\r?\n/).filter(line => /^\s*\|/.test(line)).map(tableCells);
  const heading = table.shift();
  for (const column of heading ? columns[section] : []) if (!heading.includes(column)) invalid(`${file}: ${section} is missing column ${column}.`);
  return heading ? table.filter(row => !row.every(cell => /^:?-+:?$/.test(cell))).map(row => Object.fromEntries(heading.map((key, i) => [key, row[i] ?? '']))) : [];
};
const duplicate = (items, key, file) => { const seen = new Set(); for (const item of items) { if (!item[key] || seen.has(item[key])) invalid(`${file}: duplicate or empty ${key} ${item[key]}.`); seen.add(item[key]); } };

export function parseProductDocuments({mapText, planText = ''}) {
  const map = String(mapText), plan = String(planText);
  const name = /^#\s+(.+?)(?::\s*map)?\s*$/m.exec(map)?.[1], size = /^Size:\s*(small|medium|large)\b/im.exec(map)?.[1].toLowerCase();
  if (!name || !size) invalid('product/map.md: name or Size is missing.');
  const mapRows = section => rows(map, section, 'product/map.md'), planRows = section => rows(plan, section, 'product/plan.md');
  const parts = mapRows('Parts').map(row => ({ part: row.Part, folder: row.Folder, description: row['What it is'] }));
  const stories = mapRows('Stories').map(row => ({ id: row.Id, part: row.Part, story: row.Story, tag: row.Tag }));
  const journeys = mapRows('Journeys').map(row => ({ id: row.Id, journey: row.Journey, stories: csv(row.Stories) }));
  duplicate(parts, 'part', 'product/map.md'); duplicate(stories, 'id', 'product/map.md'); duplicate(journeys, 'id', 'product/map.md');
  for (const story of stories) if (!parts.some(part => part.part === story.part)) invalid(`product/map.md: unknown part ${story.part}.`);
  for (const journey of journeys) for (const id of journey.stories) if (!stories.some(story => story.id === id)) invalid(`product/map.md: unknown Story ${id}.`);
  let runs = planRows('Runs').map(row => ({ run: row.Run, part: row.Part, slice: row.Slice, stories: csv(row.Stories), needs: csv(row.Needs) }));
  if (!plan.trim() && size === 'small' && parts.length === 1) runs = [{ run: parts[0].part, part: parts[0].part, slice: '1', stories: stories.filter(story => story.tag === 'CORE').map(story => story.id), needs: [] }];
  if (!runs.length) invalid('product/plan.md: no planned runs.');
  duplicate(runs, 'run', 'product/plan.md');
  for (const run of runs) {
    if (run.part !== 'all' && !parts.some(part => part.part === run.part)) invalid(`product/plan.md: unknown part ${run.part}.`);
    for (const id of run.stories) if (!(run.part === 'all' ? journeys : stories.filter(story => story.part === run.part)).some(story => story.id === id)) invalid(`product/plan.md: unknown Story ${id}.`);
    for (const need of run.needs) if (need !== 'plan PR' && !runs.some(other => other.run === need)) invalid(`product/plan.md: unknown need ${need}.`);
  }
  return { product: { name, size, parts, stories, journeys, runs, questions: mapRows('Questions').filter(row => !row.Answer || row.Answer === '-').map(row => row.Id) }, boundaries: planRows('Boundaries') };
}

export function parseProductWorldWriters({worldText}) {
  // Fences and unrelated tables cannot acquire world-write authority.
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
    if (writers.has(key) && writers.get(key) !== writer) throw Object.assign(Error(`${key} has two writers.`), {code:'world-writer-conflict'});
    writers.set(key,writer); result.push({key,writer});
  }
  return result;
}
