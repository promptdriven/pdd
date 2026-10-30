// Generated from prompts/cli/product.prompt.md (sha256: 61a1f5848af08a5d3840564f888983512b35a5ffafc3da6af4af965b3bb7d60c).
import { execFile as execute } from 'node:child_process';
import { readFile } from 'node:fs/promises';
import { basename, join } from 'node:path';
import { promisify } from 'node:util';
import { listRuns } from './workflow-runs.mjs';
import { runtimeLines, storyEvidence, startRun } from './workflow-runner.mjs';
import { resolveWorkflowRepository } from './workflow-github.mjs';
import { causeText } from './runtime-output.mjs';

const ordinary = promisify(execute);
const invalid = message => { throw Object.assign(Error(message), { code: 'invalid-product' }); };
const clean = value => String(value ?? '').trim().replace(/^`(.*)`$/, '$1');
const csv = value => !value || value === '-' ? [] : value.split(',').map(clean).filter(Boolean);
const marker = run => `<!-- pdd-product: run=${run} -->`;
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
const portsFor = given => {
  const execFile = given.execFile ?? ((file, args, options) => ordinary(file, args, { ...options, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }));
  return { readFile: path => readFile(path, 'utf8'), listRuns: input => listRuns(input, { execFile }),
    storyEvidence, startRun, resolveRepository: input => resolveWorkflowRepository(input, { execFile }),
    ...given, execFile };
};
async function command(p, cwd, file, args, allowAbsent = false) {
  let response;
  try { response = await p.execFile(file, args, { cwd }); }
  catch (error) {
    if (allowAbsent && Number.isInteger(error.code) && error.code === 1) return null;
    throw Error(`Could not run ${file}: ${causeText(error.message)}`);
  }
  if (!response || typeof response.stdout !== 'string') throw Error(`Invalid ${file} response.`);
  if (response.code !== undefined && response.code !== 0) {
    if (allowAbsent && response.code === 1) return null;
    throw Error(`${file} failed: ${causeText(response.stderr || response.code)}`);
  }
  return response.stdout;
}
async function basePlan(p, { cwd, baseBranch }) {
  if (p.planOnBase) { const value = await p.planOnBase({ cwd, baseBranch }); return value === true || value?.present === true; }
  for (const ref of [`refs/remotes/origin/${baseBranch}`, `refs/heads/${baseBranch}`]) {
    const present = await command(p, cwd, 'git', ['rev-parse', '--verify', '--quiet', `${ref}^{commit}`], true);
    if (present === null) continue;
    return (await command(p, cwd, 'git', ['ls-tree', '--name-only', ref, '--', 'product/plan.md'])).trim() === 'product/plan.md';
  }
  return false;
}
async function documents({ cwd }, p) {
  let map, plan = '';
  try { map = await p.readFile(join(cwd, 'product/map.md')); }
  catch { invalid('product/map.md: cannot read the product map.'); }
  try { plan = await p.readFile(join(cwd, 'product/plan.md')); }
  catch (error) { if (error.code !== 'ENOENT') invalid('product/plan.md: cannot read the plan.'); }
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
export async function readProduct(input, given = {}) { return (await documents(input, portsFor(given))).product; }
const parse = text => { try { return JSON.parse(text); } catch { invalid('GitHub returned unreadable JSON.'); } };
const pages = value => Array.isArray(value) ? value.flat() : invalid('GitHub returned an incomplete list.');
async function issues(p, cwd, repository) {
  const found = pages(parse(await command(p, cwd, 'gh', ['api', '--paginate', '--slurp', `repos/${repository}/issues?state=all&per_page=100`])));
  return found.filter(issue => !issue.pull_request);
}
function exactIssue(items, run) {
  const found = items.filter(issue => typeof issue.body === 'string' && issue.body.includes(marker(run)));
  if (found.length > 1) invalid(`More than one issue names planned run ${run}.`);
  const issue = found[0];
  if (issue && (!Number.isSafeInteger(issue.number) || issue.number < 1)) invalid(`Invalid issue for ${run}.`);
  return issue ?? null;
}
async function pullRequests(p, cwd, repository, issue, local) {
  let numbers = (local?.pr ?? []).map(pr => pr.number).filter(Number.isSafeInteger);
  if (!local) {
    const events = pages(parse(await command(p, cwd, 'gh', ['api', '--paginate', '--slurp', `repos/${repository}/issues/${issue.number}/timeline?per_page=100`])));
    for (const event of events) {
      const url = event.source?.issue?.pull_request?.html_url;
      const number = typeof url === 'string' && url.startsWith(`https://github.com/${repository}/pull/`) ? Number(url.split('/').at(-1)) : null;
      if (Number.isSafeInteger(number) && number > 0) numbers.push(number);
    }
  }
  numbers = [...new Set(numbers)];
  return Promise.all(numbers.map(async number => {
    const pr = parse(await command(p, cwd, 'gh', ['pr', 'view', String(number), '--repo', repository, '--json', 'number,body,state,isDraft,updatedAt,headRefName']));
    if (pr.number !== number || typeof pr.body !== 'string' || !['OPEN', 'MERGED', 'CLOSED'].includes(pr.state)) invalid(`Invalid PR #${number}.`);
    return pr;
  }));
}
const codePr = (pr, local) => local?.pr?.some(saved => saved.number === pr.number && saved.stage === 'code')
  || /<!-- pdd-workflow:[A-Za-z0-9_.-]+:code -->/.test(pr.body) || /PR 2 of this run: the code\./.test(pr.body);
const storyMatches = (name, id) => { const token = basename(name).replace(/\.md$/, ''); return token === id || token.startsWith(`${id}-`) || token.startsWith(`${id}.`); };
const warnings = product => product.runs.filter(run => run.stories.length > 12).map(run => `Warning: ${run.run} has ${run.stories.length} Stories; aim for about 12 per run.`);
async function progress(input, given) {
  const p = portsFor(given), { product } = await documents(input, p), cwd = input.cwd;
  const localRuns = await p.listRuns({ cwd }), repo = await p.resolveRepository({ cwd });
  const found = await issues(p, cwd, repo.repository), parent = localRuns.find(run => run.workflow === 'product');
  const planReady = product.runs.some(run => run.needs.includes('plan PR')) ? await basePlan(p, { cwd, baseBranch: parent?.baseBranch ?? repo.defaultBranch }) : true;
  const details = [];
  for (const run of product.runs) {
    const issue = exactIssue(found, run.run), local = issue && localRuns.find(record => record.number === issue.number);
    const prs = issue ? await pullRequests(p, cwd, repo.repository, issue, local) : [];
    const latest = [...prs].sort((a, b) => String(a.updatedAt ?? '').localeCompare(String(b.updatedAt ?? '')) || a.number - b.number).at(-1);
    const evidence = local ? await p.storyEvidence(local) : latest ? runtimeLines(latest.body).filter(row => row.story).map(row => ({ ...row, current: false, remote: true, at: Date.parse(latest.updatedAt) || 0 })) : [];
    const done = prs.some(pr => pr.state === 'MERGED' && codePr(pr, local));
    details.push({ run, issue, local, prs, evidence, fromPr: !local && latest ? latest.number : null, done });
  }
  const needsFor = run => run.needs.filter(need => need === 'plan PR' ? !planReady : !details.find(detail => detail.run.run === need)?.done);
  const ready = details.filter(detail => !detail.issue && !needsFor(detail.run).length).map(detail => detail.run.run);
  return { p, product, details, ready, needsFor, localRuns, repo };
}
function counts(ids, details) {
  let pass = 0, stale = 0;
  for (const id of new Set(ids)) {
    const evidence = details.flatMap(detail => detail.evidence).filter(row => storyMatches(row.story, id)).sort((a, b) => (a.at ?? 0) - (b.at ?? 0));
    const current = evidence.filter(row => row.current).at(-1), reported = evidence.filter(row => row.remote).at(-1);
    const older = evidence.filter(row => !row.current && !row.remote).at(-1);
    if (current ? current.pass : reported?.pass) pass++;
    else if (!current && !reported && older?.pass) stale++;
  }
  return { total: new Set(ids).size, pass, stale, notRun: new Set(ids).size - pass - stale };
}
export async function productStatus(input, given = {}) {
  const { product, details, ready } = await progress(input, given);
  const core = product.stories.filter(story => story.tag === 'CORE' && product.runs.some(run => run.stories.includes(story.id)));
  const parts = product.parts.map(part => ({ part: part.part, ...counts(core.filter(story => story.part === part.part).map(story => story.id), details) }));
  const journeyIds = product.runs.filter(run => run.part === 'all').flatMap(run => run.stories);
  if (journeyIds.length) parts.push({ part: 'journeys', ...counts(journeyIds, details) });
  return { name: product.name, size: product.size, parts,
    slices: [...new Set(product.runs.map(run => run.slice))].map(slice => ({ slice, ...counts(product.runs.filter(run => run.slice === slice).flatMap(run => run.stories).filter(id => journeyIds.includes(id) || core.some(story => story.id === id)), details) })),
    runs: details.map(detail => ({ run: detail.run.run, issue: detail.issue?.number ?? null,
      state: detail.done ? 'merged' : detail.local ? `${detail.local.state}${detail.local.stage?.id ? ` (step: ${detail.local.stage.id})` : ''}` : detail.prs.length ? detail.prs.map(pr => `PR #${pr.number} (${pr.isDraft ? 'draft' : pr.state.toLowerCase()})`).join(', ') : detail.issue ? 'issue ready' : 'planned',
      prs: detail.prs.map(pr => pr.number), fromPr: detail.fromPr })), ready, questions: product.questions };
}
export async function productNext(input, given = {}) {
  const { product, details, ready, needsFor } = await progress(input, given);
  return { ready, waiting: details.filter(detail => !detail.issue && needsFor(detail.run).length).map(detail => ({ run: detail.run.run, needs: needsFor(detail.run) })),
    guidance: product.size === 'small' ? 'run one feature run' : ready.length >= 2 ? 'These can run in parallel, or one person can start them in order.' : '' };
}
export async function productStart({ cwd, run, noRun = false, agent = 'codex', packageRoot }, given = {}) {
  let issue = null, created = false;
  try {
    const p = portsFor(given), { product, boundaries } = await documents({ cwd }, p), planned = product.runs.find(row => row.run === run);
    if (!planned) invalid(`Unknown planned run ${run}.`);
    if (!['codex', 'claude'].includes(agent)) invalid(`Unknown agent ${agent}.`);
    const state = await progress({ cwd }, given), { repo, localRuns } = state;
    issue = state.details.find(detail => detail.run.run === run).issue;
    const parent = localRuns.find(record => record.workflow === 'product');
    if (!issue) {
      const contractFiles = product.size === 'small' ? [] : [...new Set([...boundaries.filter(row => planned.part === 'all' || [row.From, row.To].includes(planned.part)).map(row => row.Contract), 'contracts/world.md'])];
      const body = [parent ? `Part of #${parent.number} (product).` : '', `Plan: product/${product.size === 'small' ? 'map' : 'plan'}.md, run ${run}, slice ${planned.slice}.`,
        `Stories: ${planned.stories.join(', ')}.`, ...planned.stories.map(id => `${id}: ${(product.stories.find(story => story.id === id)?.story ?? product.journeys.find(story => story.id === id)?.journey)}`),
        `Folder: ${product.parts.find(part => part.part === planned.part)?.folder ?? 'user_stories/journeys'}.${contractFiles.length ? ` Contracts: ${contractFiles.join(', ')}.` : ''}`,
        contractFiles.length ? 'Other parts are fakes from their contracts. Do not change contracts/ in this run.' : '', marker(run)].filter(Boolean).join('\n');
      const payload = { repository: repo.repository, title: `${product.name}: ${run} (${planned.stories.join(', ')})`, body };
      const response = p.createIssue ? await p.createIssue(payload) : { url: await command(p, cwd, 'gh',
        ['issue', 'create', '--repo', payload.repository, '--title', payload.title, '--body', payload.body]) };
      const url = typeof response?.url === 'string' ? response.url.trim() : '';
      const match = /^https:\/\/github\.com\/([^/]+\/[^/]+)\/issues\/([1-9][0-9]*)$/.exec(url);
      if (!match || match[1].toLowerCase() !== repo.repository.toLowerCase()) invalid('Issue creation was not confirmed. Inspect GitHub before trying again.');
      issue = { number: Number(match[2]) }; created = true;
    }
    const warning = [...warnings(product).filter(text => text.startsWith(`Warning: ${run} `)), ...(state.needsFor(planned).length ? [`Advice: ${run} still needs ${state.needsFor(planned).join(', ')}.`] : [])].join('\n');
    if (noRun) return { exitCode: 0, message: [warning, `Issue #${issue.number} ready for ${run}.`].filter(Boolean).join('\n'), issue: issue.number, created, started: false };
    const reply = await p.startRun({ name: 'feature', issue: issue.number, agent, cwd, ...(packageRoot === undefined ? {} : { packageRoot }) });
    if (!reply || !Number.isInteger(reply.exitCode) || typeof reply.message !== 'string') throw Error('Invalid feature workflow reply.');
    return { ...reply, message: [warning, reply.message].filter(Boolean).join('\n'), issue: issue.number, created, started: reply.exitCode === 0 };
  } catch (error) { return { exitCode: 1, message: causeText(error.message) || 'The planned run could not start.', issue: issue?.number ?? null, created, started: false }; }
}
export async function runProduct(input, given = {}) {
  try {
    if (input.command === 'start') return productStart(input, given);
    const product = await readProduct(input, given), warning = warnings(product);
    if (input.command === 'next') {
      const next = await productNext(input, given);
      return { exitCode: 0, message: [...warning, next.guidance,
        next.ready.length ? `Can start now: ${next.ready.join(', ')}.` : 'Can start now: none.',
        ...next.ready.map(run => `pdd product start ${run}`), ...next.waiting.map(row => `${row.run}: waits for ${row.needs.join(', ')}.`)].filter(Boolean).join('\n') };
    }
    if (input.command !== 'status') invalid('Unknown product command.');
    const status = await productStatus(input, given);
    return { exitCode: 0, message: input.json ? JSON.stringify(status) : [
      `${status.name} (${status.size}, ${product.parts.length} parts). Plan: product/${product.size === 'small' ? 'map' : 'plan'}.md`, ...warning,
      'Part  Stories pass  Stale  Not run', ...status.parts.map(part => `${part.part}  ${part.pass} of ${part.total}  ${part.stale}  ${part.notRun}`),
      ...status.runs.map(run => `${run.run}: ${run.state}${run.issue ? ` · issue #${run.issue}` : ''}${run.fromPr ? ` · from PR #${run.fromPr}` : ''}`),
      ...status.slices.map(slice => `Slice ${slice.slice}: ${slice.pass} of ${slice.total} pass.`),
      `Can start now: ${status.ready.join(', ') || 'none'}. Questions open: ${status.questions.join(', ') || 'none'}.`,
      'Stale = passed on older files; a contract or prompt changed since.' ].join('\n') };
  } catch (error) { return { exitCode: 1, message: causeText(error.message) || 'The product could not be read.' }; }
}
