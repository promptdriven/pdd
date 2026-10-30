// Generated from prompts/cli/product.prompt.md (sha256: 6886c6719232947b316ad2d63fb17464086186e7377ef1eff180115b298fa602).
import { execFile as execute } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { existsSync, realpathSync } from 'node:fs';
import { mkdtemp, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
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
const rows = (text, section, file, required = columns[section]) => {
  const body = section === null ? text : text.split(/^##\s+/m).find(piece => piece.split(/\r?\n/, 1)[0].trim() === section);
  if (!body) { if (section === null) invalid(`${file}: table is missing column ${required[0]}.`); return []; }
  const table = body.split(/\r?\n/).filter(line => /^\s*\|/.test(line)).map(tableCells);
  const heading = table.shift();
  for (const column of heading || section === null ? required : []) if (!heading?.includes(column)) invalid(`${file}: ${section ?? 'table'} is missing column ${column}.`);
  return heading ? table.filter(row => !row.every(cell => /^:?-+:?$/.test(cell))).map(row => Object.fromEntries(heading.map((key, i) => [key, row[i] ?? '']))) : [];
};
const duplicate = (items, key, file) => { const seen = new Set(); for (const item of items) { if (!item[key] || seen.has(item[key])) invalid(`${file}: duplicate or empty ${key} ${item[key]}.`); seen.add(item[key]); } };
const portsFor = given => {
  const execFile = given.execFile ?? ((file, args, options) => ordinary(file, args, { ...options, encoding: 'utf8', maxBuffer: 8 * 1024 * 1024 }));
  const p = { readFile: path => readFile(path, 'utf8'), listRuns: input => listRuns(input, { execFile }),
    storyEvidence, startRun, resolveRepository: input => resolveWorkflowRepository(input, { execFile }),
    ...given, execFile };
  p.issuePage ??= async ({ cwd, repository, marker, page, perPage }) => {
    const quoted = marker.replace(/\\/g, '\\\\').replace(/"/g, '\\"');
    const query = new URLSearchParams({ q: `repo:${repository} is:issue in:body "${quoted}"`, sort: 'created', order: 'asc', page, per_page: perPage });
    return parse(await command(p, cwd, 'gh', ['api', `search/issues?${query}`, '--jq', '{items:[.items[]|{number,body,user:{login:.user.login},author_association,created_at,state}],total_count,incomplete_results}']));
  };
  p.timelinePage ??= async ({ cwd, repository, issue, page, perPage }) => parse(await command(p, cwd, 'gh',
    ['api', `repos/${repository}/issues/${issue}/timeline?per_page=${perPage}&page=${page}`, '--jq', '[.[]|{event,source:{issue:{pull_request:{html_url:.source.issue.pull_request.html_url}}}}]']));
  p.pullRequest ??= async ({ cwd, repository, number }) => parse(await command(p, cwd, 'gh', ['pr', 'view', String(number), '--repo', repository, '--json',
    'number,url,body,state,isDraft,updatedAt,headRefName,isCrossRepository,headRepository,headRepositoryOwner']));
  p.currentActor ??= async ({ cwd }) => parse(await command(p, cwd, 'gh', ['api', 'user', '--jq', '{login}']));
  const owned = new Map();
  p.openBaseSource ??= input => openBaseSource(input, p, owned);
  p.closeBaseSource ??= async ({ handle }) => {
    const directory = owned.get(handle);
    if (!directory) throw Error('The base-source view is not owned by this command.');
    await rm(directory, { recursive: true, force: true }); owned.delete(handle); return {};
  };
  return p;
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
async function openBaseSource({ cwd, baseBranch }, p, owned) {
  const listing = await command(p, cwd, 'git', ['worktree', 'list', '--porcelain', '-z']);
  for (const record of listing.split('\0\0')) {
    const fields = record.split('\0'), branch = fields.find(field => field.startsWith('branch '));
    const path = fields.find(field => field.startsWith('worktree '))?.slice(9);
    if (branch === `branch refs/heads/${baseBranch}` && path && existsSync(path)) return { root: realpathSync(path), handle: null };
  }
  let sha = null;
  for (const ref of [`refs/heads/${baseBranch}`, `refs/remotes/origin/${baseBranch}`]) {
    const found = await command(p, cwd, 'git', ['rev-parse', '--verify', '--quiet', '--end-of-options', `${ref}^{commit}`], true);
    if (found !== null) { sha = found.trim(); break; }
  }
  if (sha === null) return { root: null, handle: null };
  if (!/^[0-9a-f]{40}$/.test(sha)) throw Error('The base commit could not be identified.');
  const directory = await mkdtemp(join(tmpdir(), 'pdd-base-source-'));
  const env = { ...process.env, GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null', GIT_CONFIG_SYSTEM: '/dev/null', GIT_TERMINAL_PROMPT: '0', GIT_ATTR_NOSYSTEM: '1' };
  for (const key of Object.keys(env)) if (/^GIT_(?:CONFIG_(?:COUNT|KEY_\d+|VALUE_\d+|PARAMETERS)|DIR|WORK_TREE|INDEX_FILE|OBJECT_DIRECTORY|ALTERNATE_OBJECT_DIRECTORIES|COMMON_DIR|TEMPLATE_DIR)$/.test(key)) delete env[key];
  const isolated = { execFile: (file, args, options) => p.execFile(file, args, { ...options, env }) };
  try {
    await command(isolated, cwd, 'git', ['-c', 'core.hooksPath=/dev/null', 'clone', '--shared', '--no-checkout', '--template=', '--quiet', '--', realpathSync(cwd), directory]);
    await command(isolated, directory, 'git', ['-c', 'core.hooksPath=/dev/null', 'checkout', '--detach', '--quiet', sha]);
    const handle = randomUUID(); owned.set(handle, directory); return { root: directory, handle };
  } catch (error) { await rm(directory, { recursive: true, force: true }); throw error; }
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
  return parseProductDocuments({ mapText: map, planText: plan });
}
export function parseProductDocuments({ mapText, planText = '' }) {
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
export async function readProduct(input, given = {}) { return (await documents(input, portsFor(given))).product; }
export function parseProductWorldWriters({ worldText }) {
  const writers = rows(String(worldText), null, 'contracts/world.md', ['Key', 'Writer']).map(row => ({ key: row.Key, writer: row.Writer }));
  for (const row of writers) if (!row.key || !row.writer) invalid(`contracts/world.md: declaration has an empty ${row.key ? 'Writer' : 'Key'}.`);
  return writers;
}
const parse = text => { try { return JSON.parse(text); } catch { invalid('GitHub returned unreadable JSON.'); } };
const sameRepo = (a, b) => typeof a === 'string' && typeof b === 'string' && a.toLowerCase() === b.toLowerCase();
const canonicalPr = (url, repository, number) => {
  const found = typeof url === 'string' && /^https:\/\/github\.com\/([^/]+\/[^/]+)\/pull\/([1-9][0-9]*)$/.exec(url);
  return !!found && sameRepo(found[1], repository) && Number(found[2]) === number;
};
const pageSize = 10;
async function issues(p, cwd, repository, run, actor, warning) {
  const found = new Map();
  for (let page = 1; ; page++) {
    const response = await p.issuePage({ cwd, repository, marker: marker(run), page, perPage: pageSize });
    if (!response || !Array.isArray(response.items) || response.items.length > pageSize || !Number.isSafeInteger(response.total_count)
      || response.total_count < 0 || response.total_count > 1000 || response.incomplete_results !== false
      || response.items.length !== Math.min(pageSize, Math.max(0, response.total_count - (page - 1) * pageSize)))
      invalid(`GitHub returned an incomplete issue search for ${run}.`);
    for (const issue of response.items) {
      if (!issue || !Number.isSafeInteger(issue.number) || issue.number < 1) invalid(`GitHub returned an invalid issue for ${run}.`);
      if (typeof issue.body === 'string' && issue.body.includes(marker(run)) && !issue.pull_request) {
        const markers = new Set(issue.body.match(/<!-- pdd-product: run=[^\r\n]+? -->/g) ?? []);
        if (markers.size > 1) warning.push(`Warning: Ignored issue #${issue.number} with ambiguous planned-run markers.`);
        else found.set(issue.number, issue);
      }
    }
    if (page * pageSize >= response.total_count) break;
  }
  const trusted = [];
  for (const issue of found.values()) {
    let accept = ['OWNER', 'MEMBER', 'COLLABORATOR'].includes(issue.author_association);
    if (!accept && typeof issue.user?.login === 'string') accept = sameRepo(issue.user.login, await actor());
    if (accept) trusted.push(issue);
    else warning.push(`Warning: Ignored untrusted issue #${issue.number} for ${run}.`);
  }
  const time = issue => Date.parse(issue.created_at) || 0;
  trusted.sort((a, b) => time(a) - time(b) || a.number - b.number);
  if (trusted.length > 1) warning.push(`Warning: Multiple trusted issues name ${run}; using oldest issue #${trusted[0].number}.`);
  return trusted[0] ?? null;
}
const ownProductMarker = (body, run) => new Set(body.match(/<!-- pdd-product: run=[^\r\n]+? -->/g) ?? []).size === 1
  && body.split(/\r?\n/).some(line => line === marker(run));
function eligiblePr(pr, number, repository, run, local, warning) {
  const reject = () => { warning.push(`Warning: PR #${number} could not be verified as ${run}'s PR.`); return false; };
  if (!pr || pr.number !== number || typeof pr.body !== 'string' || !['OPEN', 'MERGED', 'CLOSED'].includes(pr.state)
    || !canonicalPr(pr.url, repository, number)) return reject();
  const [owner, name] = repository.split('/');
  const headOwner = pr.headRepositoryOwner?.login, headName = pr.headRepository?.name;
  if (pr.isCrossRepository === true || typeof headOwner === 'string' && !sameRepo(headOwner, owner)
    || typeof headName === 'string' && !sameRepo(headName, name)) return reject();
  if (!(pr.isCrossRepository === false || sameRepo(headOwner, owner) && sameRepo(headName, name))) return reject();
  const branches = [local?.branch, ...(local?.pr ?? []).map(saved => saved.branch)].filter(branch => typeof branch === 'string');
  return ownProductMarker(pr.body, run) || branches.includes(pr.headRefName) || reject();
}
async function pullRequests(p, cwd, repository, issue, local, run, warning) {
  const numbers = new Set((local?.pr ?? []).map(pr => pr.number).filter(number => Number.isSafeInteger(number) && number > 0));
  for (let page = 1; ; page++) {
    const events = await p.timelinePage({ cwd, repository, issue: issue.number, page, perPage: pageSize });
    if (!Array.isArray(events) || events.length > pageSize) invalid(`GitHub returned an invalid timeline for issue #${issue.number}.`);
    for (const event of events) {
      if (event?.event !== 'cross-referenced') continue;
      const url = event.source?.issue?.pull_request?.html_url, match = typeof url === 'string' && /\/pull\/([1-9][0-9]*)$/.exec(url);
      const number = match && Number(match[1]);
      if (Number.isSafeInteger(number) && canonicalPr(url, repository, number)) numbers.add(number);
    }
    if (events.length < pageSize) break;
  }
  const prs = [];
  for (const number of numbers) {
    const pr = await p.pullRequest({ cwd, repository, number });
    if (eligiblePr(pr, number, repository, run, local, warning)) prs.push(pr);
  }
  return prs;
}
const codePr = (pr, local) => local?.pr?.some(saved => saved.number === pr.number && saved.stage === 'code'
    && typeof saved.branch === 'string' && saved.branch === pr.headRefName)
  || (pr.body.match(/pdd-workflow:/g) ?? []).length === 1
    && (pr.body.match(/pdd-workflow:[A-Za-z0-9_.-]+:[A-Za-z0-9_.-]+/g) ?? []).length === 1
    && pr.body.split(/\r?\n/).filter(line => /^<!-- pdd-workflow:[A-Za-z0-9_.-]+:code -->$/.test(line)).length === 1;
const storyMatches = (name, id) => { const token = basename(name).replace(/\.md$/, ''); return token === id || token.startsWith(`${id}-`) || token.startsWith(`${id}.`); };
const warnings = product => product.runs.filter(run => run.stories.length > 12).map(run => `Warning: ${run.run} has ${run.stories.length} Stories; aim for about 12 per run.`);
function cycles(product) {
  const finished = new Set(), warnings = [];
  const byName = new Map(product.runs.map(run => [run.run, run]));
  for (const start of product.runs) {
    if (finished.has(start.run)) continue;
    const active = new Map(), path = [], stack = [{ name: start.run, next: 0 }];
    while (stack.length) {
      const frame = stack.at(-1);
      if (!active.has(frame.name)) { active.set(frame.name, path.length); path.push(frame.name); }
      const needs = byName.get(frame.name).needs.filter(need => need !== 'plan PR');
      if (frame.next >= needs.length) { active.delete(frame.name); finished.add(frame.name); path.pop(); stack.pop(); continue; }
      const next = needs[frame.next++];
      if (active.has(next)) warnings.push(`Needs form a cycle: ${[...path.slice(active.get(next)), next].join(' → ')}`);
      else if (!finished.has(next)) stack.push({ name: next, next: 0 });
    }
  }
  return [...new Set(warnings)];
}
async function progress(input, given) {
  const p = portsFor(given), { product } = await documents(input, p), cwd = input.cwd;
  const localRuns = await p.listRuns({ cwd }), repo = await p.resolveRepository({ cwd });
  const parent = localRuns.find(run => run.workflow === 'product'), warning = cycles(product), views = new Map();
  const planReady = product.runs.some(run => run.needs.includes('plan PR')) ? await basePlan(p, { cwd, baseBranch: parent?.baseBranch ?? repo.defaultBranch }) : true;
  let actorPromise;
  const actor = () => actorPromise ??= Promise.resolve(p.currentActor({ cwd })).then(reply => {
    if (typeof reply?.login !== 'string' || !reply.login.trim()) throw Error('GitHub did not identify the authenticated account.');
    return reply.login;
  });
  const details = [];
  try {
    for (const run of product.runs) {
      const issue = await issues(p, cwd, repo.repository, run.run, actor, warning), local = issue && localRuns.find(record => record.number === issue.number);
      const prs = issue ? await pullRequests(p, cwd, repo.repository, issue, local, run.run, warning) : [];
      const done = prs.some(pr => pr.state === 'MERGED' && codePr(pr, local));
      const latest = [...prs].filter(pr => runtimeLines(pr.body).some(row => row.story)).sort((a, b) => String(a.updatedAt ?? '').localeCompare(String(b.updatedAt ?? '')) || a.number - b.number).at(-1);
      let evidence;
      if (local) {
        if (done) {
          const baseBranch = local.baseBranch ?? repo.defaultBranch;
          if (!views.has(baseBranch)) {
            const view = await p.openBaseSource({ cwd, baseBranch });
            if (!view || !(view.root === null || typeof view.root === 'string') || !(view.handle === null || typeof view.handle === 'string')) throw Error('Invalid base-source view.');
            views.set(baseBranch, view);
          }
          const view = views.get(baseBranch);
          if (view.root === null) warning.push(`Warning: ${run.run}'s base source is unavailable; saved results are unverified.`);
          evidence = await p.storyEvidence(local, { comparisonRoot: view.root });
        } else evidence = await p.storyEvidence(local);
      } else evidence = latest ? runtimeLines(latest.body).filter(row => row.story).map(row => ({ ...row, current: false, remote: true, at: Date.parse(latest.updatedAt) || 0 })) : [];
      details.push({ run, issue, local, prs, evidence, fromPr: !local && latest ? latest.number : null, done });
    }
  } finally {
    const errors = [];
    for (const view of views.values()) if (view.handle !== null) {
      try { await p.closeBaseSource({ handle: view.handle }); } catch (error) { errors.push(causeText(error.message)); }
    }
    if (errors.length) throw Error(`Could not release the base-source view: ${errors.join('; ')}`);
  }
  const needsFor = run => run.needs.filter(need => need === 'plan PR' ? !planReady : !details.find(detail => detail.run.run === need)?.done);
  const ready = details.filter(detail => !detail.issue && !needsFor(detail.run).length).map(detail => detail.run.run);
  return { p, product, details, ready, needsFor, localRuns, repo, warning: [...new Set(warning)] };
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
  const { product, details, ready, warning } = await progress(input, given);
  const core = product.stories.filter(story => story.tag === 'CORE' && product.runs.some(run => run.stories.includes(story.id)));
  const parts = product.parts.map(part => ({ part: part.part, ...counts(core.filter(story => story.part === part.part).map(story => story.id), details) }));
  const journeyIds = product.runs.filter(run => run.part === 'all').flatMap(run => run.stories);
  if (journeyIds.length) parts.push({ part: 'journeys', ...counts(journeyIds, details) });
  return { name: product.name, size: product.size, parts,
    slices: [...new Set(product.runs.map(run => run.slice))].map(slice => ({ slice, ...counts(product.runs.filter(run => run.slice === slice).flatMap(run => run.stories).filter(id => journeyIds.includes(id) || core.some(story => story.id === id)), details) })),
    runs: details.map(detail => ({ run: detail.run.run, issue: detail.issue?.number ?? null,
      state: detail.done ? 'merged' : detail.local ? `${detail.local.state}${detail.local.stage?.id ? ` (step: ${detail.local.stage.id})` : ''}` : detail.prs.length ? detail.prs.map(pr => `PR #${pr.number} (${pr.isDraft ? 'draft' : pr.state.toLowerCase()})`).join(', ') : detail.issue ? 'issue ready' : 'planned',
      prs: detail.prs.map(pr => pr.number), fromPr: detail.fromPr })), ready, questions: product.questions, ...(warning.length ? { warnings: warning } : {}) };
}
export async function productNext(input, given = {}) {
  const { product, details, ready, needsFor, warning } = await progress(input, given);
  return { ready, waiting: details.filter(detail => !detail.issue && needsFor(detail.run).length).map(detail => ({ run: detail.run.run, needs: needsFor(detail.run) })),
    guidance: product.size === 'small' ? 'run one feature run' : ready.length >= 2 ? 'These can run in parallel, or one person can start them in order.' : '', ...(warning.length ? { warnings: warning } : {}) };
}
function issueTitle(product, run, warning) {
  const full = `${product.name}: ${run.run} (${run.stories.join(', ')})`;
  if ([...full].length <= 256) return full;
  warning.push(`Warning: ${run.run}'s issue title was shortened; all ${run.stories.length} Stories remain in its body.`);
  const suffix = ` (${run.stories.length} Stories)`;
  const label = [...`${product.name}: ${run.run}`];
  const room = 256 - [...suffix].length;
  return `${label.length > room ? label.slice(0, room - 1).join('') + '…' : label.join('')}${suffix}`;
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
        `Stories: ${planned.stories.join(', ')}.`, `Name each Story file with its map id first${planned.stories[0] ? `, for example ${planned.stories[0]}-story.md` : ''}.`, ...planned.stories.map(id => `${id}: ${(product.stories.find(story => story.id === id)?.story ?? product.journeys.find(story => story.id === id)?.journey)}`),
        `Folder: ${product.parts.find(part => part.part === planned.part)?.folder ?? 'user_stories/journeys'}.${contractFiles.length ? ` Contracts: ${contractFiles.join(', ')}.` : ''}`,
        contractFiles.length ? 'Other parts are fakes from their contracts. Do not change contracts/ in this run.' : '', marker(run)].filter(Boolean).join('\n');
      const payload = { repository: repo.repository, title: issueTitle(product, planned, state.warning), body };
      const response = p.createIssue ? await p.createIssue(payload) : { url: await command(p, cwd, 'gh',
        ['issue', 'create', '--repo', payload.repository, '--title', payload.title, '--body', payload.body]) };
      const url = typeof response?.url === 'string' ? response.url.trim() : '';
      const match = /^https:\/\/github\.com\/([^/]+\/[^/]+)\/issues\/([1-9][0-9]*)$/.exec(url);
      if (!match || match[1].toLowerCase() !== repo.repository.toLowerCase()) invalid('Issue creation was not confirmed. Inspect GitHub before trying again.');
      issue = { number: Number(match[2]) }; created = true;
    }
    const warning = [...state.warning, ...warnings(product).filter(text => text.startsWith(`Warning: ${run} `)), ...(state.needsFor(planned).length ? [`Advice: ${run} still needs ${state.needsFor(planned).join(', ')}.`] : [])].join('\n');
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
      return { exitCode: 0, message: [...warning, ...(next.warnings ?? []), next.guidance,
        next.ready.length ? `Can start now: ${next.ready.join(', ')}.` : 'Can start now: none.',
        ...next.ready.map(run => `pdd product start ${run}`), ...next.waiting.map(row => `${row.run}: waits for ${row.needs.join(', ')}.`)].filter(Boolean).join('\n') };
    }
    if (input.command !== 'status') invalid('Unknown product command.');
    const status = await productStatus(input, given);
    return { exitCode: 0, message: input.json ? JSON.stringify(status) : [
      `${status.name} (${status.size}, ${product.parts.length} parts). Plan: product/${product.size === 'small' ? 'map' : 'plan'}.md`, ...warning, ...(status.warnings ?? []),
      'Part  Stories pass  Stale  Not run', ...status.parts.map(part => `${part.part}  ${part.pass} of ${part.total}  ${part.stale}  ${part.notRun}`),
      ...status.runs.map(run => `${run.run}: ${run.state}${run.issue ? ` · issue #${run.issue}` : ''}${run.fromPr ? ` · from PR #${run.fromPr}` : ''}`),
      ...status.slices.map(slice => `Slice ${slice.slice}: ${slice.pass} of ${slice.total} pass.`),
      `Can start now: ${status.ready.join(', ') || 'none'}. Questions open: ${status.questions.join(', ') || 'none'}.`,
      'Stale = passed on older files; a contract or prompt changed since.' ].join('\n') };
  } catch (error) { return { exitCode: 1, message: causeText(error.message) || 'The product could not be read.' }; }
}
