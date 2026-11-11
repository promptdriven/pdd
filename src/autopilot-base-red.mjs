// Generated from prompts/cli/autopilot-base-red.prompt.md (sha256: f02761211d328ef15544c3dd869db66efa0ee0572d53211ae73b2b26ab31260f).
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { StringDecoder } from 'node:string_decoder';
import { redactSecrets } from './secret-redaction.mjs';

export const MAIN_RED_LABEL = 'pdd:main-red';
export const BASE_RED_MARKER = 'pdd:autopilot-core:base-red';
const MIN = 60 * 1000, DAY = 24 * 60 * MIN, RECENT = 14 * DAY, MAX_NAMES = 50, ISSUE_NAMES = 20, TAIL_LINES = 30, KEEP_RECORDS = 50;
const GOOD = ['success', 'neutral', 'skipped'];
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const short = sha => String(sha ?? '').slice(0, 7);
const oneLine = (value, max = 300) => String(value ?? '').replace(/\s+/g, ' ').trim().slice(0, max);
const readJson = (fs, file) => { try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch { return null; } };
function save(fs, file, value) {
  fs.mkdirSync(join(file, '..'), { recursive: true, mode: 0o700 });
  const temp = `${file}.${process.pid}.tmp`;
  fs.writeFileSync(temp, JSON.stringify(value, null, 2) + '\n', { mode: 0o600 }); fs.renameSync(temp, file);
}

// The open decision of the release lead: the main-red issue goes to the work repository in auto and observe mode (it is
// the repository's own work, not a report to PDD). The other choice is to follow autopilot.report (draft: a local
// file only). Change only this function.
export const mainRedRoute = (settings = {}) => (void settings, 'file');

// ---- Failing test names ---------------------------------------------------------------------------------
// Top-level TAP lines of node:test. An indented line is a subtest (its parent's line names the failure); a TODO or
// SKIP directive is no failure. The checkout root goes, so one test in two checkouts has one name.
const NOT_OK = /^not ok \d+ - (.*)$/;
const DIRECTIVE = /\s#\s*(?:todo|skip)\b/i;
export function failingTestNames(text, { root } = {}) {
  const names = [];
  let more = false;
  for (const raw of String(text ?? '').split('\n')) {
    const m = NOT_OK.exec(raw.replace(/\r$/, ''));
    if (!m || DIRECTIVE.test(m[1])) continue;
    let name = m[1];
    if (typeof root === 'string' && root.length > 1) name = name.split(`file://${root}/`).join('').split(`${root}/`).join('');
    name = name.trim().slice(0, 200);
    if (!name || names.includes(name)) continue;
    if (names.length >= MAX_NAMES) { more = true; continue; }
    names.push(name);
  }
  return { names, more };
}
// A log in 1 MB parts, whole lines only (an over-long line without an end is dropped), so it never sits in memory at once.
function readNames(fs, file, root) {
  if (!file) return null;
  const names = [], decoder = new StringDecoder('utf8');
  let more = false, carry = '', skipping = false, fd;
  const take = text => {
    const found = failingTestNames(text, { root });
    more ||= found.more;
    for (const name of found.names) if (!names.includes(name)) { if (names.length < MAX_NAMES) names.push(name); else more = true; }
  };
  try {
    fd = fs.openSync(file, 'r');
    const buffer = Buffer.alloc(1024 * 1024);
    for (let at = 0, n; (n = fs.readSync(fd, buffer, 0, buffer.length, at)) > 0; at += n) {
      let text = carry + decoder.write(buffer.subarray(0, n));
      if (skipping) { const end = text.indexOf('\n'); if (end < 0) { carry = ''; continue; } text = text.slice(end + 1); skipping = false; }
      const cut = text.lastIndexOf('\n');
      carry = cut < 0 ? text : text.slice(cut + 1);
      if (cut >= 0) take(text.slice(0, cut));
      if (carry.length > 64 * 1024) { carry = ''; skipping = true; }
    }
    if (!skipping) take(carry + decoder.end());
  } catch { return null; } finally { if (fd !== undefined) try { fs.closeSync(fd); } catch { /* Closed. */ } }
  return { names, more };
}
const redactedTail = log => redactSecrets(String(log ?? '')).split('\n').map(line => line.replace(/\s+$/, '')).filter(Boolean).slice(-TAIL_LINES).join('\n');

// ---- Shared words ---------------------------------------------------------------------------------------
export const baseRedFingerprint = (what, names = []) => createHash('sha256').update([String(what), ...[...names].map(String).sort()].join('\n')).digest('hex').slice(0, 16);
const markerOf = fingerprint => `<!-- ${BASE_RED_MARKER}:${fingerprint} -->`;
// A job for a main-red issue never gets base-red: its own red is red.
const mainRedJob = job => String(job?.body ?? '').includes(`<!-- ${BASE_RED_MARKER}:`);
const nameOf = red => {
  const names = Array.isArray(red?.names) ? red.names : [];
  return names.length ? `${oneLine(names[0], 120)}${names.length > 1 ? ` and ${names.length - 1} more` : ''}` : red?.what === 'ci' ? 'a CI check' : 'the full test suite';
};
export const baseRedWaiting = job => job?.phase === 'pr' && object(job.baseRed);
export function baseRedStatus(job) {
  return baseRedWaiting(job) ? `; main is red (${nameOf(job.baseRed)}) since ${new Date(job.baseRed.since).toISOString()}; no slot` : '';
}

// The base tip after one fetch per tick.
function baseTip(ctx) {
  const base = ctx.state.baseBranch;
  return ctx.baseRedTip ??= ctx.git(['fetch', '-q', 'origin', base]).then(() => ctx.git(['rev-parse', `origin/${base}`]));
}

// ---- CI: one rerun, then the base tip -------------------------------------------------------------------
function tipChecks(ctx, tip) {
  ctx.baseRedChecks ??= new Map();
  if (!ctx.baseRedChecks.has(tip)) ctx.baseRedChecks.set(tip, (async () => {
    const runs = await ctx.gh.ok('GET', `repos/${ctx.repo}/commits/${tip}/check-runs?per_page=100`);
    const status = await ctx.gh.ok('GET', `repos/${ctx.repo}/commits/${tip}/status`);
    return [...(runs?.check_runs ?? []).map(r => ({ name: r.name, done: r.status === 'completed', good: GOOD.includes(r.conclusion) })),
      ...(status?.statuses ?? []).map(s => ({ name: s.context, done: s.state !== 'pending', good: s.state === 'success' }))];
  })());
  return ctx.baseRedChecks.get(tip);
}
export async function ciVsBase(ctx, job, ci) {
  const now = ctx.now(), runs = Array.isArray(ci?.failedRuns) ? ci.failedRuns : [];
  const rerun = job.ciRerun?.head === job.head ? { names: [], asked: [], ...job.ciRerun } : { head: job.head, names: [], asked: [] }, asked = [];
  for (const run of runs) {
    if (rerun.names.includes(run.name)) continue;
    rerun.names = [...rerun.names, run.name];
    if (!Number.isSafeInteger(run.id)) continue;
    const endpoint = run.app === 'github-actions' ? `repos/${ctx.repo}/actions/jobs/${run.id}/rerun` : `repos/${ctx.repo}/check-runs/${run.id}/rerequest`;
    const r = await ctx.gh.call('POST', endpoint).catch(() => ({ status: 0 }));
    if (r.status >= 200 && r.status < 300) { rerun.asked = [...rerun.asked, { id: run.id, name: run.name, at: now }].slice(-20); asked.push(run.name); }
  }
  job.ciRerun = rerun; ctx.saveJob(job);
  // GitHub may show the old run for a while after the ask; at most for the quiet period.
  const showing = runs.filter(run => rerun.asked.some(a => a.id === run.id && now - a.at < ctx.quiet)).map(run => run.name);
  const waiting = [...new Set([...asked, ...showing])];
  if (waiting.length) return { ...ci, state: 'pending', pending: waiting, sig: `${ci.sig}|rerun:${waiting.join(',')}` };
  if (mainRedJob(job)) return ci;
  const tip = await baseTip(ctx), checks = await tipChecks(ctx, tip);
  const on = name => { const same = checks.filter(c => c.name === name); return same.some(c => c.done && !c.good) ? 'red' : same.some(c => !c.done) ? 'pending' : 'green'; };
  const states = (ci.failed ?? []).map(name => ({ name, state: on(name) }));
  const pending = states.filter(s => s.state === 'pending').map(s => s.name);
  if (pending.length) return { ...ci, state: 'pending', pending, sig: `${ci.sig}|base:${tip}` };
  const own = states.filter(s => s.state !== 'red').map(s => s.name), red = states.filter(s => s.state === 'red').map(s => s.name);
  if (own.length) return { ...ci, state: 'red', failed: own, ...(red.length ? { onBase: `Also red on the base (${ctx.state.baseBranch} at ${short(tip)}), not from this change: ${red.join(', ')}.` } : {}) };
  return { ...ci, state: 'base-red', baseRed: { what: 'ci', sha: tip, names: red } };
}

// ---- Suite: the same tests at the merge base --------------------------------------------------------------
const recordFile = (ctx, sha) => join(ctx.root, 'base-suite', `${sha}.json`);
const STATES = ['running', 'pass', 'fail', 'broken'];
async function prune(ctx, tools) {
  const dir = join(ctx.root, 'base-suite');
  let names = [];
  try { names = ctx.fs.readdirSync(dir).filter(name => /^[0-9a-f]{7,64}\.json$/.test(name)); } catch { /* None yet. */ }
  const rows = names.map(name => ({ file: join(dir, name), rec: readJson(ctx.fs, join(dir, name)) })).sort((a, b) => (b.rec?.at ?? 0) - (a.rec?.at ?? 0));
  const running = new Set();
  rows.forEach((row, i) => {
    if (row.rec?.state === 'running') { running.add(row.rec.cwd); return; }
    if (i < KEEP_RECORDS && ctx.now() - (row.rec?.at ?? 0) < RECENT) return;
    try {
      ctx.fs.rmSync(row.file, { force: true });
      const id = row.rec?.agent?.id;
      if (id) for (const name of ctx.fs.readdirSync(ctx.dirs.logs).filter(n => n.startsWith(`${id}.`))) ctx.fs.rmSync(join(ctx.dirs.logs, name), { force: true });
    } catch (error) { ctx.warn(`Autopilot core could not prune a base suite record: ${error.message}`); }
  });
  let trees = [];
  try { trees = ctx.fs.readdirSync(ctx.dirs.worktrees).filter(name => name.startsWith('base-suite-')); } catch { /* None. */ }
  for (const name of trees) if (!running.has(join(ctx.dirs.worktrees, name))) await tools.removeTree(ctx, join(ctx.dirs.worktrees, name));
}
async function startBase(ctx, job, sha, tools, { restarts = 0, deaths = 0, quiets = 0, cwd = null } = {}) {
  if (!restarts) await prune(ctx, tools);
  let path = cwd && ctx.fs.existsSync(cwd) ? cwd : null;
  if (!path) {
    path = join(ctx.dirs.worktrees, `base-suite-${sha.slice(0, 12)}`);
    if (!await tools.removeTree(ctx, path)) throw Object.assign(Error(`cannot remove the old checkout ${path}`), { code: 'git' });
    await ctx.git(['worktree', 'add', '-q', '--detach', path, sha]);
  }
  // A job id that starts with base-suite-: no issue's local cleanup removes its files.
  const agent = tools.startJob(ctx, { issue: 'base', branch: ctx.state.baseBranch, head: sha }, 'suite', path, '', tools.queuedCommand(ctx, path, ctx.settings.testCommand), { CI: 'true' });
  const rec = { sha, state: 'running', tests: [], more: false, tail: '', text: '', at: ctx.now(), cwd: path, agent, restarts, deaths, quiets };
  save(ctx.fs, recordFile(ctx, sha), rec);
  (ctx.baseRedWatched ??= new Set()).add(sha);
  return rec;
}
async function finish(ctx, rec, state, tools, extra = {}) {
  Object.assign(rec, { state, at: ctx.now(), ...extra });
  save(ctx.fs, recordFile(ctx, rec.sha), rec);
  if (rec.cwd) await tools.removeTree(ctx, rec.cwd);
  return rec;
}
// A runner failure starts the run again in the same checkout, at most twice; then it is broken.
function again(ctx, job, rec, tools, { deaths = 0, quiets = 0, why }) {
  const restarts = rec.restarts ?? 0, counts = { deaths: (rec.deaths ?? 0) + deaths, quiets: (rec.quiets ?? 0) + quiets };
  if (restarts >= 2) return finish(ctx, rec, 'broken', tools, { ...counts, text: `the base suite runner failed at ${short(rec.sha)} (${why}, 3 tries)` });
  return startBase(ctx, job, rec.sha, tools, { restarts: restarts + 1, ...counts, cwd: rec.cwd });
}
async function baseSuite(ctx, job, sha, tools) {
  const file = recordFile(ctx, sha), rec = readJson(ctx.fs, file);
  if (!object(rec) || !STATES.includes(rec.state) || rec.state === 'running' && !object(rec.agent)) return startBase(ctx, job, sha, tools);
  if (rec.state !== 'running') return rec;
  const seen = ctx.jobs.read(rec.agent);
  if (seen.state === 'running') {
    const watched = ctx.baseRedWatched ??= new Set();
    if (watched.has(sha)) return rec;
    watched.add(sha);
    // The core's process rule, as for the job's own suite; the reading job carries the alert keys.
    const watch = await tools.watchProcess(ctx, job, rec.agent, 'suite');
    save(ctx.fs, file, rec);
    if (watch.state === 'ceiling') return finish(ctx, rec, 'broken', tools, { text: oneLine(watch.cause?.text ?? 'the base suite reached its backstop') });
    if (watch.state !== 'quiet') return rec;
    return again(ctx, job, rec, tools, { quiets: 1, why: 'it made nothing new' });
  }
  if (seen.exit?.code === 0) return finish(ctx, rec, 'pass', tools);
  const log = tools.readTail(ctx.fs, rec.agent.log);
  if (seen.state === 'dead' || seen.exit?.signal || [86, 127].includes(seen.exit?.code) || tools.runnerLine.test(log) || !log.trim())
    return again(ctx, job, rec, tools, { deaths: seen.state === 'dead' ? 1 : 0, why: seen.state === 'dead' ? 'the run died' : seen.exit?.signal ? `killed by ${seen.exit.signal}` : `exit ${seen.exit?.code}` });
  const found = readNames(ctx.fs, rec.agent.log, rec.cwd) ?? { names: [], more: false };
  return finish(ctx, rec, 'fail', tools, { tests: found.names, more: found.more, tail: redactedTail(log) });
}
async function mergeBase(ctx, job) {
  const base = ctx.state.baseBranch;
  await baseTip(ctx);
  return ctx.git(['merge-base', `origin/${base}`, job.head]);
}
export async function suiteVsBase(ctx, job, { ci = null, review = null, suite, vectors = null, reds = [] } = {}, tools) {
  let red = ci?.state === 'base-red' ? ci.baseRed : null;
  if (suite?.state === 'fail' && !mainRedJob(job)) {
    const sha = await mergeBase(ctx, job), base = await baseSuite(ctx, job, sha, tools);
    if (base.state === 'running') {
      // No repair before the compare, also when the review is red. The base suite's own process rule bounds the wait.
      job.baseSuite = sha; job.progress = { ...(job.progress ?? {}), at: ctx.now(), running: true }; ctx.saveJob(job);
      return 'wait';
    }
    if (job.baseSuite) { delete job.baseSuite; ctx.saveJob(job); }
    if (base.state !== 'fail') return suite;
    const head = readNames(ctx.fs, job.suite?.agent?.log, job.suite?.cwd);
    const known = side => Boolean(side?.names?.length) && !side.more;
    const fresh = known(head) && known({ names: base.tests, more: base.more }) ? head.names.filter(name => !base.tests.includes(name)) : [];
    if (fresh.length) {
      const also = head.names.filter(name => base.tests.includes(name)), [first, ...rest] = String(suite.text ?? '').split('\n');
      return { ...suite, text: [first, `Failing tests from this change: ${fresh.join('; ')}.`,
        ...(also.length ? [`Also red on the base (${short(sha)}), not from this change: ${also.join('; ')}.`] : []), ...rest].join('\n') };
    }
    red = { what: 'suite', sha, names: known(head) ? head.names : Array.isArray(base.tests) ? base.tests : [], tail: base.tail ?? '' };
    suite = { state: 'base-red', head: suite.head, text: suite.text };
  }
  // The hold: only when the base-red part is the only red, and nothing else of the job still runs.
  if (!red || reds.length || review?.state !== 'pass' || suite?.state === 'running' || vectors?.state === 'running') return suite;
  await tools.leaveLane(ctx, job);
  const tip = red.what === 'ci' ? red.sha : await baseTip(ctx), names = (red.names ?? []).slice(0, MAX_NAMES);
  job.lane = null;
  job.baseRed = { what: red.what, sha: red.sha, tip, names, tail: red.tail ?? '', fingerprint: baseRedFingerprint(red.what, names), since: ctx.now(), report: null };
  job.progress = { ...(job.progress ?? {}), at: ctx.now(), running: true }; ctx.saveJob(job);
  job.baseRed.report = await fileMainRed(ctx, job, job.baseRed).catch(error => { ctx.warn(`Autopilot core could not file the main-red issue for #${job.issue}: ${error.message}`); return null; });
  ctx.saveJob(job);
  return 'wait';
}

// ---- The base-red wait ----------------------------------------------------------------------------------
export async function baseRedWait(ctx, job, tools) {
  const red = job.baseRed;
  job.progress = { ...(job.progress ?? {}), at: ctx.now(), running: true };
  if (!red.report) red.report = await fileMainRed(ctx, job, red).catch(error => { ctx.warn(`Autopilot core could not file the main-red issue for #${job.issue}: ${error.message}`); return null; });
  ctx.saveJob(job);
  const tip = await baseTip(ctx);
  // A deleted or moved issue (404, 410) counts as closed.
  const read = red.report ? await ctx.gh.call('GET', `repos/${ctx.repo}/issues/${red.report.number}`) : null;
  if (read && read.status !== 200 && ![404, 410].includes(read.status)) throw Object.assign(Error(`GitHub GET issue returned ${read.status || 'no reply'}`), { code: 'github' });
  const open = read?.status === 200 && read.value?.state !== 'closed';
  if (tip !== red.tip && !open) {
    const rerun = job.ciRerun;
    delete job.baseRed; delete job.ciRerun;
    // A refresh that fails keeps the base-red state: the old head's red must not count as the PR's own.
    try { return await tools.refreshBase(ctx, job); } catch (error) { Object.assign(job, { baseRed: red, ...(rerun ? { ciRerun: rerun } : {}) }); ctx.saveJob(job); throw error; }
  }
  if (!red.alerted && ctx.now() - red.since >= ctx.quiet) {
    red.alerted = true; ctx.saveJob(job);
    const ref = red.report ? ` (issue #${red.report.number})` : '';
    try {
      await (ctx.ports.alert ?? (async () => {}))({ issue: job.issue, kind: 'stuck', text: `Autopilot core: PR #${job.pr} has waited ${Math.round((ctx.now() - red.since) / MIN)} minutes because main is red (${nameOf(red)})${ref}.`,
        tried: 'Autopilot did not repair the PR: the same failure is on the base branch. The PR waits and holds no slot.',
        need: `Fix the failing ${red.what === 'ci' ? 'check' : 'test'} on ${ctx.state.baseBranch}${ref}, then close that issue. The PR then updates onto the base and runs its checks again.` });
    } catch (error) { ctx.warn(`Autopilot core alert failed: ${error.message}`); }
  }
}

// ---- The main-red issue ---------------------------------------------------------------------------------
export async function fileMainRed(ctx, job, red) {
  if (mainRedRoute(ctx.settings) !== 'file') return null;
  const names = Array.isArray(red?.names) ? red.names : [], fingerprint = red.fingerprint ?? baseRedFingerprint(red.what, names), marker = markerOf(fingerprint);
  let endpoint = `repos/${ctx.repo}/issues?state=all&labels=${encodeURIComponent(MAIN_RED_LABEL)}&per_page=100`;
  for (let page = 0; endpoint && page < 5; page++) {
    const r = await ctx.gh.call('GET', endpoint);
    if (r.status !== 200 || !Array.isArray(r.value)) throw Error(`GitHub GET issues returned ${r.status || 'no reply'}`);
    const hit = r.value.find(row => !row.pull_request && String(row.body ?? '').includes(marker) && (row.state === 'open' || ctx.now() - Date.parse(row.closed_at) < RECENT));
    if (hit) return { number: hit.number, ref: `${ctx.repo}#${hit.number}`, found: true };
    endpoint = r.next;
  }
  const base = ctx.state.baseBranch, ci = red.what === 'ci';
  const title = oneLine(ctx.publicBody(`Main is red: ${names.length ? `${names[0]}${names.length > 1 ? ` (and ${names.length - 1} more)` : ''}` : ci ? 'a CI check' : 'the full test suite'}`), 200);
  const listed = names.slice(0, ISSUE_NAMES).map(name => `  - ${oneLine(name, 200)}`);
  const body = [`Autopilot found ${ci ? 'a CI check' : 'a full test suite'} failure on the base branch \`${base}\`. PR #${job.pr} (issue #${job.issue}) has the same failure, but it did not cause it.`, '',
    `- Base branch: \`${base}\` at ${red.sha}`,
    ci ? `- Failing check(s): ${names.map(name => oneLine(name, 200)).join(', ') || 'unknown'}` : `- Failing tests: ${names.length ? '' : 'the names could not be read'}`,
    ...(ci ? [] : listed), ...(!ci && names.length > ISSUE_NAMES ? [`  - and ${names.length - ISSUE_NAMES} more`] : []),
    `- Seen on: PR #${job.pr} for issue #${job.issue}`, '',
    'While this is red, Autopilot does not repair PRs for this failure. They stay open and wait with no slot. When this issue is closed and the base moves, they update onto the base and run their checks again.', '',
    'Fix the failing or flaky test on the base branch itself, then close this issue.',
    ...(red.tail ? ['', 'Last lines of the base suite log (redacted):', '', '```', redactSecrets(red.tail).replaceAll('```', "'''"), '```'] : []), '', marker].join('\n');
  const issue = await ctx.gh.ok('POST', `repos/${ctx.repo}/issues`, { title, body: ctx.publicBody(body), labels: [MAIN_RED_LABEL, ...(ctx.settings.label ? [ctx.settings.label] : [])] });
  return { number: issue.number, ref: `${ctx.repo}#${issue.number}`, found: false };
}

// ---- Stop (with the core's stopChecks) ------------------------------------------------------------------
export function stopBaseSuite(ctx, job) {
  const sha = job?.baseSuite;
  if (!sha) return;
  delete job.baseSuite;
  try {
    let names = [];
    try { names = ctx.fs.readdirSync(ctx.dirs.jobs).filter(name => /^\d+\.json$/.test(name)); } catch { /* No jobs. */ }
    if (names.map(name => readJson(ctx.fs, join(ctx.dirs.jobs, name))).some(other => object(other) && other.issue !== job.issue && other.phase === 'pr' && other.baseSuite === sha)) return;
    const file = recordFile(ctx, sha), rec = readJson(ctx.fs, file);
    if (rec?.state !== 'running') return;
    if (object(rec.agent)) ctx.jobs.stop(rec.agent);
    ctx.fs.rmSync(file, { force: true });
  } catch (error) { ctx.warn(`Autopilot core could not stop the base suite of #${job.issue}: ${error.message}`); }
}
