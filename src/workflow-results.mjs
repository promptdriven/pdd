// Generated from prompts/cli/workflow-results.prompt.md (sha256: e1ca1609d3282ef92693286ea80c74f3317855dc6046f9612a4860052b1bfe6d).
import {checkPlanResults,checkPlanResultLines} from './runtime-check-plan.mjs';
import { outcomeText, resultOutcome } from './runtime-outcome.mjs';
import { PROMPT_TESTS_WORDS } from './runtime-output.mjs';
import { execFileSync } from 'node:child_process';
import { lstatSync, readdirSync, readFileSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { createHash } from 'node:crypto';
import { readPromptApprovals } from './approval-policy.mjs';
import { readRun } from './workflow-runs.mjs';
import { captureSource, gitFiles, proseSha256, sourceFilePort } from './runtime-preflight.mjs';
import { judgeOldCodeProof } from './workflow-pr-evidence.mjs';

const BATCH = /^\d{8}-\d{6}-[a-z0-9]{4}$/;
export const PDD_RESULT = 'pdd result';
export const NO_VERDICT = 'pdd:no-verdict';
const KINDS = ['pdd test', 'pdd lint', 'pdd workflow prove'];
const listed = items => items.length < 3 ? items.join(' or ') : `${items.slice(0, -1).join(', ')} or ${items.at(-1)}`;
export const noResultLine = (kinds = KINDS) => `${PDD_RESULT}: none. pdd has no ${listed(kinds)} result of its own for this run (${NO_VERDICT}).`;

// One clean line; a workflow ownership marker inside saved text stays text.
const text = (value, max = 300) => String(value ?? '').replace(/[\u0000-\u001f\u007f-\u009f]+/g, ' ').replace(/\s+/g, ' ').trim().slice(0, max).replaceAll('pdd-workflow:', 'pdd-workflow\\u003a');
const real = path => { try { return realpathSync(path); } catch { return resolve(path); } };
function readJson(path) {
  try {
    const stat = lstatSync(path);
    if (!stat.isFile() || stat.size > 4 * 1024 * 1024) return null;
    return JSON.parse(readFileSync(path, 'utf8'));
  } catch { return null; }
}
const iso = ms => Number.isFinite(ms) ? new Date(ms).toISOString().replace(/\.\d{3}Z$/, 'Z') : 'time unknown';
const first = values => values.find(value => typeof value === 'string' && value.trim() && value.trim().toLowerCase() !== 'unknown');
const unique = values => [...new Set(values.filter(value => typeof value === 'string' && value.trim()).map(value => text(value, 200)))];
// The request ids and report links that pdd saved for a batch's rows.
const requestsOf = rows => unique(rows.flatMap(row => Array.isArray(row?.request_ids) ? row.request_ids : []));
const reportsOf = rows => unique(rows.map(row => row?.report_url)).filter(url => /^https?:\/\/\S+$/.test(url));
// A pdd result line shows this many requests and reports; it names how many more the run record keeps.
const SHOWN = 10;
function gitLine(root, args) {
  try { return String(execFileSync('git', ['-C', root, ...args], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] })).trim(); } catch { return ''; }
}
// The prove record, judged by the PR renderer's own freshness rule, so a step record and a PR top always agree.
function proveResult(path, { runId, since, root, baseBranch }, git) {
  let stat;
  try { stat = lstatSync(path); } catch { return null; }
  let saved;
  try { saved = stat.isFile() ? { content: readFileSync(path, 'utf8'), error: '', savedAt: stat.mtimeMs } : { content: '', error: 'Proof is not a regular file.' }; }
  catch { saved = { content: '', error: 'Proof could not be read.' }; }
  const head = git(root, ['rev-parse', '--verify', 'HEAD^{commit}']), base = baseBranch ? git(root, ['merge-base', 'HEAD', `refs/remotes/origin/${baseBranch}`]) : '';
  const judged = judgeOldCodeProof(saved, { runId, startedAt: since, headSha: head, baseSha: base });
  const state = ['stale', 'unavailable', 'not-run'].includes(judged.status) ? judged.status : 'current';
  return { kind: 'pdd workflow prove', at: Math.round(stat.mtimeMs), state, summary: text(judged.line, 600),
    ...(state === 'current' ? { outcome: judged.status } : {}), ...(judged.record ? { headSha: judged.record.headSha } : {}) };
}
// The interpreter build and model of a check: a row's direct fields, else the validated cache_identity of a reused (cached) pass.
function identity(rows) {
  const cached = rows.map(row => row?.cache_identity).filter(value => value && typeof value === 'object' && !Array.isArray(value));
  const pick = (direct, fromCache, max) => {
    const own = first(direct);
    if (own) return [text(own, max), false];
    const reused = first(fromCache);
    return reused ? [text(reused, max), true] : [null, false];
  };
  const [engine, engineCached] = pick(rows.map(row => row?.engine_sha), cached.map(value => value.engine_sha), 12);
  const [model, modelCached] = pick(rows.map(row => row?.requested_model), cached.map(value => value.requested_model), 80);
  return { engine, model, ...(engineCached ? { engineCached } : {}), ...(modelCached ? { modelCached } : {}) };
}
// A prove result that is not current is shown, but it is never pdd's proof.
const STAGE_LABEL = {pr1:'PR 1 (historical)',before:'before the fix (historical)'};
export const usableResult = result => result.states?.some(row => row.state === 'partial') ? false : result.kind === 'native evidence' ? result.assessment?.identity?.stage !== 'pr1' && result.assessment?.storyNativeProof !== 'none' && ['pdd-observed','qualified-external'].includes(result.assessment?.storyNativeProof) : result.kind !== 'pdd workflow prove' || result.state === 'current';

function runtimeEvidence(batch, summary) {
  const coverage = batch.coverage ?? summary?.coverage;
  const nativeOnly = batch.rows.filter(row => Array.isArray(row?.native_only) && row.native_only.length).map(row => ({test:row.test,state:row.state,prompts:row.native_only.filter(item => item && typeof item.path === 'string' && typeof item.reason === 'string').map(item => ({path:item.path,reason:item.reason}))}));
  return {...(batch.check_plan ? {checkPlan:batch.check_plan,checkScope:checkPlanResults(batch.check_plan,batch.rows)} : {}), ...(coverage ? {coverage} : {}), ...(nativeOnly.length ? {nativeOnly} : {})};
}

// pdd's own saved results for one run: the newest `pdd test` check batch, the newest `pdd lint` batch (both from the
// runtime state folder, for this worktree, made at or after the run started) and the run's `pdd workflow prove` record.
// It reads files only. It never runs a test, calls the interpreter or changes a file.
export function readRunResults({ root, runDir = null, runId = null, since = 0, baseBranch = null }, { env = process.env, capture = captureSource, git = gitLine, workspace, ...nativePorts } = {}) {
  const results = [], wanted = real(root);
  const directory = join(resolve(env.PDD_STATE_DIR || join(env.HOME || homedir(), '.pdd', 'runtime')), 'batches');
  let names = [];
  try { names = readdirSync(directory).filter(name => BATCH.test(name)).sort(); } catch { names = []; }
  let check = null, lint = null;
  for (const name of names) {
    const batch = readJson(join(directory, name, 'batch.json'));
    if (!batch || batch.batch !== name || typeof batch.root !== 'string' || !Array.isArray(batch.rows) || batch.rows.some(row=>!row || typeof row!=='object' || Array.isArray(row))) continue;
    let at;
    try { at = Date.parse(batch.created_at); } catch { continue; }
    if (!Number.isFinite(at) || at < since || (batch.intent !== 'check' && batch.intent !== 'lint-only')) continue;
    let association=null;
    if(workspace) {
      try { association=workspace({root,producerRoot:batch.root,tests:[...new Set(batch.rows.map(row=>row?.test))],source_sha256:batch.source_sha256,runId:batch.association?.runId??null,stage:batch.association?.stage??null}); } catch { continue; }
      if(association?.state!=='eligible') {
        // Ordinary same-worktree history remains readable when its source has
        // drifted or its legacy source identity is unavailable. It retains the
        // existing changed/unknown judgment. Alternate or stage-bound evidence
        // must be admitted by its owner before any repository filtering.
        if(real(batch.root)!==wanted||batch.association)continue;
        association=null;
      }
    } else if(real(batch.root)!==wanted)continue;
    if (batch.intent === 'lint-only') { if (!lint || at >= lint.at) lint = { name, at, batch, association }; }
    else if (batch.intent === 'check' && (!check || at >= check.at)) check = { name, at, batch, association };
  }
  if (check) {
    const { batch } = check, summary = readJson(join(directory, check.name, 'summary.json'));
    let source = 'unknown';
    const tests = [...new Set(batch.rows.map(row => row?.test).filter(test => typeof test === 'string'))].sort();
    const sha256 = /^[a-f0-9]{64}$/.test(batch.source_sha256 ?? '') ? batch.source_sha256 : null;
    const sourceTests = batch.source_selection?.tests ?? tests;
    const selection = {tests:sourceTests,appMap:null,...(batch.source_selection ? {excludeFixtureProjects:batch.source_selection.exclude_fixture_projects === true} : {})};
    const sourceRoot = check.association?.sourceAnchor?.root ?? root;
    const freshness = [];
    try { freshness.push(sha256 && (sourceTests.length || batch.source_selection) ? capture(sourceRoot, selection).sha256 === sha256 ? 'current' : 'changed' : 'unknown'); }
    catch { freshness.push('unknown'); }
    if (batch.native_source) {
      try { freshness.push(batch.native_source.sha256 ? capture(sourceRoot,{...selection,tests:batch.native_source.tests}).sha256 === batch.native_source.sha256 ? 'current' : 'changed' : 'unknown'); }
      catch { freshness.push('unknown'); }
    }
    source = freshness.includes('changed') ? 'changed' : freshness.includes('unknown') ? 'unknown' : 'current';
    const states = batch.rows.map(row => ({ test: row.test, ...resultOutcome(row) }));
    const stateEvidence = batch.rows.map(row => text(`${row.test}: ${outcomeText(row)}`)).join('; ');
    const incomplete = states.some(row => row.state !== 'passed');
    const recorded = text(summary?.summary_line);
    const safeSummary = incomplete && /✓/.test(recorded) ? 'Prompt tests: no full pass' : recorded;
    const storyName=value=>typeof value==='string'?value.split('/').at(-1).replace(/\.md$/,''):null;
    const storyLabel=new RegExp(`^${PROMPT_TESTS_WORDS}\\s*\\(([^)]+)\\)`);
    const summaryRows=Array.isArray(summary?.rows)?summary.rows:[];
    const stories=[...new Set(summaryRows.filter(row=>{
      const line=text(row?.summary_line);
      if(!line || !incomplete || !line.includes('✓'))return !!line;
      const story=storyName(row?.story??storyLabel.exec(line)?.[1]);
      const owners=batch.rows.filter(saved=>story && storyName(saved.story)===story && (!row?.test || saved.test===row.test));
      return owners.length>0 && owners.every(saved=>resultOutcome(saved).state==='passed'&&!saved.not_checked?.length);
    }).map(row=>text(row.summary_line)))];
    results.push({ kind: 'pdd test', batch: check.name, at: check.at, source, sourceSha256: sha256, tests, ...(batch.source_selection ? {sourceTests,excludeFixtureProjects:selection.excludeFixtureProjects} : {}), ...(batch.native_source ? {nativeSource:batch.native_source} : {}), ...runtimeEvidence(batch,summary), requests: requestsOf(batch.rows), reports: reportsOf(batch.rows),
      ...(check.association?.runId?{producerRoot:batch.root,association:{runId:check.association.runId,repo:check.association.repo,
        workspaceRoot:check.association.producerRoot,tests:check.association.tests,source_sha256:check.association.source_sha256,
        stage:check.association.stage,sourceAnchor:check.association.sourceAnchor}}:{}),
      ...(check.association?{stage:check.association.stage,sourceAnchor:check.association.sourceAnchor}:{}),states, summary: [safeSummary || 'result not saved (the check did not finish)', stateEvidence, ...checkPlanResultLines(checkPlanResults(batch.check_plan,batch.rows))].filter(Boolean).join('; '), stories,
      ...identity(batch.rows) });
  }
  if (lint) {
    const rows = lint.batch.rows.filter(row => row && typeof row === 'object');
    const passing = rows.filter(row => row.state === 'passed').length;
    results.push({ kind: 'pdd lint', batch: lint.name, at: lint.at, ...runtimeEvidence(lint.batch,readJson(join(directory,lint.name,'summary.json'))), ...(lint.association?{stage:lint.association.stage,sourceAnchor:lint.association.sourceAnchor}:{}),requests: requestsOf([lint.batch.lint]), states: rows.map(row => ({ test: row.test, ...resultOutcome(row) })), summary: [`Lint: ${passing} of ${rows.length} tests pass. 0 AI calls.`, ...rows.map(row => text(`${row.test}: ${outcomeText(row)}`))].join(' ') });
  }
  if (runDir) {
    const proof = proveResult(join(runDir, 'old-code-proof.json'), { runId, since, root, baseBranch }, git);
    if (proof) results.push(proof);
  }
  if (runDir) {
    const run = readRun(runDir);
    const selections = new Map();
    for (const entry of array(run?.evidence)) if (entry.native?.schema === 'pdd.native-evidence-record.v1') selections.set(`${entry.native.profileId}\0${entry.native.storyPath}`, entry);
    for (const entry of selections.values()) {
      const selectors = {root,runDir,runId,profileId:entry.native.profileId,storyPath:entry.native.storyPath};
      let assessment;
      try { assessment = judgeNativeContext(selectors, JSON.parse(readNativeContext(selectors, {workspace,capture,...nativePorts}).content)); } catch { assessment = emptyNative(selectors.profileId); }
      results.push({kind:'native evidence',at:entry.at,source:assessment.sourceState,stage:assessment.identity.stage,assessment,summary:nativeResultSummary(assessment)});
    }
  }
  return results;
}

// Why pdd's own saved check has no verdict, from its saved rows (summary.json, else batch.json). It reads files only.
// issue: a failed expectation, a file-rule refusal or a step time limit (fix this issue's files); access: sign-in,
// access or an interpreter address problem; service: not run, busy, or an AI-service refusal (the interpreter); unknown: an
// outcome that is not known yet.
const SERVICE_REFUSALS = new Set(['graph-provider-failure', 'graph-uncertain-child-dispatch']);
const ACCESS_NOTES = new Set(['blocked', 'auth-required']);
// pdd's own words for a server step deadline and for a login that the interpreter did not accept (any error code).
const TIME_LIMIT_WORDS = /\btook more than [\d.]+ minutes and was stopped\b|\b(?:timeout|timed[ -]out|time[ -]limit|deadline[ -]exceeded)\b/i;
const SIGN_IN_WORDS = /\(HTTP 40[13]\)|\bgh auth login\b/;
const words = item => item && typeof item === 'object' ? [item.message, item.engine_message, item.cause].filter(value => typeof value === 'string').join(' ') : '';
const timeLimited = row => Boolean(row.time_limit) || [row.reason, row.note, ...(Array.isArray(row.refusals) ? row.refusals : [])]
  .some(item => item?.code === 'step_timeout' || SERVICE_REFUSALS.has(item?.code) && TIME_LIMIT_WORDS.test(words(item)));
// pdd's own words for a temporary PDD Cloud answer (503 cloud-unavailable): a service state, not a sign-in problem.
const TEMPORARY_WORDS = /\bTry again in a minute\b/;
const signIn = row => ![row.note, row.reason].some(item => TEMPORARY_WORDS.test(words(item)))
  && (ACCESS_NOTES.has(row.note?.code ?? row.reason?.code) || [row.note, row.reason].some(item => SIGN_IN_WORDS.test(words(item))) || SIGN_IN_WORDS.test(String(row.why ?? '')));
export function checkCause(rows) {
  const open = (Array.isArray(rows) ? rows : []).filter(row => row && typeof row === 'object').map(row => ({ ...row, ...resultOutcome(row) })).filter(row => row.state !== 'passed');
  if (!Array.isArray(rows) || !rows.length) return 'none';
  if (!open.length) return 'passed';
  const codes = row => (Array.isArray(row.refusals) ? row.refusals : []).map(item => item?.code);
  if (open.some(row => row.state === 'failed' || ['broken-test','check-plan-prerequisite'].includes(row.reason?.code) || timeLimited(row) || row.state === 'refused' && (!codes(row).length || codes(row).some(code => !SERVICE_REFUSALS.has(code))))) return 'issue';
  if (open.some(row => ['not run', 'partial'].includes(row.state) && signIn(row))) return 'access';
  // An unknown answer that names the AI provider failure is a known end with no verdict.
  const provider = row => row.state === 'partial' && (SERVICE_REFUSALS.has(row.reason?.code) || SERVICE_REFUSALS.has(row.provider?.code) || codes(row).length > 0 && codes(row).every(code => SERVICE_REFUSALS.has(code)));
  return open.every(row => ['refused', 'not run'].includes(row.state) || provider(row)) ? 'service' : 'unknown';
}
const OPEN_ROWS = new Set(['ready', 'waiting', 'sending', 'queued', 'running']);
const stateFolder = env => resolve(env.PDD_STATE_DIR || join(env.HOME || homedir(), '.pdd', 'runtime'));
export function savedCheckCause(batch, { env = process.env } = {}) {
  if (!BATCH.test(String(batch ?? ''))) return 'none';
  const folder = join(stateFolder(env), 'batches', batch);
  const summary = readJson(join(folder, 'summary.json')), saved = readJson(join(folder, 'batch.json'));
  const summaryRows = Array.isArray(summary?.rows) ? summary.rows : null, savedRows = Array.isArray(saved?.rows) ? saved.rows : null;
  // A named check whose rows cannot be read has an outcome that is not known.
  if (!summaryRows && !savedRows) return 'unknown';
  // A check still open, or a summary that an interrupted --retry left behind (its saved rows moved on), is not known yet.
  const states = rows => rows.reduce((map, row) => map.set(`${row?.test}\0${row?.story}`, [...(map.get(`${row?.test}\0${row?.story}`) ?? []), resultOutcome(row ?? {}).state]), new Map());
  if (savedRows?.some(row => OPEN_ROWS.has(row?.state))) return 'unknown';
  const shown = summaryRows && states(summaryRows);
  if (shown && savedRows && [...states(savedRows)].some(([key, list]) => shown.has(key) && shown.get(key).join() !== list.join())) return 'unknown';
  return checkCause(summaryRows ?? savedRows);
}
// A person may buy one replacement for a stopped check, while all original receipts stay intact.
export function savedLostCheck(batch, { env = process.env, root } = {}) {
  if (!BATCH.test(String(batch ?? '')) || typeof root !== 'string') return null;
  const folder = join(stateFolder(env), 'batches', batch);
  const saved = readJson(join(folder, 'batch.json')), summary = readJson(join(folder, 'summary.json'));
  if (saved?.batch !== batch || saved.intent !== 'check' || typeof saved.root !== 'string' || real(saved.root) !== real(root)
    || !Array.isArray(saved.rows) || !saved.rows.length || !/^[a-f0-9]{64}$/.test(saved.source_sha256 ?? '')) return null;
  if (saved.rows.some(row => !row || (OPEN_ROWS.has(row.recovery_state ?? row.state) || row.state === 'sent'))) return null;
  const lost = saved.rows.filter(row => ['partial', 'unknown'].includes(resultOutcome(row).state));
  const safePath = path => typeof path === 'string' && path.length && !isAbsolute(path) && !path.startsWith('-')
    && !path.split(/[\\/]/).includes('..');
  if (!lost.length || !lost.every(row => safePath(row.test) && Number.isInteger(row.max_calls) && row.max_calls >= 1 && row.max_calls <= 1000)) return null;
  const usage = saved.rows.map(row => summary?.rows?.find(item => item.test === row.test) ?? row);
  const numeric = value => typeof value === 'number' && Number.isFinite(value) && value >= 0;
  const knownCalls = usage.reduce((sum, row) => sum + (numeric(row.calls) ? row.calls : numeric(row.known_calls) ? row.known_calls : 0), 0);
  return { batch, sourceSha256: saved.source_sha256, tests: [...new Set(lost.map(row => row.test))],
    maxCalls: Math.min(...lost.map(row => row.max_calls)), cost: { calls: usage.every(row => numeric(row.calls)) ? knownCalls : null, knownCalls } };
}

// Proof that the interpreter gave a verdict after a time: a passed or failed row of this worktree's pdd test that ended at or
// after `since` (a sent check, not a cached pass or a read of an older answer). It reads files only.
export function latestCheckVerdict({ root, since }, { env = process.env } = {}) {
  const directory = join(stateFolder(env), 'batches'), wanted = real(root);
  let names;
  try { names = readdirSync(directory).filter(name => BATCH.test(name)); } catch { return null; }
  let latest = null;
  for (const name of names) {
    const batch = readJson(join(directory, name, 'batch.json'));
    if (batch?.batch !== name || batch.intent !== 'check' || typeof batch.root !== 'string'
      || !Array.isArray(batch.rows) || real(batch.root) !== wanted) continue;
    for (const row of batch.rows) if (['passed', 'failed'].includes(row?.state) && Number.isFinite(row.ended_at) && row.ended_at >= since)
      latest = latest === null ? row.ended_at : Math.max(latest, row.ended_at);
  }
  return latest;
}
export function checkVerdictSince({root, since}, {env = process.env} = {}) {
  return latestCheckVerdict({root, since}, {env}) !== null;
}

function more({ requests = [], reports = [] }) {
  const left = [[requests.length - SHOWN, 'request'], [reports.length - SHOWN, 'report']].filter(([count]) => count > 0).map(([count, word]) => `${count} more ${word}${count === 1 ? '' : 's'}`);
  return left.length ? [`${left.join(' and ')} not shown (all in the run record)`] : [];
}
// One line per result, each starting with "pdd result:", so a reader can tell pdd's own results from agent notes.
export function resultLines(results, { kinds = null } = {}) {
  const shown = (results ?? []).filter(result => !kinds || kinds.includes(result.kind));
  if (!shown.length) return [noResultLine(kinds ?? KINDS)];
  return shown.map(result => {
    if (result.kind === 'native evidence') return `${PDD_RESULT}: native evidence (${iso(result.at)}, source ${result.source}, ${STAGE_LABEL[result.stage] ?? (result.stage || 'unknown stage')}): ${nativeResultSummary(result.assessment)}`;
    const facts = [result.batch && `batch ${result.batch}`, iso(result.at), result.source && `source ${result.source}`, result.stage && (STAGE_LABEL[result.stage] ?? result.stage),
      result.engine && `engine ${result.engine}${result.engineCached ? ' (cached)' : ''}`, result.model && `model ${result.model}${result.modelCached ? ' (cached)' : ''}`,
      result.requests?.length && `request${result.requests.length > 1 ? 's' : ''} ${result.requests.slice(0, SHOWN).join(' ')}`,
      result.headSha && `head ${result.headSha.slice(0, 7)}`].filter(Boolean).join(', ');
    return `${PDD_RESULT}: ${result.kind} (${facts}): ${[result.summary, ...(result.stories ?? []).filter(line => line !== result.summary),
      ...(result.coverage?.runtime ? [`Runtime coverage: ${result.coverage.runtime.checkable} of ${result.coverage.runtime.total} prompts checkable, ${result.coverage.runtime.native_only} native-only`] : []),
      ...(result.nativeOnly ?? []).flatMap(row => row.prompts.map(prompt => text(`${row.test} ${row.state}: ${prompt.path}: ${prompt.reason}`,2000))),
      ...(result.reports ?? []).slice(0, SHOWN).map(url => `Report: ${url} (report links expire after 7 days)`), ...more(result)].join('; ')}`;
  });
}

// Native judgments are derived from the read-only owner context, never saved verdict flags.
const known = value => typeof value === 'string' && value.trim() && value !== 'unknown';
const array = value => Array.isArray(value) ? value : [];
const distinct = values => [...new Set(values)];
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const admitted = intake => intake?.admission === 'verified' && ['external-machine','pdd-observed'].includes(intake.origin) && known(intake.originalRef) && known(intake.verificationRef);
const nativeFormats = ['junit-xml','tap13','json','pdd.native-node-report.v1'];
function nativeReceipt(report) {
  if (report === null) return 'missing';
  if (!object(report)) return 'unknown';
  if (!nativeFormats.includes(report.format) || report.format === 'pdd.native-node-report.v1' && (report.producer !== 'pdd-node-test-events' || !/^1\./.test(report.producerVersion))) return 'incompatible';
  if (!['producer','producerVersion','runner','runnerVersion','runtimeVersion','profileId','requirementsId'].every(key => known(report[key])) || !Array.isArray(report.observations) || report.observations.some(row=>!object(row)||!known(row.occurrenceId)||!known(row.testId)||!['passed','failed','skipped','todo','not-completed','unknown'].includes(row.outcome)||![true,false,null].includes(row.selected)||![true,false,null].includes(row.started)) || !object(report.capture)) return 'unknown';
  if (report.complete !== true || !['selectionComplete','terminalSeen','processEnded'].every(key => report.capture[key] === true) || !known(report.capture.eventRef)) return 'partial';
  return 'accepted';
}
const executedPass = row => row.outcome === 'passed' && row.started === true && row.selected === true;
function nativeComparison(current, baseline, intake) {
  const answer = {state:'absent',reason:'none',lostIds:[],changes:[]};
  if (!baseline) return answer;
  answer.state = 'incomparable';
  const prior = baseline.report;
  if (!admitted(intake) || !admitted(baseline.intake)) answer.reason = 'unverified';
  else if (nativeReceipt(current) === 'unknown' || nativeReceipt(prior) === 'unknown' || !current || !prior) answer.reason = 'unknown';
  else if (nativeReceipt(current) === 'partial' || nativeReceipt(prior) === 'partial') answer.reason = 'partial';
  else if (nativeReceipt(current) !== 'accepted' || nativeReceipt(prior) !== 'accepted' || ['format','producer','producerVersion','runner','runnerVersion','runtimeVersion','profileId','requirementsId'].some(key => current[key] !== prior[key])) answer.reason = 'scope-or-version';
  else {
    answer.state = 'comparable';
    for (const id of distinct(prior.observations.map(row=>row.testId))) {
      const before = prior.observations.filter(row=>row.testId===id), after = current.observations.filter(row=>row.testId===id);
      if (!before.every(executedPass) || after.length && after.every(executedPass)) continue;
      answer.lostIds.push(id);
      answer.changes.push({id,before:'passed',after:after.length ? distinct(after.map(row=>row.outcome==='passed' && !executedPass(row) ? 'unknown' : row.outcome)).join(',') : 'missing'});
    }
  }
  return answer;
}
function emptyNative(profileId) {
  return {profileId,profileState:'unverified',sourceState:'unknown',receiptState:'unknown',origin:'unknown',requiresReview:true,
    requiredIds:[],missingIds:[],failedIds:[],skippedIds:[],unknownIds:[],unexecutedGates:[],prerequisiteProblems:[],optionalSkippedIds:[],duplicateIds:[],
    occurrenceCount:null,uniqueIdCount:null,observations:[],identity:Object.fromEntries(['sourceId','implementationId','testsId','requirementsId','profilePrompt','profileApproval','originalRef','verificationRef','producer','producerVersion','reportFormat','runnerVersion','runtimeVersion','stage','sourceRef'].map(key=>[key,'unknown'])),
    criteria:[],comparison:{state:'incomparable',reason:'unknown',lostIds:[],changes:[]},limits:[],profileNativeProof:'none',storyNativeProof:'none',gates:[],prerequisites:[]};
}
export async function assessNativeEvidence(selectors, ports = {}) {
  const result = emptyNative(selectors.profileId);
  let context;
  try { const reply = await (ports.readNativeContext ?? (input=>readNativeContext(input,ports)))(selectors); context = JSON.parse(reply.content); } catch { return result; }
  try { return judgeNativeContext(selectors, context); } catch { return result; }
}
function judgeNativeContext(selectors, context) {
  const result = emptyNative(selectors.profileId);
  if(context?.schema==='pdd.native-context-unavailable.v1'&&known(context.reason))result.limits=[context.reason];
  const p = context?.protected, candidate = context?.candidate, intake = context?.intake, report = context?.report;
  if (context?.schema !== 'pdd.native-assessment-context.v1' || context.runId !== selectors.runId || !object(p) || p.profileId !== selectors.profileId || !object(candidate) || !object(intake) || !Array.isArray(p.requiredIds) || !Array.isArray(p.requiredGates) || !Array.isArray(p.fixtures) || !Array.isArray(p.mappings) || p.requiredIds.some(id=>!known(id)) || p.requiredGates.some(id=>!known(id)) || !p.requiredIds.length && !p.requiredGates.length || p.fixtures.some(row=>!object(row)||!known(row.id)||!known(row.artifactId))) return result;
  result.origin = intake.origin ?? 'unknown'; result.limits = array(intake.limits);
  result.requiresReview = p.review !== 'approved' || !known(p.approvalRef) || candidate.requirementsId !== p.requirementsId;
  result.requiredIds = distinct(p.requiredIds);
  result.receiptState = nativeReceipt(report);
  const sourceFields=['sourceId','implementationId','testsId','requirementsId'];
  if (report && object(report.source)) {
    const valuesKnown=sourceFields.every(key=>known(candidate[key]) && known(report.source[key])) && known(p.requirementsId);
    result.sourceState = valuesKnown ? sourceFields.every(key=>candidate[key]===report.source[key]) && report.profileId===p.profileId && report.requirementsId===p.requirementsId && candidate.requirementsId===p.requirementsId ? 'current' : 'stale' : 'unknown';
  }
  const verified=admitted(intake);
  for (const key of sourceFields) result.identity[key]=known(candidate[key]) ? candidate[key] : 'unknown';
  Object.assign(result.identity,{profilePrompt:p.promptPath||'unknown',profileApproval:p.approvalRef||'unknown',originalRef:intake.originalRef||'unknown',verificationRef:intake.verificationRef||'unknown',producer:report?.producer||'unknown',producerVersion:report?.producerVersion||'unknown',reportFormat:report?.format||'unknown',runnerVersion:report?.runnerVersion||'unknown',runtimeVersion:report?.runtimeVersion||'unknown',stage:intake.stage||'unknown',sourceRef:intake.sourceRef||'unknown'});
  if (Array.isArray(report?.observations)) {
    result.observations=report.observations.map(row=>({occurrenceId:row.occurrenceId,testId:row.testId,selected:typeof row.selected==='boolean'?row.selected:null,started:typeof row.started==='boolean'?row.started:null,outcome:row.outcome,skipReason:row.skipReason??null}));
    result.occurrenceCount=result.observations.length;result.uniqueIdCount=new Set(result.observations.map(row=>row.testId)).size;
    result.duplicateIds=distinct(result.observations.map(row=>row.testId)).filter(id=>result.observations.filter(row=>row.testId===id).length>1);
    result.optionalSkippedIds=distinct(result.observations.filter(row=>!p.requiredIds.includes(row.testId)&&row.outcome==='skipped').map(row=>row.testId));
  }
  for (const id of result.requiredIds) {
    const rows=result.observations.filter(row=>row.testId===id);
    if(!rows.length)result.missingIds.push(id);
    if(rows.some(row=>row.outcome==='failed'))result.failedIds.push(id);
    if(rows.some(row=>row.outcome==='skipped'))result.skippedIds.push(id);
    if(rows.some(row=>!['passed','failed','skipped'].includes(row.outcome)||row.outcome==='passed'&&!executedPass(row)||row.selected===false&&row.started===true))result.unknownIds.push(id);
  }
  result.gates=p.requiredGates.map(id=>{const rows=array(report?.gates).filter(row=>row.id===id);return {id,outcome:verified&&rows.length===1&&['passed','failed','skipped'].includes(rows[0].outcome)?rows[0].outcome:'unknown'};});
  result.unexecutedGates=result.gates.filter(row=>row.outcome!=='passed').map(row=>row.id);
  result.prerequisites=p.fixtures.map(expected=>{
    const rows=array(report?.prerequisites).filter(row=>row.id===expected.id), observed=rows.length===1?rows[0]:{};
    let state=['missing','incompatible'].includes(observed.state)?observed.state:'unknown';
    if(verified&&observed.state==='verified'&&known(observed.verificationRef))state=observed.artifactId===expected.artifactId?'verified':'incompatible';
    return {id:expected.id,expectedArtifactId:expected.artifactId,artifactId:observed.artifactId||'unknown',state,verificationRef:observed.verificationRef||'unknown'};
  });
  result.prerequisiteProblems=result.prerequisites.filter(row=>row.state!=='verified').map(row=>row.id);
  if(!result.requiresReview&&verified&&result.sourceState==='current'&&result.receiptState==='accepted')result.profileState=[result.missingIds,result.failedIds,result.skippedIds,result.unknownIds,result.unexecutedGates,result.prerequisiteProblems].some(rows=>rows.length)||report.exitCode!==0?'incomplete':'complete';
  if(result.profileState==='complete')result.profileNativeProof=result.origin==='pdd-observed'?'pdd-observed':'qualified-external';
  const story=context.story;
  if(story?.path===selectors.storyPath&&Array.isArray(story.criteria))result.criteria=story.criteria.map(criterion=>{
    const mappings=p.mappings.filter(row=>row.storyPath===story.path&&row.criterionId===criterion.id), exact=mappings.filter(row=>row.criterionText===criterion.text);
    const ids=distinct(mappings.flatMap(row=>array(row.nativeIds)));
    const reason=!mappings.length?'unmapped':!exact.length?'criterion-changed':mappings.length!==1||exact.length!==1||!known(criterion.id)||!known(criterion.text)||!Array.isArray(exact[0].nativeIds)||!exact[0].nativeIds.length||exact[0].nativeIds.some(id=>!p.requiredIds.includes(id))?'invalid-mapping':result.profileState==='unverified'?'profile-unverified':result.profileState==='incomplete'?'profile-incomplete':'supported';
    return {id:criterion.id,text:criterion.text,state:reason==='supported'?'supported':'unproved',nativeIds:ids,reason};
  });
  if(result.criteria.length&&result.criteria.every(row=>known(row.id)&&known(row.text)&&row.state==='supported')&&new Set(result.criteria.map(row=>row.id)).size===result.criteria.length)result.storyNativeProof=result.profileNativeProof;
  result.comparison=nativeComparison(report,context.baseline,intake);
  return result;
}

const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const nativeError = message => Object.assign(Error(message),{code:'native-evidence-invalid'});
function nativeBytes(path, files = {}) {
  const fs = files;
  const full = resolve(path), parts = full.split(sep);
  for(let index=2;index<=parts.length;index++) {
    const stat=(fs.lstatSync ?? lstatSync)(parts.slice(0,index).join(sep));
    if(stat.isSymbolicLink() || index===parts.length&&(!stat.isFile() || stat.size>10*1024*1024))throw nativeError('Original evidence must be a regular local file of at most 10 MiB, without symlinks.');
  }
  return Buffer.from((fs.readFileSync ?? readFileSync)(full));
}
function nativePath(path) {
  if(typeof path!=='string'||!path||isAbsolute(path)||path.includes('\\')||path.split('/').some(part=>!part||part==='.'||part==='..')||/[\0-\x1f]/.test(path))throw nativeError('Unsafe native source path.');
  return path;
}
function pointerValue(value,path) {
  if(typeof path!=='string'||!path.startsWith('/')||/~(?![01])/u.test(path))return undefined;
  for(const key of path.slice(1).split('/').map(key=>key.replaceAll('~1','/').replaceAll('~0','~'))) {
    if(!object(value)&&!Array.isArray(value)||!Object.hasOwn(value,key))return undefined;
    value=value[key];
  }
  return value;
}
function profileIn(content, profileId) {
  const found=[];
  for(const match of content.matchAll(/<details\b[^>]*>\s*<summary>\s*Native validation profile:\s*([^<]+)<\/summary>([\s\S]*?)<\/details>/g)) {
    if(match[1].trim()!==profileId)continue;
    for(const json of match[2].matchAll(/```json\s*\n([\s\S]*?)\n```/g)) {
      try { const row=JSON.parse(json[1]); if(row.schema==='pdd.native-profile.v1'&&row.profileId===profileId)found.push(row); } catch {}
    }
  }
  if(found.length!==1)throw nativeError('Native profile declaration is missing or ambiguous.');
  const p=found[0];
  if(!['requiredIds','requiredGates','fixtures','mappings','sourcePaths','testPaths'].every(key=>Array.isArray(p[key]))||!p.requiredIds.length&&!p.requiredGates.length||p.requiredIds.some(id=>!known(id))||new Set(p.requiredIds).size!==p.requiredIds.length||new Set(p.requiredGates).size!==p.requiredGates.length)throw nativeError('Malformed native profile inventory.');
  for(const path of [...p.sourcePaths,...p.testPaths])nativePath(path);
  return p;
}
function nativeSelection(root,storyPath,profileId,ports,retained) {
  const visible=new Set((ports.gitFiles ?? gitFiles)(root));
  const sourceFiles=(ports.sourceFilePort??sourceFilePort)(root,visible);
  const read=path=>{nativePath(path);if(!visible.has(path))throw nativeError('Native source is not Git-visible.');return sourceFiles.read({path}).content;};
  // A saved, reviewed owner can still explain profile completion when the
  // current Story is absent. Recheck its actual prompt bytes and journal below;
  // never reconstruct current criteria or support from the retained mapping.
  if(retained?.path&&(!visible.has(storyPath)||!sourceFiles.stat({path:storyPath}).exists)) {
    const content=read(retained.path),profile=profileIn(content,profileId);
    if(!profile.mappings.some(row=>row.storyPath===storyPath))throw nativeError('Retained native owner does not map the selected Story.');
    return {promptPath:retained.path,content,profile,story:null,read};
  }
  const storyText=read(storyPath), section=/^## Native validation\s*\n([\s\S]*?)(?=^## |$(?![\s\S]))/m.exec(storyText)?.[1]??'';
  const links=[...section.matchAll(/\[[^\]]*\]\(([^)\s]+)#native-validation-profile-([^)\s]+)\)/g)];
  if(links.length!==1||links[0][2]!==profileId)throw nativeError('Native Story owner link is missing or ambiguous.');
  const promptPath=relative(root,resolve(root,dirname(storyPath),links[0][1])).split(sep).join('/');
  const content=read(promptPath), profile=profileIn(content,profileId);
  const criteriaSection=/^## Acceptance(?: criteria)?\s*\n([\s\S]*?)(?=^## |$(?![\s\S]))/m.exec(storyText)?.[1]??'';
  const criteria=[...criteriaSection.matchAll(/^\s*(\d+)\.\s+(.+)$/gm)].map(match=>({id:`AC${match[1]}`,text:match[2].trim()}));
  return {promptPath,content,profile,story:{path:storyPath,criteria},read};
}
function reviewedNative(selectors,selection,retained,ports,snapshotOnly=false) {
  if(ports.approvals)return ports.approvals({...selectors,...selection,retained});
  const commonDir=gitLine(selectors.root,['rev-parse','--path-format=absolute','--git-common-dir']);
  if(!commonDir)throw nativeError('Native approval journal is unavailable.');
  const journal=readPromptApprovals({commonDir}), run=selectors.runDir?readRun(selectors.runDir):null;
  const candidates=[{content:selection.content},...(!snapshotOnly&&retained?.path===selection.promptPath?[retained]:[])];
  // Actual retained Git bytes permit historical requirements lookup; hashes alone never reconstruct prose.
  const commits=snapshotOnly?[]:gitLine(selectors.root,['log','--all','--format=%H','--',selection.promptPath]).split('\n').filter(Boolean);
  for(const sha of commits) {try{const content=execFileSync('git',['-C',selectors.root,'show',`${sha}:${selection.promptPath}`],{encoding:'utf8',stdio:['ignore','pipe','ignore']});candidates.push({content});}catch{}}
  for(const event of [...journal].reverse()) {
    const approved=event.prompts.find(row=>row.path===selection.promptPath);
    if(!approved)continue;
    const decision=array(run?.decisions).find(row=>row.evidence?.id===event.id);
    // A workflow journal event cannot outlive the saved decision that binds
    // it. Without workflow identity, standalone approvals use the journal.
    const workflowApproval=known(run?.workflow)||run?.approvalRecord?.evidence?.id===event.id||Boolean(decision);
    if(workflowApproval&&(!decision||decision.decision!=='approve'||!known(decision.gateId)||
      run?.approvalRecord?.evidence?.id===event.id&&decision.gateId!==run.approvalRecord.gateId||
      array(decision.evidence?.prompts).length!==event.prompts.length||!event.prompts.every(prompt=>array(decision.evidence?.prompts).some(row=>row.path===prompt.path&&row.proseSha256===prompt.proseSha256))))continue;
    const bytes=candidates.find(row=>proseSha256(row.content)===approved.proseSha256);
    if(!bytes)continue;
    let profile;try{profile=profileIn(bytes.content,selectors.profileId);}catch{continue;}
    return {profile,content:bytes.content,promptPath:selection.promptPath,approvalRef:event.id||`approval-at-${event.at}`,review:'approved',sourceRoot:run?.sourceRoot||selectors.root,requirementsId:digest(`${selection.promptPath}\0${selectors.profileId}\0${approved.proseSha256}`)};
  }
  return {profile:selection.profile,content:selection.content,promptPath:selection.promptPath,approvalRef:'',review:'missing',sourceRoot:run?.sourceRoot||selectors.root,requirementsId:digest(`${selection.promptPath}\0${selectors.profileId}\0${proseSha256(selection.content)}`)};
}
function nativeSource(selectors,selection,reviewed,ports) {
  if(ports.source)return ports.source({...selectors,selection,reviewed});
  const profile=selection.profile, paths=distinct([...profile.sourcePaths,...profile.testPaths,selection.promptPath]);
  const capture=(ports.capture ?? captureSource)(selectors.root,{tests:paths,appMap:null});
  const hashPaths=paths=>digest(Buffer.concat(paths.map(path=>Buffer.concat([Buffer.from(`${path}\0`),Buffer.from(selection.read(path)),Buffer.from('\0')]))));
  return {sourceId:capture.sha256,implementationId:hashPaths(profile.sourcePaths),testsId:hashPaths(profile.testPaths),requirementsId:digest(`${selection.promptPath}\0${selectors.profileId}\0${proseSha256(selection.content)}`),paths,tests:profile.testPaths,source_sha256:capture.sha256};
}
function xmlNative(source) {
  const stack=[],roots=[],tokens=source.match(/<!--[\s\S]*?-->|<\?xml\s[\s\S]*?\?>|<!\[CDATA\[[\s\S]*?\]\]>|<[^>]*>|[^<]+|</g)||[];
  const decode=value=>value.replace(/&([^;]+);/g,(_,name)=>{const names={amp:'&',lt:'<',gt:'>',quot:'"',apos:"'"};if(Object.hasOwn(names,name))return names[name];if(/^#(?:x[\da-f]+|\d+)$/i.test(name)){const n=name[1]==='x'?parseInt(name.slice(2),16):Number(name.slice(1));if(n>0&&n<=0x10ffff&&!(n>=0xd800&&n<=0xdfff))return String.fromCodePoint(n);}throw nativeError('Unsupported XML entity.');});
  for(const token of tokens) {
    if(token.startsWith('<!--')||token.startsWith('<?xml'))continue;
    if(token.startsWith('<![CDATA[')){if(!stack.length)throw nativeError('Malformed XML.');stack.at(-1).text+=token.slice(9,-3);continue;}
    if(token.startsWith('</')){const close=/^<\/([\w:.-]+)\s*>$/.exec(token);if(!close||stack.pop()?.tag!==close[1])throw nativeError('Malformed XML.');continue;}
    if(token.startsWith('<')) {
      const match=/^<([\w:.-]+)([\s\S]*?)\s*(\/?)>$/.exec(token);if(!match)throw nativeError('Unsafe or malformed XML.');
      const node={tag:match[1],attrs:{},children:[],text:''};let raw=match[2].trim();
      while(raw){const a=/^([\w:.-]+)\s*=\s*("[^"]*"|'[^']*')\s*/.exec(raw);if(!a||Object.hasOwn(node.attrs,a[1]))throw nativeError('Malformed XML attribute.');node.attrs[a[1]]=decode(a[2].slice(1,-1));raw=raw.slice(a[0].length);}
      if(stack.length)stack.at(-1).children.push(node);else roots.push(node);
      if(!match[3])stack.push(node);
    } else if(stack.length)stack.at(-1).text+=decode(token);else if(token.trim())throw nativeError('Malformed XML.');
  }
  if(stack.length||roots.length!==1||!['testsuite','testsuites'].includes(roots[0].tag))throw nativeError('Incomplete JUnit XML.');
  return roots[0];
}
function nativeReport(bytes,profile,reference) {
  const base={format:profile.reportFormat,producer:'unknown',producerVersion:'unknown',runner:'unknown',runnerVersion:'unknown',runtimeVersion:'unknown',profileId:profile.profileId,requirementsId:'unknown',source:{},capture:{selectionComplete:null,terminalSeen:null,processEnded:null,eventRef:reference},complete:null,exitCode:null,gates:[],prerequisites:[],observations:[],rowReferences:[]};
  const outcomeNames=['passed','failed','skipped','todo','not-completed','unknown'];
  if(profile.reportFormat==='json') {
    const doc=JSON.parse(bytes.toString('utf8')),reader=profile.reader;
    if(!object(reader)||!object(reader.fields)||!object(reader.outcomes))throw nativeError('Structured report requires the reviewed pointer reader.');
    const rows=pointerValue(doc,reader.rows);if(!Array.isArray(rows))throw nativeError('Structured report occurrence array is unavailable.');
    const observationFields=['occurrenceId','testId','selected','started','outcome','skipReason'];
    for(const [name,path]of Object.entries(reader.fields))if(!observationFields.includes(name)&&Object.hasOwn(base,name))base[name]=pointerValue(doc,path)??base[name];
    base.observations=rows.map((row,index)=>{const observation={occurrenceId:`${reference}${reader.rows}/${index}`,testId:'unknown',selected:null,started:null,outcome:'unknown',skipReason:null};for(const field of observationFields){const value=pointerValue(row,reader.fields[field]);if(value!==undefined)observation[field]=field==='outcome'?(reader.outcomes[value]??'unknown'):value;}base.rowReferences.push(`${reader.rows}/${index}`);return observation;});
    if(base.observations.some(row=>!outcomeNames.includes(row.outcome)))throw nativeError('Unknown structured outcome interpretation.');
    return base;
  }
  if(profile.reportFormat==='pdd.native-node-report.v1') {
    const doc=JSON.parse(bytes.toString('utf8'));
    // An imported normalized assertion is not an observed Node event capture.
    if(doc.schema!=='pdd.native-node-report.v1'||!Array.isArray(doc.events))throw nativeError('Original Node events and selection/process envelope are required.');
    Object.assign(base,{producer:'pdd-node-test-events',producerVersion:doc.producerVersion,runner:'node:test',runnerVersion:doc.runnerVersion,runtimeVersion:doc.runtimeVersion,source:doc.source??{},capture:{selectionComplete:null,terminalSeen:doc.events.some(event=>event.type==='test:plan'&&event.data?.nesting===0),processEnded:null,eventRef:`${reference}/events`},complete:null,exitCode:null});
    const enqueued=[],dequeued=[];
    for(const [index,event]of doc.events.entries()) {
      if(event.type==='test:enqueue')enqueued.push(event.data);
      if(event.type==='test:dequeue')dequeued.push(event.data);
      if(!['test:pass','test:fail'].includes(event.type))continue;
      const row=event.data??{},same=other=>['file','line','column','name','nesting'].every(key=>other?.[key]===row[key]);
      base.observations.push({occurrenceId:`${reference}/events/${index}`,testId:`${row.file}::${row.name}@${row.line}:${row.column}`,selected:enqueued.some(same)?true:null,started:row.skip||row.todo?false:dequeued.some(same)?true:null,outcome:row.skip?'skipped':row.todo?'todo':event.type==='test:pass'?'passed':'failed',skipReason:row.skip||row.todo||null});
    }
    base.capture.selectionComplete=enqueued.length>0;
    base.complete=base.capture.terminalSeen&&enqueued.length===base.observations.length;
    return base;
  }
  if(profile.reportFormat==='junit-xml') {
    const root=xmlNative(bytes.toString('utf8')),properties={};let count=0;
    const visit=(node,parents=[])=>{
      if(node.tag==='property'&&known(node.attrs.name))properties[node.attrs.name]=node.attrs.value??node.text;
      if(node.tag==='testcase') {
        const a=node.attrs,skip=node.children.find(row=>row.tag==='skipped'),failed=node.children.some(row=>['failure','error'].includes(row.tag));
        const fullName=[a.classname,a.name].filter(Boolean).join('::');
        base.observations.push({occurrenceId:`${reference}/testcase/${count++}`,testId:known(a.file)&&known(a.line)&&known(a.column)?`${a.file}::${fullName}@${a.line}:${a.column}`:fullName||'unknown',selected:null,started:skip?false:true,outcome:skip?'skipped':failed?'failed':'passed',skipReason:skip?.attrs.message||skip?.text||null,reportedIdentity:{...a,fullName,suite:parents}});
      }
      for(const child of node.children)visit(child,node.tag==='testsuite'?[...parents,node.attrs.name].filter(Boolean):parents);
    };visit(root);
    Object.assign(base,Object.fromEntries(['producer','producerVersion','runner','runnerVersion','runtimeVersion'].filter(key=>known(properties[key])).map(key=>[key,properties[key]])));
    const testcases=node=>node.tag==='testcase'?[node]:node.children.flatMap(testcases);
    const suites=node=>['testsuite','testsuites'].includes(node.tag)?[node,...node.children.flatMap(suites)]:[];
    const countsMatch=suites(root).every(suite=>{const rows=testcases(suite),counts={tests:rows.length,failures:rows.filter(row=>row.children.some(child=>child.tag==='failure')).length,errors:rows.filter(row=>row.children.some(child=>child.tag==='error')).length,skipped:rows.filter(row=>row.children.some(child=>child.tag==='skipped')).length};return Object.entries(counts).every(([key,count])=>!Object.hasOwn(suite.attrs,key)||/^\d+$/.test(suite.attrs[key])&&Number(suite.attrs[key])===count);});
    base.capture.terminalSeen=countsMatch; base.complete=countsMatch; base.aggregate={unit:'testcases',reported:root.attrs.tests??null};
    return base;
  }
  if(profile.reportFormat==='tap13') {
    const lines=bytes.toString('utf8').split(/\r?\n/),scopes=[{indent:-1,name:''}],seenPlans=[],resultCounts=new Map();let terminal=false,bail=false,malformed=false;
    for(let index=0;index<lines.length;index++) {
      const line=lines[index],indent=/^ */.exec(line)[0].length;
      if(/^\s*Bail out!/i.test(line))bail=true;
      const subtest=/^( *)# Subtest:\s*(.*)$/.exec(line);
      if(subtest){while(scopes.length>1&&scopes.at(-1).indent>=indent)scopes.pop();scopes.push({indent,name:subtest[2],line:index});continue;}
      const scopeKey=level=>`${level}:${scopes.filter(row=>row.indent>=0&&row.indent<level).map(row=>row.line).join('/')}`;
      const plan=/^\s*(\d+)\.\.(\d+)(?:\s+#.*)?$/.exec(line);
      if(plan){if(plan[1]!=='1'||seenPlans.some(row=>row.key===scopeKey(indent)))malformed=true;seenPlans.push({indent,key:scopeKey(indent),count:Number(plan[2])-Number(plan[1])+1});if(indent===0)terminal=true;continue;}
      const result=/^( *)(not ok|ok)\s+(\d+)?(?:\s+-)?\s*(.*?)(?:\s+#\s*(SKIP|TODO)\b\s*(.*))?$/i.exec(line);
      if(!result)continue;
      while(scopes.length>1&&scopes.at(-1).indent>=indent)scopes.pop();
      const key=scopeKey(indent);resultCounts.set(key,(resultCounts.get(key)??0)+1);
      if(result[3]&&Number(result[3])!==resultCounts.get(key))malformed=true;
      const name=result[4],directive=result[5]?.toUpperCase(),observed={occurrenceId:`${reference}/line/${index+1}`,testId:[...scopes.map(row=>row.name).filter(Boolean),name].join('::'),selected:null,started:directive?false:true,outcome:directive==='SKIP'?'skipped':directive==='TODO'?'todo':result[2]==='ok'?'passed':'failed',skipReason:directive?result[6]||directive:null,reportedIdentity:{name,fullName:[...scopes.map(row=>row.name).filter(Boolean),name].join('::'),file:null,line:null,column:null}};
      let diagnostic='';
      if(lines[index+1]?.trim()==='---'){let end=index+2;while(end<lines.length&&(!lines[end].trim()||/^ */.exec(lines[end])[0].length>indent)&&lines[end].trim()!=='...')end++;if(lines[end]?.trim()==='...')diagnostic=lines.slice(index+2,end).join('\n');else malformed=true;}
      const location=/\blocation:\s*['"]?(.+?):(\d+):(\d+)['"]?\s*$/m.exec(diagnostic);
      if(location){Object.assign(observed.reportedIdentity,{file:location[1],line:Number(location[2]),column:Number(location[3])});observed.testId=`${location[1]}::${observed.reportedIdentity.fullName}@${location[2]}:${location[3]}`;}
      base.observations.push(observed);
    }
    const plansComplete=seenPlans.every(plan=>(resultCounts.get(plan.key)??0)===plan.count);
    base.capture.terminalSeen=terminal&&!bail&&!malformed&&plansComplete;base.complete=terminal&&!bail&&!malformed&&plansComplete; base.aggregate={unit:'planned-results',plans:seenPlans};
    // A TAP plan asserts totals, never selected scope, starts, runner identity or process exit.
    base.capture.eventRef=reference;
    return base;
  }
  base.interpretation='incompatible';return base;
}

function originalInputs(summaryFile,ports,depth=0) {
  if(depth>1)throw nativeError('Native baselines cannot contain another baseline.');
  const descriptorBytes=nativeBytes(summaryFile,ports.files),descriptor=JSON.parse(descriptorBytes.toString('utf8'));
  if(descriptor.schema!=='pdd.native-evidence-import.v1'||!known(descriptor.profileId)||!known(descriptor.storyPath)||!Array.isArray(descriptor.originals))throw nativeError('Malformed native evidence descriptor.');
  const roles=['report','source','selection','execution','fixture','gate'];
  const originals=descriptor.originals.map((row,index)=>{
    if(!object(row)||!roles.includes(row.role)||!known(row.path))throw nativeError('Malformed native original reference.');
    const path=resolve(dirname(summaryFile),row.path),bytes=nativeBytes(path,ports.files);
    return {index,role:row.role,name:basename(path),path,sha256:digest(bytes),bytes};
  });
  if(originals.filter(row=>row.role==='report').length!==1)throw nativeError('Native evidence requires one unambiguous original report.');
  return {descriptor,descriptorBytes,originals,baseline:descriptor.baseline?originalInputs(resolve(dirname(summaryFile),descriptor.baseline),ports,depth+1):null};
}
function originalJson(originals,role) {
  const rows=originals.filter(row=>row.role===role);if(rows.length!==1)return null;
  try{return {...JSON.parse(rows[0].bytes.toString('utf8')),originalRef:`sha256:${rows[0].sha256}`};}catch{return null;}
}
function bindNativeRows(report,profile,selection,limits) {
  for(const row of array(report.observations)) {
    row.identityBound=false;
    const original=row.testId;
    let candidates=profile.requiredIds.filter(id=>id===original);
    if(!candidates.length&&row.reportedIdentity) {
      const observed=row.reportedIdentity;
      candidates=profile.requiredIds.filter(id=>{
        const match=/^(.*?)::(.*)@(\d+):(\d+)$/.exec(id);if(!match)return false;
        let observedFile=observed.file;
        if(observedFile&&isAbsolute(observedFile))observedFile=relative(selection.root,observedFile).split(sep).join('/');
        return observedFile===match[1]&&[observed.name,observed.fullName].includes(match[2])&&Number(observed.line)===Number(match[3])&&Number(observed.column)===Number(match[4]);
      });
    }
    const id=candidates.length===1?candidates[0]:original,match=/^(.*?)::(.*)@(\d+):(\d+)$/.exec(id??'');
    if(!match||!profile.testPaths.includes(match[1])){row.testId=known(id)?id:'unknown';limits.push(`Unresolved native test identity at ${row.occurrenceId}.`);continue;}
    try {
      const line=selection.read(match[1]).split('\n')[Number(match[3])-1];
      const name=match[2].split('::').at(-1);
      if(!line||!line.includes(name)||!Number.isSafeInteger(Number(match[4]))||Number(match[4])<1)throw nativeError('Native declaration location does not match.');
      row.testId=id;row.identityBound=true;
    }catch{row.testId='unknown';limits.push(`Native source declaration unavailable at ${row.occurrenceId}.`);}
  }
}
function nativeSourceAgreement(report,originals,candidate,association,checks,limits) {
  const expected={...candidate,source_sha256:candidate.source_sha256??candidate.sourceId,stage:association.stage,runId:association.runId,producerRoot:association.producerRoot,repo:association.producerRoot};
  const identities=['sourceId','implementationId','testsId','requirementsId','source_sha256','stage','runId','producerRoot','repo'];
  const records=[{reference:'parsed-report',value:report}];
  for(const original of originals.filter(row=>row.role!=='report')) {
    try{records.push({reference:`sha256:${original.sha256}`,value:JSON.parse(original.bytes.toString('utf8'))});}catch{}
  }
  let agrees=true;
  for(const {reference,value} of records) {
    for(const [location,facts] of [['',value],['source',value?.source],['capture',value?.capture],['capture.source',value?.capture?.source]]) {
      if(!object(facts))continue;
      for(const key of identities) {
        if(!known(facts[key]))continue;
        const observed=known(expected[key]),matches=observed&&facts[key]===expected[key];
        const field=[location,key].filter(Boolean).join('.');
        checks.push({check:'original-source-identity',originalRef:reference,field,asserted:facts[key],observed:expected[key]??null,state:matches?'checked':observed?'mismatch':'unavailable'});
        if(!matches){agrees=false;limits.push(observed?`Original source identity contradicts the selected source at ${reference} ${field}.`:`Original source identity cannot be checked against unavailable selected source at ${reference} ${field}.`);}
      }
    }
  }
  return agrees;
}
function nativeContextFromOriginals(selectors,input,retained,ports,historical=false) {
  if(input.descriptor&&(input.descriptor.profileId!==selectors.profileId||input.descriptor.storyPath!==selectors.storyPath))throw nativeError('Original profile/Story selectors do not match.');
  const limits=['External original; command was not observed by PDD. Parsing does not authenticate the runner or speaker.'],checks=[];
  const source=originalJson(input.originals,'source'),execution=originalJson(input.originals,'execution'),selectionEvidence=originalJson(input.originals,'selection');
  let association={state:'unavailable',reason:'Canonical workspace reader is unavailable.',stage:null};
  const producerRoot=source?.producerRoot??source?.repo;
  const tests=source?.tests;
  if(ports.workspace&&known(producerRoot)&&Array.isArray(tests)&&known(source?.source_sha256)) {
    try{association=ports.workspace({root:selectors.root,producerRoot,tests,source_sha256:source.source_sha256,runId:source.runId??null,stage:source.stage??null});}catch(error){limits.push(`Native association lookup unavailable: ${text(error.message)}.`);}
  }
  const ownedSameRoot=association.runId===null&&source?.runId==null&&association.stage==='current'&&real(association.producerRoot??'')===real(selectors.root);
  const associationValid=association?.state==='eligible'&&(!selectors.runId||association.runId===selectors.runId||ownedSameRoot)&&['current','pr1'].includes(association.stage)&&known(association.producerRoot)&&Array.isArray(association.tests)&&association.tests.length===tests?.length&&association.tests.every(path=>tests.includes(path));
  checks.push({check:'workspace-association',state:associationValid?'checked':'unavailable',reason:association?.reason??'unknown',stage:association?.stage??'unknown'});
  if(!associationValid)limits.push(`Native run/source association is unverified: ${text(association?.reason||'unknown owner or stage')}.`);
  // Only the canonical owner can choose a historical comparator. Current
  // evidence always binds to the current selection, even for a PR 1 original.
  const sourceRoot=historical&&associationValid?association.sourceAnchor?.root:selectors.root;
  if(!known(sourceRoot))throw nativeError('Canonical historical source anchor is unavailable.');
  const selection=nativeSelection(sourceRoot,selectors.storyPath,selectors.profileId,ports,retained);selection.root=sourceRoot;
  const reviewed=reviewedNative(selectors,selection,retained,ports,historical),profile=reviewed.profile;
  const protectedProfile={...profile,requirementsId:reviewed.requirementsId,promptPath:reviewed.promptPath,sourceRoot:reviewed.sourceRoot,approvalRef:reviewed.approvalRef,review:reviewed.review};
  let candidate={sourceId:'unknown',implementationId:'unknown',testsId:'unknown',requirementsId:'unknown'};
  try{candidate=nativeSource({...selectors,root:sourceRoot},selection,reviewed,ports);checks.push({check:'selected-native-source',state:'checked',sourceId:candidate.sourceId,sourceAnchor:historical?association.sourceAnchor:null});}catch(error){limits.push(`Native source capture unavailable: ${text(error.message)}.`);}
  const original=input.originals.find(row=>row.role==='report'),originalRef=`sha256:${original.sha256}`;
  let report,parsed=false;
  try{report=nativeReport(original.bytes,profile,originalRef);parsed=nativeFormats.includes(profile.reportFormat)&&!report.interpretation;checks.push({check:'original-report',state:'read',format:profile.reportFormat,sha256:original.sha256,rowReferences:report.rowReferences});}
  catch(error){limits.push(`Original report interpretation unavailable: ${text(error.message)}.`);report={format:profile.reportFormat,observations:[],interpretation:'unknown'};}
  const assertedSource=Object.fromEntries(['sourceId','implementationId','testsId','requirementsId'].map(key=>[key,known(report.source?.[key])?report.source[key]:source?.source?.[key]]));
  const sourceAgrees=nativeSourceAgreement(report,input.originals,candidate,association,checks,limits);
  const sourceMatches=sourceAgrees&&object(assertedSource)&&['sourceId','implementationId','testsId'].every(key=>known(assertedSource[key])&&assertedSource[key]===candidate[key]);
  const selectedPathsMatch=Array.isArray(tests)&&Array.isArray(candidate.paths)&&tests.length===candidate.paths.length&&tests.every(path=>candidate.paths.includes(path));
  report.source=object(report.source)?{...report.source}:{};
  for(const key of ['sourceId','implementationId','testsId','requirementsId'])if(!known(report.source[key]))report.source[key]=known(assertedSource?.[key])?assertedSource[key]:key==='requirementsId'?reviewed.requirementsId:'unknown';
  const profileMatches=(!known(report.profileId)||report.profileId===selectors.profileId)&&(!known(report.requirementsId)||report.requirementsId===reviewed.requirementsId);
  if(!profileMatches)limits.push('Original source/profile identity contradicts the reviewed requirements.');
  if(!known(report.profileId))report.profileId=selectors.profileId;
  if(!known(report.requirementsId))report.requirementsId=reviewed.requirementsId;
  // These selectors are derived from the matched reviewed bytes, never inserted into the original.
  checks.push({check:'reviewed-profile-binding',state:reviewed.review,approvalRef:reviewed.approvalRef,derivedSelectors:{profileId:selectors.profileId,requirementsId:reviewed.requirementsId}});
  if(!sourceMatches||!selectedPathsMatch)limits.push('Original source/test selection does not establish the current complete native source binding.');
  const sourceRef=source?.originalRef??'unknown';
  const companionMatches=row=>row&&known(row.sourceId)&&row.sourceId===assertedSource?.sourceId&&row.stage===association?.stage;
  const executionIdentity=['producer','producerVersion','runner','runnerVersion','runtimeVersion'];
  const executionValid=companionMatches(execution)&&Number.isInteger(execution.exitCode)&&execution.processEnded===true&&
    (report.capture?.processEnded==null||report.capture.processEnded===true)&&
    executionIdentity.every(key=>!known(report[key])||!known(execution[key])||report[key]===execution[key])&&
    (report.exitCode===null||report.exitCode===undefined||report.exitCode===execution.exitCode);
  checks.push({check:'original-process-completion',state:executionValid?'checked':'unavailable',originalRef:execution?.originalRef??'unknown'});
  if(executionValid) {
    report.exitCode=execution.exitCode;report.capture={...report.capture,processEnded:true};
    for(const key of executionIdentity)if(!known(report[key])&&known(execution[key]))report[key]=execution[key];
  }else limits.push('Original process completion or runner/version identity is unavailable.');
  const reportedGates=array(report.gates),reportedFixtures=array(report.prerequisites);
  report.gates=[];report.prerequisites=[];
  for(const row of input.originals.filter(row=>['gate','fixture'].includes(row.role))) {
    let evidence;try{evidence=JSON.parse(row.bytes.toString('utf8'));}catch{continue;}
    const reference=`sha256:${row.sha256}`;
    if(row.role==='gate') {
      const occurrence=array(report.observations).find(observed=>observed.occurrenceId===evidence.occurrenceRef);
      const observed=reportedGates.find(gate=>gate.id===evidence.id&&gate.occurrenceRef===evidence.occurrenceRef&&gate.outcome===evidence.outcome);
      if(companionMatches(evidence)&&executionValid&&evidence.reportRef===originalRef&&observed&&occurrence&&occurrence.started===true&&occurrence.outcome===evidence.outcome&&['passed','failed','skipped'].includes(evidence.outcome))report.gates.push({id:evidence.id,outcome:evidence.outcome,verificationRef:reference});
    } else {
      let state=['missing','incompatible'].includes(evidence.state)?evidence.state:'unknown';
      const occurrence=array(report.observations).find(observed=>observed.occurrenceId===evidence.occurrenceRef);
      const observed=reportedFixtures.find(fixture=>fixture.id===evidence.id&&fixture.artifactId===evidence.artifactId&&fixture.occurrenceRef===evidence.occurrenceRef);
      if(companionMatches(evidence)&&evidence.reportRef===originalRef&&occurrence&&observed&&known(evidence.path)&&known(evidence.artifactId)) {
        try{const actual=nativeBytes(resolve(dirname(row.originalPath??row.path),evidence.path),ports.files);state=digest(actual)===evidence.artifactId.replace(/^sha256:/,'')?'verified':'incompatible';}catch(error){state=error.code==='ENOENT'?'missing':'unknown';}
      }
      report.prerequisites.push({id:evidence.id,artifactId:evidence.artifactId??'unknown',state,verificationRef:state==='verified'?reference:''});
    }
  }
  bindNativeRows(report,profile,selection,limits);
  const selectedValid=companionMatches(selectionEvidence)&&selectionEvidence.complete===true&&Array.isArray(selectionEvidence.testIds)&&selectionEvidence.testIds.every(id=>known(id))&&
    (report.capture?.selectionComplete==null||report.capture.selectionComplete===true)&&
    array(report.observations).every(row=>row.selected==null||typeof row.selected==='boolean'&&row.selected===selectionEvidence.testIds.includes(row.testId));
  checks.push({check:'original-selection',state:selectedValid?'checked':'unavailable',originalRef:selectionEvidence?.originalRef??'unknown'});
  if(selectedValid) {
    report.capture={...report.capture,selectionComplete:true};
    for(const row of array(report.observations))if(row.selected==null)row.selected=selectionEvidence.testIds.includes(row.testId)?true:null;
  }else limits.push('Original complete selection observation is unavailable or contradicts the report.');
  const identitiesBound=profile.requiredIds.every(id=>array(report.observations).filter(row=>row.testId===id).every(row=>row.identityBound===true));
  if(selectedValid&&selectionEvidence.testIds.some(id=>!report.observations.some(row=>row.testId===id)))report.complete=false;
  const verified=associationValid&&sourceMatches&&profileMatches&&selectedPathsMatch&&identitiesBound&&executionValid&&selectedValid&&reviewed.review==='approved'&&candidate.requirementsId===reviewed.requirementsId;
  const intake={origin:parsed?'external-machine':'unknown',admission:verified?'verified':'unverified',originalRef,verificationRef:verified?`derived:${digest(JSON.stringify(checks))}`:'',limits:distinct(limits),stage:associationValid?association.stage:'unknown',sourceRef};
  const context={schema:'pdd.native-assessment-context.v1',runId:selectors.runId,protected:protectedProfile,candidate,story:selection.story,intake,report,baseline:null};
  if(input.baseline) {
    try {
      const derived=nativeContextFromOriginals(selectors,input.baseline,retained,ports,true),baseline=derived.context;
      context.baseline={intake:baseline.intake,report:baseline.report};
      checks.push({check:'historical-baseline',stage:baseline.intake.stage,checks:derived.checks});
      context.intake.limits=distinct([...context.intake.limits,...baseline.intake.limits.map(limit=>`Historical baseline (${baseline.intake.stage}): ${limit}`)]);
    }catch(error){
      const reason=`Historical source unavailable: ${text(error.message)}.`;
      context.baseline={intake:{admission:'unverified',limits:[reason]},report:null};
      context.intake.limits.push(reason);
    }
  }
  return {context,checks,reviewedPrompt:{path:selection.promptPath,content:reviewed.content}};
}
export function prepareNativeEvidence({root,runDir,runId,summaryFile},ports={}) {
  const input=originalInputs(resolve(summaryFile),ports),selectors={root,runDir,runId,profileId:input.descriptor.profileId,storyPath:input.descriptor.storyPath};
  const prior=array((ports.readRun??readRun)(runDir)?.evidence).filter(row=>row.native?.profileId===selectors.profileId&&row.native?.storyPath===selectors.storyPath).at(-1)?.native?.reviewedPrompt;
  const derived=nativeContextFromOriginals(selectors,input,prior,ports);
  const originals=[{role:'descriptor',name:basename(summaryFile),bytes:input.descriptorBytes,sha256:digest(input.descriptorBytes)},...input.originals];
  if(input.baseline)originals.push({role:'baseline-descriptor',baseline:true,name:'baseline-descriptor.json',bytes:input.baseline.descriptorBytes,sha256:digest(input.baseline.descriptorBytes)},...input.baseline.originals.map(row=>({...row,baseline:true})));
  const record={schema:'pdd.native-evidence-record.v1',runId,profileId:selectors.profileId,storyPath:selectors.storyPath,originals:originals.map(({role,name,path:originalPath,sha256,baseline=false},index)=>({role,name,sha256,index,baseline,...(originalPath?{originalPath}:{})})),reviewedPrompt:derived.reviewedPrompt,checks:derived.checks,intake:derived.context.intake};
  return {originals,record,assessment:judgeNativeContext(selectors,derived.context)};
}
export function readNativeContext(selectors,ports={}) {
  try {
    const run=selectors.runDir?(ports.readRun??readRun)(selectors.runDir):null;
    if((run && (run.runId!==selectors.runId||real(run.root)!==real(selectors.root)))||!run&&selectors.runId)throw nativeError('Native run identity is unavailable.');
    const records=array(run?.evidence).filter(row=>row.native?.schema==='pdd.native-evidence-record.v1'&&row.native.runId===selectors.runId&&row.native.profileId===selectors.profileId&&row.native.storyPath===selectors.storyPath);
    const saved=records.at(-1)?.native;
    if(!saved) {
      const selection=nativeSelection(selectors.root,selectors.storyPath,selectors.profileId,ports),reviewed=reviewedNative(selectors,selection,null,ports);
      let candidate={};try{candidate=nativeSource(selectors,selection,reviewed,ports);}catch{}
      return {content:JSON.stringify({schema:'pdd.native-assessment-context.v1',runId:selectors.runId,protected:{...reviewed.profile,...reviewed},candidate,story:selection.story,intake:{origin:'unknown',admission:'unverified',originalRef:'',verificationRef:'',stage:'unknown',limits:['No saved native original evidence. Original stage is unavailable.']},report:null,baseline:null})};
    }
    const originals=array(saved.originals).map(row=>{
      const path=resolve(selectors.runDir,row.savedPath??'');
      const rel=relative(resolve(selectors.runDir),path);
      if(!rel||rel==='..'||rel.startsWith(`..${sep}`))throw nativeError('Saved original escapes its owned evidence history.');
      const bytes=nativeBytes(path,ports.files);
      if(digest(bytes)!==row.sha256)throw nativeError('Retained original bytes changed.');
      return {...row,path,bytes};
    });
    const input={originals:originals.filter(row=>!row.baseline&&row.role!=='descriptor'),descriptor:JSON.parse(originals.find(row=>row.role==='descriptor').bytes.toString('utf8')),baseline:null};
    if(originals.some(row=>row.baseline))input.baseline={originals:originals.filter(row=>row.baseline&&row.role!=='baseline-descriptor'),descriptor:JSON.parse(originals.find(row=>row.role==='baseline-descriptor').bytes.toString('utf8')),baseline:null};
    if(input.descriptor.profileId!==selectors.profileId||input.descriptor.storyPath!==selectors.storyPath)throw nativeError('Saved native descriptor selectors changed.');
    return {content:JSON.stringify(nativeContextFromOriginals(selectors,input,saved.reviewedPrompt,ports).context)};
  }catch(error){return {content:JSON.stringify({schema:'pdd.native-context-unavailable.v1',reason:text(error.message)})};}
}

function nativeResultSummary(a) {
  const rows = [`profile ${text(a.profileId)}: ${a.profileState}`, `Story native proof: ${a.storyNativeProof}`, `origin ${a.origin}`, `receipt ${a.receiptState}`,
    `occurrences ${a.occurrenceCount ?? 'unknown'}, unique IDs ${a.uniqueIdCount ?? 'unknown'}`];
  for (const name of ['missingIds','failedIds','skippedIds','unknownIds','duplicateIds','optionalSkippedIds','unexecutedGates','prerequisiteProblems']) if (a[name].length) rows.push(`${name}: ${a[name].map(id=>text(id)).join(', ')}`);
  for (const criterion of a.criteria) rows.push(`${text(criterion.id)}: ${criterion.state} (${criterion.reason}); criterion ${text(criterion.text,1000)}; native IDs ${criterion.nativeIds.map(id=>text(id)).join(', ') || 'none'}`);
  for (const row of a.observations) rows.push(`${text(row.occurrenceId)} ${text(row.testId)}: ${text(row.outcome)}; selected ${row.selected ?? 'unknown'}, started ${row.started ?? 'unknown'}${row.skipReason ? `; ${text(row.skipReason)}` : ''}`);
  for (const row of a.gates) rows.push(`gate ${text(row.id)}: ${text(row.outcome)}`);
  for (const row of a.prerequisites) rows.push(`fixture ${text(row.id)}: ${text(row.state)}, artifact ${text(row.artifactId)}, reference ${text(row.verificationRef)}`);
  rows.push(`baseline ${a.comparison.state} (${a.comparison.reason}); lost IDs ${a.comparison.lostIds.map(id=>text(id)).join(', ')||'none'}`);
  rows.push(`source ${text(a.identity.sourceId)}, implementation ${text(a.identity.implementationId)}, tests ${text(a.identity.testsId)}, profile prompt ${text(a.identity.profilePrompt)}, review ${text(a.identity.profileApproval)}`);
  rows.push(`original ${text(a.identity.originalRef)}, source reference ${text(a.identity.sourceRef)}, verification ${text(a.identity.verificationRef)}`);
  rows.push(...a.limits.map(limit=>`Limit: ${text(limit,1000)}`));
  return rows.join('; ');
}
