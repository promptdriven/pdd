// Generated from prompts/cli/workflow-results.prompt.md (sha256: 175e0969d09702e17ce36a942bd3121b5dc0121edf820e90e9347e602b1d7981).
import { execFileSync } from 'node:child_process';
import { lstatSync, readdirSync, readFileSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { join, resolve } from 'node:path';
import { captureSource } from './runtime-preflight.mjs';
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
export const usableResult = result => result.kind !== 'pdd workflow prove' || result.state === 'current';

// pdd's own saved results for one run: the newest `pdd test` check batch, the newest `pdd lint` batch (both from the
// runtime state folder, for this worktree, made at or after the run started) and the run's `pdd workflow prove` record.
// It reads files only. It never runs a test, calls the interpreter or changes a file.
export function readRunResults({ root, runDir = null, runId = null, since = 0, baseBranch = null }, { env = process.env, capture = captureSource, git = gitLine } = {}) {
  const results = [], wanted = real(root);
  const directory = join(resolve(env.PDD_STATE_DIR || join(env.HOME || homedir(), '.pdd', 'runtime')), 'batches');
  let names = [];
  try { names = readdirSync(directory).filter(name => BATCH.test(name)).sort(); } catch { names = []; }
  let check = null, lint = null;
  for (const name of names) {
    const batch = readJson(join(directory, name, 'batch.json'));
    if (!batch || batch.batch !== name || typeof batch.root !== 'string' || real(batch.root) !== wanted || !Array.isArray(batch.rows)) continue;
    const at = Date.parse(batch.created_at);
    if (!Number.isFinite(at) || at < since) continue;
    if (batch.intent === 'lint-only') { if (!lint || at >= lint.at) lint = { name, at, batch }; }
    else if (batch.intent === 'check' && (!check || at >= check.at)) check = { name, at, batch };
  }
  if (check) {
    const { batch } = check, summary = readJson(join(directory, check.name, 'summary.json'));
    let source = 'unknown';
    const tests = [...new Set(batch.rows.map(row => row?.test).filter(test => typeof test === 'string'))].sort();
    const sha256 = /^[a-f0-9]{64}$/.test(batch.source_sha256 ?? '') ? batch.source_sha256 : null;
    try { if (sha256 && tests.length) source = capture(root, { tests, appMap: null }).sha256 === sha256 ? 'current' : 'changed'; }
    catch { source = 'unknown'; }
    const stories = Array.isArray(summary?.rows) ? [...new Set(summary.rows.map(row => text(row?.summary_line)).filter(Boolean))] : [];
    results.push({ kind: 'pdd test', batch: check.name, at: check.at, source, sourceSha256: sha256, tests, requests: requestsOf(batch.rows), reports: reportsOf(batch.rows),
      summary: text(summary?.summary_line) || 'result not saved (the check did not finish)', stories,
      ...identity(batch.rows) });
  }
  if (lint) {
    const rows = lint.batch.rows.filter(row => row && typeof row === 'object');
    const passing = rows.filter(row => row.state === 'passed').length, ended = ['passed', 'failed', 'refused'].includes(lint.batch.lint?.state) || rows.every(row => ['passed', 'failed', 'refused'].includes(row.state));
    results.push({ kind: 'pdd lint', batch: lint.name, at: lint.at, requests: requestsOf([lint.batch.lint]), summary: ended ? `Lint: ${passing} of ${rows.length} tests pass. 0 AI calls.` : 'Lint: result unknown (the lint did not finish).' });
  }
  if (runDir) {
    const proof = proveResult(join(runDir, 'old-code-proof.json'), { runId, since, root, baseBranch }, git);
    if (proof) results.push(proof);
  }
  return results;
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
    const facts = [result.batch && `batch ${result.batch}`, iso(result.at), result.source && `source ${result.source}`,
      result.engine && `engine ${result.engine}${result.engineCached ? ' (cached)' : ''}`, result.model && `model ${result.model}${result.modelCached ? ' (cached)' : ''}`,
      result.requests?.length && `request${result.requests.length > 1 ? 's' : ''} ${result.requests.slice(0, SHOWN).join(' ')}`,
      result.headSha && `head ${result.headSha.slice(0, 7)}`].filter(Boolean).join(', ');
    return `${PDD_RESULT}: ${result.kind} (${facts}): ${[result.summary, ...(result.stories ?? []).filter(line => line !== result.summary),
      ...(result.reports ?? []).slice(0, SHOWN).map(url => `Report: ${url} (report links expire after 7 days)`), ...more(result)].join('; ')}`;
  });
}
