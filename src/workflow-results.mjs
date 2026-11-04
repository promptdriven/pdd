// Generated from prompts/cli/workflow-results.prompt.md (sha256: d567cc802ab5aadd375ed90e0bb4504a713876587427082929c14a31742efc16).
import { lstatSync, readdirSync, readFileSync, realpathSync } from 'node:fs';
import { homedir } from 'node:os';
import { join, resolve } from 'node:path';
import { captureSource } from './runtime-preflight.mjs';

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

// pdd's own saved results for one run: the newest `pdd test` check batch, the newest `pdd lint` batch (both from the
// runtime state folder, for this worktree, made at or after the run started) and the run's `pdd workflow prove` record.
// It reads files only. It never runs a test, calls the interpreter or changes a file.
export function readRunResults({ root, runDir = null, runId = null, since = 0 }, { env = process.env, capture = captureSource } = {}) {
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
    try {
      const tests = [...new Set(batch.rows.map(row => row?.test).filter(test => typeof test === 'string'))].sort();
      if (/^[a-f0-9]{64}$/.test(batch.source_sha256 ?? '') && tests.length) source = capture(root, { tests, appMap: null }).sha256 === batch.source_sha256 ? 'current' : 'changed';
    } catch { source = 'unknown'; }
    const stories = Array.isArray(summary?.rows) ? [...new Set(summary.rows.map(row => text(row?.summary_line)).filter(Boolean))] : [];
    results.push({ kind: 'pdd test', batch: check.name, at: check.at, source,
      summary: text(summary?.summary_line) || 'result not saved (the check did not finish)', stories,
      engine: text(first(batch.rows.map(row => row?.engine_sha)), 12) || null, model: text(first(batch.rows.map(row => row?.requested_model)), 80) || null });
  }
  if (lint) {
    const rows = lint.batch.rows.filter(row => row && typeof row === 'object');
    const passing = rows.filter(row => row.state === 'passed').length, ended = ['passed', 'failed', 'refused'].includes(lint.batch.lint?.state) || rows.every(row => ['passed', 'failed', 'refused'].includes(row.state));
    results.push({ kind: 'pdd lint', batch: lint.name, at: lint.at, summary: ended ? `Lint: ${passing} of ${rows.length} tests pass. 0 AI calls.` : 'Lint: result unknown (the lint did not finish).' });
  }
  if (runDir) {
    const path = join(runDir, 'old-code-proof.json'), proof = readJson(path);
    if (proof && proof.runId === runId && typeof proof.outcome === 'string') {
      let at = NaN; try { at = lstatSync(path).mtimeMs; } catch { /* no time */ }
      results.push({ kind: 'pdd workflow prove', at: Math.round(at), summary: `Old-code proof: ${text(proof.outcome, 40)}`, baseSha: text(proof.baseSha, 40), headSha: text(proof.headSha, 40) });
    }
  }
  return results;
}

// One line per result, each starting with "pdd result:", so a reader can tell pdd's own results from agent notes.
export function resultLines(results, { kinds = null } = {}) {
  const shown = (results ?? []).filter(result => !kinds || kinds.includes(result.kind));
  if (!shown.length) return [noResultLine(kinds ?? KINDS)];
  return shown.map(result => {
    const facts = [result.batch && `batch ${result.batch}`, iso(result.at), result.source && `source ${result.source}`,
      result.engine && `engine ${result.engine}`, result.model && `model ${result.model}`,
      result.headSha && `head ${result.headSha.slice(0, 7)}`].filter(Boolean).join(', ');
    return `${PDD_RESULT}: ${result.kind} (${facts}): ${[result.summary, ...(result.stories ?? []).filter(line => line !== result.summary)].join('; ')}`;
  });
}
