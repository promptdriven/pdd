// Generated from prompts/cli/code-replay.prompt.md (sha256: 6c89c2434a019758e09681d2729d50ca4099ad9c3513cf376cd42a99d0eeeba1).
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { lstatSync, readFileSync, readlinkSync, realpathSync } from 'node:fs';
import { isAbsolute, join, relative, resolve } from 'node:path';
import { findTests, gitFiles } from './runtime-preflight.mjs';

const finiteJson = value => {
  const pending = [value];
  while (pending.length) {
    const item = pending.pop();
    if (typeof item === 'number' && !Number.isFinite(item)) return false;
    if (item && typeof item === 'object') for (const value of Object.values(item)) pending.push(value);
  }
  return true;
};
const scenarioSchema = 'prompt-runtime.program-scenario.v1';
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const text = value => typeof value === 'string' && value.trim().length > 0;
const require = (ok, reason) => { if (!ok) throw Error(reason); };
const reasonOf = error => error instanceof SyntaxError ? 'Replay evidence or original vectors contain invalid JSON.' : String(error.message).replace(/\s+/g, ' ').slice(0, 250);
const control = value => value?.kind === 'semantic' && text(value.command) && value.crashed === false
  && Number.isSafeInteger(value.assertion_failures) && value.assertion_failures > 0;
function bytesAt(root, path) {
  require(text(path) && !isAbsolute(path), 'Vector path must be repository-relative.');
  const file = resolve(root, path), rel = relative(realpathSync(root), realpathSync(file));
  require(rel && !rel.startsWith('..') && !isAbsolute(rel) && lstatSync(file).isFile(), 'Vector must be a repository-contained regular file.');
  return readFileSync(file);
}
export function sourceFingerprint(root) {
  try {
    return hash(JSON.stringify(gitFiles(root).sort().map(path => {
      const full = join(root, path);
      let stat; try { stat = lstatSync(full); } catch (error) { if (error.code === 'ENOENT') return [path, 'missing']; throw error; }
      if (stat.isSymbolicLink()) return [path, 'link', readlinkSync(full)];
      require(stat.isFile(), 'Not a regular source file.');
      return [path, stat.mode & 0o111, hash(readFileSync(full))];
    })));
  } catch { return null; }
}
export function freezeReplayVectors(root, { committed = false } = {}) {
  try {
    const git = args => execFileSync('git', args, { cwd: root, maxBuffer: 16 * 1024 * 1024 });
    let tests;
    if (committed) {
      const entries = git(['ls-tree', '-r', '-z', 'HEAD']).toString('utf8').split('\0').filter(Boolean);
      tests = [];
      for (const entry of entries) {
        const tab = entry.indexOf('\t'), metadata = entry.slice(0, tab), path = entry.slice(tab + 1);
        if (!path.endsWith('.json')) continue;
        const bytes = git(['show', `HEAD:${path}`]);
        if (!bytes.toString('utf8').includes('prompt-runtime.program-scenario')) continue;
        require(/^100(?:644|755) blob /.test(metadata), 'Original vectors must be regular Git blobs.');
        const doc = JSON.parse(bytes.toString('utf8'));
        if (typeof doc?.schema_version !== 'string' || !doc.schema_version.startsWith('prompt-runtime.program-scenario')) continue;
        require(doc.schema_version === scenarioSchema && finiteJson(doc), 'Original vector schema or numeric values are invalid.');
        tests.push({ path, doc, bytes });
      }
    } else tests = findTests({ root }).tests;
    require(tests.length > 0, 'No original scenario vectors were found.');
    return { schema_version: 'code-replay-v1', vectors: tests.map(test => {
      require(test.doc?.schema_version === scenarioSchema && !test.error && finiteJson(test.doc), 'An original vector is unreadable or unsupported JSON.');
      return { path: test.path, sha256: hash(test.bytes ?? bytesAt(root, test.path)) };
    }) };
  } catch (error) { return { schema_version: 'code-replay-v1', vectors: [], error: reasonOf(error) }; }
}
export function readCodeReplay({ root, runDir, baseline }) {
  const counts = { pass: 0, fail: 0, blocked: 0, not_replayed: 0, total: 0, operations: 0, executed: 0 };
  let manifest_sha256 = null;
  const result = (status, reason, extra = {}) => ({ schema_version: 'code-replay-v1', status, reason, counts,
    manifest_sha256, execution_evidence: 'agent_reported', ...extra });
  try {
    require(baseline?.schema_version === 'code-replay-v1' && baseline.vectors?.length && !baseline.error, 'Original vector baseline is unavailable or empty.');
    const path = join(runDir, 'code-replay.json'), stat = lstatSync(path);
    require(stat.isFile() && stat.size <= 2 * 1024 * 1024, 'code-replay.json must be a regular file of at most 2 MiB.');
    const bytes = readFileSync(path); manifest_sha256 = hash(bytes);
    const doc = JSON.parse(bytes.toString('utf8')), current = sourceFingerprint(root);
    require(finiteJson(doc), 'Replay evidence contains nonfinite JSON numbers.');
    require(doc.schema_version === 'code-replay-v1' && current && doc.source_sha256 === current, 'Replay source identity is missing or stale.');
    require(Array.isArray(doc.vectors) && doc.vectors.length === baseline.vectors.length, 'Replay vector inventory is incomplete.');
    const seen = new Set();
    for (const original of baseline.vectors) {
      require(!seen.has(original.path), 'Duplicate original vector path.'); seen.add(original.path);
      const rows = doc.vectors.filter(row => row?.path === original.path);
      require(rows.length === 1, 'Replay vector paths must be unique and match the baseline.');
      const vector = rows[0], bytes = bytesAt(root, original.path);
      require(hash(bytes) === original.sha256 && vector.sha256 === original.sha256, 'Original vector bytes changed or the vector hash mismatches.');
      const scenario = JSON.parse(bytes.toString('utf8'));
      require(scenario.schema_version === scenarioSchema && finiteJson(scenario), 'Original vector schema or numeric values are invalid.');
      require(Array.isArray(scenario.criteria) && scenario.criteria.length > 0, 'Original criteria are missing.');
      const criteria = new Set();
      for (const item of scenario.criteria) {
        require(text(item?.id) && text(item.text) && !criteria.has(item.id), 'Original criteria need unique IDs and text.');
        criteria.add(item.id);
      }
      require(Array.isArray(scenario.steps) && scenario.steps.length > 0 && Array.isArray(vector.steps) && vector.steps.length === scenario.steps.length, 'Every original step must be replayed.');
      const ids = new Set();
      for (const [index, step] of scenario.steps.entries()) {
        const replay = vector.steps[index];
        require(text(step.step_id) && !ids.has(step.step_id) && text(step.operation), 'Original step identities must be unique.'); ids.add(step.step_id);
        require(replay?.step_id === step.step_id && replay.operation === step.operation, 'Replay step/operation does not match the original.');
        counts.operations++;
        const executed = replay.execution?.executed === true && text(replay.execution.boundary) && text(replay.execution.command);
        if (executed) counts.executed++;
        require(Array.isArray(step.checks) && step.checks.length > 0 && Array.isArray(replay.checks) && replay.checks.length === step.checks.length, 'Every original check must have one replay row; empty reports cannot pass.');
        for (const [at, check] of step.checks.entries()) {
          require(text(check?.criterion_id) && criteria.has(check.criterion_id) && text(check.target) && text(check.op)
            && typeof check.path === 'string' && (check.path === '' || /^\/(?:[^~]|~[01])*$/.test(check.path)), 'Original check identity is invalid.');
          const row = replay.checks[at];
          require(row && ['criterion_id', 'target', 'path', 'op'].every(key => row[key] === check[key]), 'Replay check identity does not match the original.');
          require(['pass', 'fail', 'blocked', 'not_replayed'].includes(row.status), 'Replay check needs a typed outcome.');
          require(!['pass', 'fail'].includes(row.status) || Object.hasOwn(row, 'actual'), 'Executed check rows need an observed actual value.');
          require(row.status === 'pass' || text(row.reason), 'Incomplete or failed checks need a reason.');
          const mapped = ['result', 'error', 'world', 'calls'].includes(check.target);
          const status = !mapped || !executed ? 'not_replayed' : row.status;
          counts[status]++; counts.total++;
        }
      }
    }
    const formal = doc.formal;
    require(formal && ['proved_bounded', 'proved_solver', 'failed', 'not_run', 'not_applicable'].includes(formal.status) && text(formal.rule), 'A typed formal result and rule are required.');
    if (formal.status.startsWith('proved_')) require(text(formal.bounds) && text(formal.command) && control(formal.control), 'A proved formal result needs bounds, command and semantic control.');
    else if (formal.status === 'failed') require(text(formal.counterexample), 'Formal failure needs a counterexample.');
    else require(text(formal.reason), 'A formal non-result needs a reason.');
    const extra = { source_sha256: current, vectors: baseline.vectors, mutation_detected: control(doc.mutation), formal_status: formal.status };
    if (counts.fail || formal.status === 'failed') return result('fail', 'Recorded assertions or the formal check failed.', extra);
    if (counts.blocked || !control(doc.mutation) || formal.status === 'not_run') return result('blocked', 'Replay needs complete checks, semantic mutation detection and the formal result.', extra);
    if (counts.not_replayed) return result('not_replayed', 'Some original checks or public operations were not replayed.', extra);
    return result('pass', 'All original checks have passing agent-reported execution evidence and semantic controls.', extra);
  } catch (error) { return result('blocked', reasonOf(error)); }
}
export function codeReplayLine(outcome) {
  const status = { pass: 'PASS', fail: 'FAIL', blocked: 'BLOCKED', not_replayed: 'NOT REPLAYED' }[outcome.status];
  return `Code replay: ${status} · ${outcome.reason} · ${outcome.counts.pass}/${outcome.counts.total} checks pass · ${outcome.counts.executed}/${outcome.counts.operations} operations executed (agent-reported; CLI validates structure and source identity).`;
}
