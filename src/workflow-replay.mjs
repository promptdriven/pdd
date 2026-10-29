// Generated from prompts/cli/workflow-replay.prompt.md (sha256: 4204cf58756e541bb3e0d43e8180fdc71394bc99ea69676396239617eab271a7).
import { createHash } from 'node:crypto';
import { closeSync, constants, fstatSync, lstatSync, openSync, readFileSync, readlinkSync, readSync } from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { gitFiles } from './runtime-preflight.mjs';
import { cleanText } from './runtime-output.mjs';
export const REPLAY_POLICY = 'pdd.replay-evidence.v1';
const LIMIT = 2 * 1024 * 1024, MAX = 10000;
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const object = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const text = v => typeof v === 'string' && v.trim().length > 0 && v.length <= 1000;
const parse = bytes => JSON.parse(new TextDecoder('utf-8',{fatal:true}).decode(bytes));
const sha = v => typeof v === 'string' && /^[a-f0-9]{64}$/.test(v);
const integer = v => Number.isSafeInteger(v) && v >= 0;
const exit = v => integer(v) && v <= 255;
const requireThat = (condition, message) => { if (!condition) throw Error(message); };
const key = row => JSON.stringify([row.vector, row.step_id, row.check_index]);
const stepKey = row => JSON.stringify([row.vector, row.step_id]);
const identity = ['entry_path','operation','criterion_id','target','path','op'];
const states = ['pass','fail','blocked','not_replayed'];
const controls = ['assertion_failure','crash','survived','not_run'];
const sanitize = value => cleanText(String(value ?? '')).replace(/[\r\n\x00-\x1f]/g,' ').slice(0,1000)
  .replace(/https?:\/\/[^\s]+\/s\/[^\s]+/g,'(Try link removed)');
const render = value => sanitize(value).replace(/[\\`*_[\]()|]/g,'\\$&')
  .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');

export function sourceFingerprint(root) {
  try {
    const files = gitFiles(root).sort().map(path => {
      const full = join(root, path);
      let stat; try { stat = lstatSync(full); } catch (error) { if (error.code === 'ENOENT') return [path, 'missing']; throw error; }
      if (stat.isSymbolicLink()) return [path, 'link', readlinkSync(full)];
      if (!stat.isFile()) throw Error('Not a regular source file');
      return [path, stat.mode & 0o111, hash(readFileSync(full))];
    });
    return hash(JSON.stringify(files));
  } catch { return null; }
}
function boundedFile(path, max = LIMIT) {
  for (let parent = dirname(path); ; parent = dirname(parent)) {
    requireThat(!lstatSync(parent).isSymbolicLink(), 'Evidence paths cannot traverse symbolic links.');
    if (dirname(parent) === parent) break;
  }
  const fd = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_NONBLOCK);
  try {
    const stat = fstatSync(fd);
    requireThat(stat.isFile() && stat.nlink === 1, 'Evidence must be a regular single-link file.');
    requireThat(stat.size > 0 && stat.size <= max, 'Evidence is empty or exceeds its byte limit.');
    const bytes = Buffer.alloc(Math.min(max + 1, stat.size + 1));
    let size = 0, read;
    while (size < bytes.length && (read = readSync(fd,bytes,size,bytes.length-size,null))) size += read;
    requireThat(size === stat.size && fstatSync(fd).size === size, 'Evidence changed while being read.');
    return bytes.subarray(0,size);
  } finally { closeSync(fd); }
}
function vectorFile(root, path, visible) {
  requireThat(text(path) && !isAbsolute(path) && !path.includes('\\') && !path.split('/').some(p => !p || p === '.' || p === '..'), 'Vector paths must be canonical repository-relative paths.');
  const rel = relative(root,resolve(root,path));
  requireThat(rel && !rel.startsWith('..') && !rel.startsWith(sep) && visible.has(path), 'An original vector is not Git-visible in this repository.');
  return boundedFile(join(root,path));
}
function scenario(path, bytes) {
  const doc = parse(bytes);
  requireThat(object(doc) && doc.schema_version === 'prompt-runtime.program-scenario.v1' && Array.isArray(doc.steps) && doc.steps.length > 0 && doc.steps.length <= MAX, 'Original vectors need nonempty versioned scenario steps.');
  const seen = new Set(), steps = [], checks = [];
  for (const step of doc.steps) {
    requireThat(object(step) && text(step.step_id) && !seen.has(step.step_id) && text(step.entry_path) && text(step.operation), 'Original step identities must be complete and unique.');
    seen.add(step.step_id);
    requireThat(Array.isArray(step.checks) && step.checks.length > 0 && step.checks.length <= MAX, 'Every original step needs assertion checks.');
    const base = {vector:path,step_id:step.step_id,entry_path:step.entry_path,operation:step.operation}; steps.push(base);
    step.checks.forEach((check,check_index) => {
      requireThat(object(check) && text(check.criterion_id) && ['result','error','world','calls'].includes(check.target) && typeof check.path === 'string' && check.path.length <= 1000 && text(check.op), 'Original assertion identities are incomplete or unsupported.');
      checks.push({...base,check_index,criterion_id:check.criterion_id,target:check.target,path:check.path,op:check.op});
    });
  }
  return {path,sha256:hash(bytes),steps,checks};
}
export function pinReplayVectors(root, paths) {
  const anchor = {schema_version:'pdd.replay-vectors.v1',vectors:[]};
  try {
    requireThat(Array.isArray(paths) && paths.length <= 200 && new Set(paths).size === paths.length, 'Original vector selection is invalid or too large.');
    if (!paths.length) return {...anchor,outcome:'not_replayed',reason:'The approved prompt area has no original scenario vectors.'};
    const visible = new Set(gitFiles(root)); let bytes = 0, count = 0, steps = 0;
    for (const path of paths) {
      const raw = vectorFile(root,path,visible); bytes += raw.length;
      requireThat(bytes <= 10*1024*1024, 'Original vectors exceed 10 MiB.');
      const vector = scenario(path,raw);count += vector.checks.length;steps += vector.steps.length;
      requireThat(count <= MAX && steps <= MAX, 'Original vectors exceed the step/check limit.');anchor.vectors.push(vector);
    }
    return anchor;
  } catch (e) { return {...anchor,outcome:'blocked',reason:sanitize(e.message)}; }
}
const emptyCounts = (total=0) => ({total,pass:0,fail:0,blocked:0,not_replayed:total});
export function readReplayEvidence(run) {
  let result = {outcome:'blocked',reason:'Structured replay evidence is unavailable.',counts:emptyCounts(),vectors:[],source:null,manifest_sha256:null,operations:{total:0,executed:0}};
  try {
    const baseline = run.replayBaseline;
    requireThat(baseline?.schema_version === 'pdd.replay-vectors.v1' && Array.isArray(baseline.vectors) && baseline.vectors.length <= 200, 'No approved original-vector anchor is saved; return to prompt space.');
    result.vectors = baseline.vectors.map(({path,sha256})=>({path,sha256}));
    if (baseline.outcome) return {...result,outcome:baseline.outcome === 'not_replayed' ? 'not_replayed':'blocked',reason:sanitize(baseline.reason)};
    requireThat(baseline.vectors.length > 0, 'The original vector set is empty.');
    const current = pinReplayVectors(run.root,baseline.vectors.map(v=>v.path));
    requireThat(!current.outcome && JSON.stringify(current.vectors) === JSON.stringify(baseline.vectors), 'Original vectors changed, are absent, empty, unreadable or no longer match their approved hashes.');
    const checks = baseline.vectors.flatMap(v=>v.checks), steps = baseline.vectors.flatMap(v=>v.steps);
    result.counts=emptyCounts(checks.length);result.operations.total=steps.length;
    const expected = new Map(checks.map(row=>[key(row),row])), expectedSteps = new Map(steps.map(row=>[stepKey(row),row]));
    requireThat(checks.length > 0 && checks.length <= MAX && expected.size === checks.length && steps.length <= MAX && expectedSteps.size === steps.length, 'Original assertion/operation identities are empty or duplicated.');
    const bytes = boundedFile(join(run.runDir,'replay-evidence.json'));result.manifest_sha256=hash(bytes);
    const doc = parse(bytes);
    requireThat(object(doc) && doc.schema_version === REPLAY_POLICY && doc.run_id === run.runId, 'The replay manifest version or run identity is invalid.');
    const fingerprint = sourceFingerprint(run.root);
    requireThat(object(doc.source) && doc.source.kind === 'git-content-v1' && sha(doc.source.sha256) && fingerprint !== null && doc.source.sha256 === fingerprint, 'Replay evidence is stale or its source fingerprint is invalid.');result.source={kind:'git-content-v1',sha256:doc.source.sha256};
    requireThat(Array.isArray(doc.vectors) && doc.vectors.length === baseline.vectors.length && new Set(doc.vectors.map(v=>v?.path)).size === doc.vectors.length, 'The manifest must name every original vector exactly once.');
    const originals = new Map(result.vectors.map(v=>[v.path,v.sha256]));
    requireThat(doc.vectors.every(v=>object(v) && sha(v.sha256) && originals.get(v.path) === v.sha256), 'The manifest changed or substituted an original vector hash.');
    requireThat(Array.isArray(doc.checks) && doc.checks.length <= MAX && Array.isArray(doc.operations) && doc.operations.length <= MAX, 'The manifest needs bounded check and operation rows.');
    const rows = new Map(), operations = new Map();
    for (const row of doc.checks) {
      requireThat(object(row) && integer(row.check_index) && states.includes(row.outcome), 'An assertion row has an invalid outcome or identity.');
      const original=expected.get(key(row));
      requireThat(original && !rows.has(key(row)) && identity.every(k=>row[k] === original[k]), 'An assertion row is unknown, duplicated or mismatches its original operation/target.');
      requireThat((row.reason === undefined || text(row.reason)) && (!['blocked','not_replayed'].includes(row.outcome) || text(row.reason)), 'Unmapped/blocked checks need a reason.');rows.set(key(row),row);
    }
    for (const row of doc.operations) {
      requireThat(object(row), 'Invalid public-operation row.');const original=expectedSteps.get(stepKey(row));
      requireThat(original && !operations.has(stepKey(row)) && ['entry_path','operation'].every(k=>row[k]===original[k]), 'A public operation is unknown, duplicated or substituted.');
      requireThat(typeof row.executed === 'boolean' && ['returned','expected_error','crash','not_run'].includes(row.outcome), 'Public execution flags/outcomes must be typed.');
      if (row.executed) requireThat(row.outcome !== 'not_run' && object(row.boundary) && ['function','command','route'].includes(row.boundary.kind) && text(row.boundary.name) && text(row.command) && exit(row.exit_code), 'Executed operations need a real public-boundary identity and command/exit record.');
      else requireThat(row.outcome === 'not_run' && row.exit_code === null, 'An unexecuted operation cannot claim completion.');
      operations.set(stepKey(row),row);
    }
    const counts = {total:checks.length,pass:0,fail:0,blocked:0,not_replayed:0};
    for (const original of checks) {
      const op=operations.get(stepKey(original)), row=rows.get(key(original));
      const outcome=(!op?.executed || !['returned','expected_error'].includes(op.outcome)) ? 'not_replayed' : row?.outcome ?? 'not_replayed';counts[outcome]++;
    }
    requireThat(object(doc.counts) && Object.keys(counts).every(k=>integer(doc.counts[k]) && doc.counts[k]===counts[k]), 'Replay counts do not equal the original assertion outcomes.');
    result.counts=counts;result.operations.executed=[...operations.values()].filter(op=>op.executed && ['returned','expected_error'].includes(op.outcome)).length;
    const mutation=doc.mutation;
    requireThat(object(mutation) && mutation.kind === 'semantic' && text(mutation.description) && controls.includes(mutation.outcome) && (mutation.outcome === 'not_run' ? text(mutation.reason) && mutation.exit_code === null && (mutation.command === null || text(mutation.command)) : text(mutation.command) && exit(mutation.exit_code)) && Array.isArray(mutation.failed_checks) && mutation.failed_checks.length <= MAX, 'A typed semantic mutation-control record is required.');
    const failed=new Set();for(const row of mutation.failed_checks) {requireThat(object(row) && integer(row.check_index) && expected.has(key(row)) && !failed.has(key(row)), 'Mutation failures must name unique original assertions.');failed.add(key(row));}
    result.mutation={outcome:mutation.outcome,failures:failed.size,description:sanitize(mutation.description)};
    const formal=doc.formal;
    requireThat(object(formal) && ['proved_bounded','proved_solver','failed','not_run','not_applicable'].includes(formal.result) && text(formal.scope) && text(formal.reason) && controls.includes(formal.control_outcome), 'A typed formal result, scope, reason and control outcome are required.');
    requireThat(formal.result !== 'failed' || Object.hasOwn(formal,'counterexample'), 'A failed formal check needs its counterexample.');
    result.formal={result:formal.result,scope:sanitize(formal.scope),reason:sanitize(formal.reason),control_outcome:formal.control_outcome};
    const detected=mutation.outcome === 'assertion_failure' && mutation.exit_code !== 0 && failed.size > 0;
    requireThat(!formal.result.startsWith('proved_') || (detected && formal.control_outcome === 'assertion_failure'), 'A proved formal check needs semantic assertion-failure control, not a crash.');
    const outcome=counts.blocked ? 'blocked' : counts.not_replayed ? 'not_replayed' : !detected ? 'blocked' : counts.fail || formal.result === 'failed' ? 'fail' : 'pass';
    return {...result,outcome,reason:counts.blocked ? 'Some checks are blocked.' : counts.not_replayed ? 'Some original assertions or public operations were not replayed.' : !detected ? 'The semantic mutation control did not detect an assertion failure; a crash is not detection.' : outcome==='fail' ? 'Assertion or formal failures were recorded.' : 'All original assertions have source-bound public-boundary replay evidence.'};
  } catch (e) { return {...result,outcome:'blocked',reason:e.code==='ENOENT' ? 'Missing replay-evidence.json or an original vector; code replay is blocked.' : sanitize(e.message || 'Malformed replay evidence.')}; }
}
export function formatReplayEvidence(result) {
  const counts=result.counts??emptyCounts(), label=String(result.outcome).replace('_',' ').toUpperCase();
  const formalLabel={proved_bounded:'Proved (bounded)',proved_solver:'Proved (solver)',failed:'Failed + counterexample',not_run:'Not run',not_applicable:'Not applicable'};
  return [ ...(counts.fail ? [`✗ ${counts.fail} replay assertions fail`] : []), ...(result.formal?.result==='failed' ? ['✗ Formal check failed (counterexample in replay-evidence.json).'] : []),
    `Code replay: ${label} — ${render(result.reason)}`,`${counts.total} checks: ${counts.pass} passed, ${counts.fail} failed, ${counts.blocked} blocked, ${counts.not_replayed} not replayed.`,
    `Public-boundary operations: ${result.operations?.executed??0}/${result.operations?.total??0} executed.`,
    `Semantic mutation control: ${result.mutation?.outcome??'not recorded'}${result.mutation ? ` (${result.mutation.failures} assertion failures)` : ''}.`,
    `Formal check (agent reported): ${formalLabel[result.formal?.result]??'not recorded'}${result.formal ? `; scope: ${render(result.formal.scope)}; reason: ${render(result.formal.reason)}` : ''}.`,
    `Source: ${result.source?.sha256??'unconfirmed'}. Manifest SHA256: ${result.manifest_sha256??'unavailable'}.`,
    ...(result.vectors??[]).slice(0,12).map(v=>`Original vector: ${render(v.path)} — ${sha(v.sha256)?v.sha256:'unconfirmed'}.`),
    ...((result.vectors?.length??0)>12 ? [`${result.vectors.length-12} more original vector identities are in the full manifest.`] : []),
    'Agents execute the tests and supply this record. pdd validates structure and identity; it does not independently prove execution or prompt/code equivalence.',
    'Full evidence: replay-evidence.json in the run folder.'].join('\n');
}
