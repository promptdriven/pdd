import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

// Rules to check: read-saved-lint.md. A confirmed standalone lint keeps its
// selected verdict and cannot authorize a new lint or paid Check. Exhaust all
// 32 combinations below at runCheck with real temporary Git/private state.
// Concurrent means two overlapping invocations, not all OS interleavings.
// No hosted Runtime, arbitrary histories, crashes or multiple rows are proved.
const domain = {
  history: ['pending-first', 'already-finished'], verdict: ['passed', 'refused'],
  output: ['text', 'json'], reference: ['explicit', 'latest'],
  schedule: ['sequential', 'concurrent'],
};
for (const history of domain.history) for (const verdict of domain.verdict)
for (const output of domain.output) for (const reference of domain.reference)
for (const schedule of domain.schedule) {
  test(`FORMAL saved lint ${history}/${verdict}/${output}/${reference}/${schedule}`, async t => {
    const h = harbor(t);
    let finished = history === 'already-finished';
    const diagnostic = { code: 'story-criterion-mismatch', file: 'tests/place-order.json',
      message: 'Criterion text does not match the Story.' };
    const f = await fakeRuntime(t, (entry, f) => {
      const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
      if (entry.command === 'check') return { status: 200, json: f.check(id) };
      if (!finished) return { status: entry.method === 'POST' ? 202 : 200, json: f.job(id, 'lint', 'running') };
      const answer = f.lint(id);
      if (verdict === 'refused') {
        answer.result.report.lint.tests[0].verdict = 'refused';
        answer.result.problems = [diagnostic];
      }
      return { status: 200, json: answer };
    });
    const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
    async function invoke(argv) {
      const p = portsFor(env), plan = parseArgv(argv);
      const code = await runCheck({ cwd: h.repo, words: plan.operands, options: plan.options }, p.ports);
      return { ...p, code };
    }
    // Oracle: Story AC1–4, independent of implementation helpers.
    const expectedExit = verdict === 'passed' ? 0 : 4;
    const seed = await invoke(['lint', 'place-order', '--timeout', '1', '--json']);
    assert.equal(seed.code, finished ? expectedExit : 3, 'specified initial history');
    finished = true;
    const batch = readdirSync(join(h.state, 'batches'), { withFileTypes: true }).find(e => e.isDirectory()).name;
    const folder = join(h.state, 'batches', batch);
    const saved = () => JSON.parse(readFileSync(join(folder, 'batch.json')));
    const before = saved(), originalPosts = f.posts.length;
    const argv = ['test', '--read', ...(reference === 'explicit' ? [batch] : []), ...(output === 'json' ? ['--json'] : [])];
    const recover = () => invoke(argv);
    const results = schedule === 'concurrent' ? await Promise.all([recover(), recover()]) : [await recover(), await recover()];
    const last = await recover();
    assert.equal(last.code, expectedExit, 'confirmed standalone verdict determines saved-read exit');
    for (const result of [...results, last]) {
      if (result.code === 3) {
        assert.equal(schedule, 'concurrent', 'only an overlapping owner may defer this terminal read');
        assert.equal(result.ports.stdout.text, '');
        continue;
      }
      assert.equal(result.code, expectedExit, 'confirmed standalone verdict determines saved-read exit');
      if (output === 'json') {
        const json = JSON.parse(result.ports.stdout.text);
        assert.equal(json.exit_code, expectedExit);
        assert.equal(json.rows[0].state, verdict, 'confirmed lint never becomes not_run or a false pass');
        assert.equal(json.lint_state, verdict);
        assert.notEqual(json.rows[0].reason?.code, 'lint-finished');
      }
    }
    const after = saved(), summary = JSON.parse(readFileSync(join(folder, 'summary.json')));
    assert.equal(summary.exit_code, expectedExit);
    assert.equal(summary.rows[0].state, verdict);
    assert.equal(summary.lint_state, verdict, 'saved summary remains a lint result');
    assert.ok(last.ports.stdout.text.includes(output === 'json' ? JSON.stringify(summary.summary_line) : summary.summary_line),
      'both formats expose the persisted lint summary');
    if (verdict === 'refused') assert.ok(last.ports.stdout.text.includes(diagnostic.code), 'refusal remains visible');
    assert.equal(after.rows[0].state, verdict);
    assert.notEqual(after.rows[0].note?.code, 'lint-finished');
    assert.deepEqual(after.rows[0].request_ids, []);
    assert.deepEqual(after.lint.request_ids, before.lint.request_ids);
    assert.equal(after.source_sha256, before.source_sha256);
    assert.equal(f.posts.length, originalPosts, 'standalone reads send zero new POSTs');
    assert.equal(f.posts.filter(e => e.command === 'check').length, 0);
    const gets = f.gets.length;
    assert.equal((await recover()).code, expectedExit);
    assert.equal(f.gets.length, gets, 'repeated terminal read uses persisted receipt');
    assert.equal(f.posts.length, originalPosts);
  });
}
