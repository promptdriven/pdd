import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

for (const failed of [false, true]) test(`criterion coverage survives immediate and saved/read output (${failed ? 'failed' : 'passed'})`, async t => {
  const setup = harbor(t, repo => {
    const path = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(path));
    // Synthetic authored checks: one mixed criterion, one exit-only criterion,
    // another output criterion.
    doc.steps[0].checks = [
      { criterion_id: 'AC1', target: 'result', path: '/exit_code', op: 'equals', value: 0 },
      { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'printed' },
      { criterion_id: 'AC2', target: 'result', path: '/exit_code', op: 'equals', value: 0 },
      { criterion_id: 'AC3', target: 'result', path: '/stdout', op: 'equals', value: 'printed' }
    ];
    doc.steps.push({ ...doc.steps[0], step_id: 'second', checks: [
      { criterion_id: 'AC2', target: 'result', path: '/exitCode', op: 'equals', value: 0 }
    ] });
    writeFileSync(path, JSON.stringify(doc));
  });
  const fake = await fakeRuntime(t, (entry, f) => entry.command === 'lint' ? { status: 200, json: f.lint(entry.request.requestId) }
    : entry.command === 'check' ? { status: 200, json: f.check(entry.request.requestId, failed ? 'failed' : 'passed', [{ criterion_id:'AC1', target:'result', path:'/stdout', expected:'printed', actual: failed ? 'other' : 'printed', passed:!failed }]) }
      : assert.fail(`unexpected request ${entry.url}`));
  const env = { HOME:setup.home, PDD_STATE_DIR:setup.state, PDD_RUNTIME_URL:fake.origin };
  const invoke = async (options, words = ['place-order']) => {
    const { ports } = portsFor(env);
    const code = await runCheck({cwd:setup.repo, words, options}, ports);
    assert.equal(code, failed ? 1 : 0, ports.stderr.text + ports.stdout.text);
    return ports.stdout.text;
  };
  const immediate = JSON.parse(await invoke({'--json':true}));
  const facts = immediate.rows[0].criterion_coverage;
  assert.deepEqual(facts.slice(0, 3), [
    {criterion_id:'AC1', check_count:2, exit_code_only:false},
    {criterion_id:'AC2', check_count:2, exit_code_only:true},
    {criterion_id:'AC3', check_count:1, exit_code_only:false}
  ]);
  const posts = fake.posts.length;
  const reread = JSON.parse(await invoke({'--read':true,'--json':true}, [immediate.batch]));
  assert.deepEqual(reread.rows[0].criterion_coverage, facts);
  const text = await invoke({'--read':true}, [immediate.batch]);
  assert.match(text, /criterion AC2:.*checked by exit code only/);
  assert.doesNotMatch(text, /criterion AC1:.*checked by exit code only|criterion AC3:.*checked by exit code only/);
  assert.equal(fake.posts.length, posts, 'saved reads do not execute checks');
  const immediateText = await invoke({});
  assert.match(immediateText, /criterion AC2:.*checked by exit code only/);
});
