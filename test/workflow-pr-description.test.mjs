import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
const {stepDone, approveRun} = await import(process.env.PDD_DESCRIPTION_RUNNER || '../src/workflow-runner.mjs');

const classic = 'GraphQL: Projects (classic) is being deprecated in favor of the new Projects experience (repository.pullRequest.projectCards)';
const ok = result => assert.equal(result.exitCode, 0, result.message);
async function published(t) {
  const f = await fixture(t, {agent: 'codex'}), exec = f.ports.execFile;
  f.patches = []; f.legacyEdits = 0;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'edit') {
      f.legacyEdits++;
      return {code: 1, stdout: '', stderr: classic};
    }
    if (file === 'gh' && args[0] === 'api' && args.includes('PATCH')) {
      f.patches.push({args, input: options.input});
      if (f.failure) return f.failure();
    }
    return exec(file, args, options);
  };
  ok(await f.run());
  f.done = (step, summary = 'Synthetic regression step') => stepDone({step, summary, cwd: f.record().root}, f.agentPorts());
  ok(await f.done('scope'));
  ok(await approveRun({ref: '17', cwd: f.source, said: 'Synthetic approval for isolated native test.'}, f.ports));
  writeFileSync(join(f.record().root, 'value.mjs'), 'export const value = 2;\n');
  for (const step of ['change', 'verify', 'formal']) ok(await f.done(step));
  assert.equal(f.prs.length, 1);
  f.change = () => {
    const root = f.record().root;
    writeFileSync(join(root, 'value.mjs'), 'export const value = 3;\n');
    f.git(root, 'commit', '-qam', 'Source update');
  };
  return f;
}

test('2830: descriptions update when gh pr edit has the Projects classic failure', async t => {
  const f = await published(t);
  f.change();
  const summary = 'Multiline description: "quotes", café 😀 and $literal\nSecond line: `code` and \\backslash';
  const result = await f.done('formal', summary);
  ok(result);
  assert.equal(f.legacyEdits, 0, 'PR descriptions must bypass the Projects classic query');
  assert.equal(f.patches.length, 2, 'Pending and final descriptions both use REST');
  for (const patch of f.patches) {
    assert.deepEqual(patch.args, ['api', '--hostname', 'github.com', '--method', 'PATCH', 'repos/example/project/pulls/23', '--input', '-']);
    assert.deepEqual(Object.keys(JSON.parse(patch.input)), ['body']);
  }
  const body = JSON.parse(f.patches.at(-1).input).body;
  assert.equal(body, f.prs[0].body, 'The entire body survives JSON stdin transport');
  assert.ok(body.includes(summary.split('\n')[0]));
  assert.ok(body.includes(summary.split('\n')[1]));
  assert.ok(body.includes('\n'));
});

for (const mode of ['returned exit', 'thrown stderr', 'thrown message']) {
  test(`2830: ${mode} preserves a safe gh diagnostic and retry before any source push`, async t => {
    const f = await published(t), previous = f.prs[0].body, pushes = f.pushes.length;
    f.change();
    const token = 'ghp_abcdefghijklmnopqrstuvwxyz0123456789ABCD';
    const diagnostic = `\x1b[31mgh: description permission denied\x1b[0m\t${token}\r\nsecond diagnostic line`;
    f.failure = () => {
      if (mode === 'returned exit') return {code: 1, stdout: '', stderr: diagnostic};
      if (mode === 'thrown stderr') throw Object.assign(Error('Command failed'), {code: 1, stderr: diagnostic});
      throw Object.assign(Error(diagnostic), {code: 1});
    };
    const result = await f.done('formal');
    assert.equal(result.exitCode, 1);
    assert.match(result.message, /description permission denied/);
    assert.match(result.message, /workflow done formal/);
    assert.doesNotMatch(result.message, /ghp_|\x1b|second diagnostic line/);
    assert.ok(result.message.split('\n').some(line => line.includes('description permission denied') && line.includes('workflow done formal')));
    assert.equal(f.pushes.length, pushes, 'Failed pending update cannot push new source');
    assert.equal(f.prs[0].body, previous);
  });
}

test('2830: rejected final REST update keeps publication pending and names gh and retry', async t => {
  const f = await published(t), exec = f.ports.execFile;
  f.change();
  let updates = 0;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'gh' && args[0] === 'api' && args.includes('PATCH') && ++updates === 2)
      return {code: 1, stderr: 'gh: final description rejected (HTTP 403)', stdout: ''};
    return exec(file, args, options);
  };
  const pushes = f.pushes.length, result = await f.done('formal');
  assert.equal(result.exitCode, 1);
  assert.match(result.message, /final description rejected \(HTTP 403\)/);
  assert.match(result.message, /workflow done formal/);
  assert.match(result.message, /Source was pushed; the PR stays publication-pending/);
  assert.equal(f.pushes.length, pushes + 1);
  assert.match(f.prs[0].body, /publication-pending/);
});
