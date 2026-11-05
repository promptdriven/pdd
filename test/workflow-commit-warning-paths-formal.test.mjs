import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { stepDone, approveRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { readFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';

// Exhaust all one- and two-character names over this alphabet, for each status.
// Prefix and suffix keep every generated name valid and avoid warning delimiters.
const alphabet = ['a', ' ', '"'];
const names = [...alphabet, ...alphabet.flatMap(a => alphabet.map(b => a + b))].map(s => `f${s}.txt`);
const statuses = ['modified', 'untracked', 'rename'];
const steps = JSON.parse(readFileSync(join(packageRoot, 'skills/pdd-small-change/workflow.json'), 'utf8')).areas.at(-1).steps;
const afterVerify = steps.slice(steps.indexOf('verify') + 1);

for (const status of statuses) for (const name of names) {
  test(`exact warning path set: ${status} ${JSON.stringify(name)}`, async t => {
    const f = await fixture(t);
    if (status === 'modified') {
      writeFileSync(join(f.source, name), 'before\n');
      f.git(f.source, 'add', '--', name);
      f.git(f.source, 'commit', '-qm', 'tracked');
      f.git(f.source, 'update-ref', 'refs/remotes/origin/main', f.git(f.source, 'rev-parse', 'HEAD'));
    }
    assert.equal((await f.run()).exitCode, 0);
    let run = f.record();
    f.tick();
    assert.equal((await stepDone({ step: 'scope', summary: 'scope', cwd: run.root }, f.agentPorts())).exitCode, 0);
    f.tick();
    assert.equal((await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { HOME: f.ports.env.HOME } })).exitCode, 0);
    run = f.record();
    if (status === 'rename') f.git(run.root, 'mv', 'value.mjs', name);
    else writeFileSync(join(run.root, name), 'changed\n');
    // Verify the intended status, including a leading space for unstaged modifications.
    const porcelain = execFileSync('git', ['status', '--porcelain=v1', '-z'], { cwd: run.root, encoding: 'utf8' });
    assert.equal(porcelain.slice(0, 2), { modified: ' M', untracked: '??', rename: 'R ' }[status]);
    f.tick();
    assert.equal((await stepDone({ step: 'change', summary: 'change', cwd: run.root }, f.agentPorts())).exitCode, 0);
    writeFileSync(join(run.runDir, 'verify.md'), 'offline fixture\n');
    f.tick();
    let out = await stepDone({ step: 'verify', summary: 'fixture', cwd: run.root }, f.agentPorts());
    for (const step of afterVerify) {
      f.tick();
      out = await stepDone({ step, summary: `${step} done`, cwd: run.root }, f.agentPorts());
    }
    assert.equal(out.exitCode, 0);
    assert.equal(f.prs.length, 1);
    const committed = f.git(run.root, 'diff-tree', '--no-commit-id', '--name-only', '-r', '-z', 'HEAD').split('\0').filter(Boolean);
    assert.ok(committed.includes(name), 'destination was committed');
    const warning = out.message.match(/^warning: pdd committed (\d+) uncommitted file\(s\): (.*)\.$/m);
    assert.ok(warning);
    assert.equal(Number(warning[1]), 1);
    assert.deepEqual([warning[2]], [name], 'exact warning path set');
  });
}
