import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync, existsSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { fixture } from './helpers/workflow-delivery-fixture.mjs';
import { approveRun, stepDone } from '../src/workflow-runner.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { PLACE } from './runtime-fake.mjs';

const root = resolve(import.meta.dirname, '..');
const paths = ['prompts/a.prompt.md', 'prompts/b.prompt.md'];
async function ready(t) {
  const f = await fixture(t, { name: 'feature' });
  const started = await f.run();
  assert.equal(started.exitCode, 0, started.message);
  const run = f.record();
  mkdirSync(join(run.root, 'prompts'));
  const text = readFileSync(join(root, 'test/fixtures/harbor', PLACE), 'utf8')
    .replace('"status": "approved"', '"status": "draft"')
    .replace(/"prose_sha256": "[^"]*"/, '"prose_sha256": ""');
  writeFileSync(join(run.root, paths[0]), text);
  writeFileSync(join(run.root, paths[1]), '# Notes\n\nKeep the visible text exactly as reviewed.\n');
  for (const step of ['understand', 'visual', 'prompt-story']) {
    f.tick();
    const out = await stepDone({ step, summary: 'Review the selected text', cwd: run.root }, f.agentPorts());
    assert.equal(out.exitCode, 0, out.message);
  }
  f.herdr.idle();
  return { f, run: f.record() };
}

function change(run, kind) {
  if (kind.includes('layout')) {
    for (const path of paths) {
      const file = join(run.root, path);
      writeFileSync(file, '\r\n' + readFileSync(file, 'utf8')
        .replace(/ /g, '  ').replace('visible  text', 'visible\ntext').replace(/\n/g, '  \r\n\r\n') + '\r\n');
    }
  }
  if (kind.includes('fill')) {
    const out = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'test', '--fill-hash'],
      { cwd: run.root, encoding: 'utf8' });
    assert.equal(out.status, 0, out.stderr + out.stdout);
  }
  if (kind === 'text') {
    const file = join(run.root, paths[1]);
    writeFileSync(file, readFileSync(file, 'utf8').replace('Keep', 'Change'));
  }
}

for (const route of ['said', 'terminal']) {
  for (const kind of ['fill', 'layout', 'layout-fill', 'text']) {
    test(`2869 ${route}: ${kind} ${route === 'said' ? 'after gate display' : 'during confirmation'}`, async t => {
      const { f, run } = await ready(t);
      const before = readFileSync(join(run.runDir, 'status.json'), 'utf8');
      const journal = join(run.commonDir, 'pdd/approvals.json');
      let reviewed;
      const mutate = () => {
        change(run, kind);
        reviewed = paths.map(path => ({ path, proseSha256: proseSha256(readFileSync(join(run.root, path), 'utf8')) }));
      };
      if (route === 'said') mutate();
      const input = { ref: '17', cwd: run.root, ...(route === 'said' ? { said: 'I approve the text shown' } : {}) };
      const ports = route === 'said' ? f.agentPorts() : { ...f.ports, confirm: async () => { mutate(); return true; } };
      const out = await approveRun(input, ports);
      if (kind === 'text') {
        assert.equal(out.exitCode, 1, 'real text drift still needs another review');
        assert.match(out.message, /show.*gate.*again/i);
        assert.equal(existsSync(journal), false);
        assert.equal(f.record().decisions.length, 0);
        if (route === 'said') assert.equal(readFileSync(join(run.runDir, 'status.json'), 'utf8'), before);
        return;
      }
      assert.equal(out.exitCode, 0, out.message);
      const after = f.record();
      assert.equal(after.area, run.area + 1);
      assert.equal(after.decisions.length, 1);
      assert.deepEqual(after.decisions[0].evidence.prompts, reviewed, 'evidence records current exact prose hashes');
      assert.deepEqual(JSON.parse(readFileSync(journal, 'utf8')).approvals[0].prompts, reviewed);
      assert.match(readFileSync(join(run.root, paths[0]), 'utf8'), /"status"\s*:\s*"approved"/);
      for (const row of reviewed) assert.equal(proseSha256(readFileSync(join(run.root, row.path), 'utf8')), row.proseSha256,
        'approval preserves the latest reviewed layout');
    });
  }
}

test('2869 legacy exact snapshot remains usable for unchanged prose', async t => {
  const { f, run } = await ready(t);
  run.gate.promptSnapshot = run.gate.promptSnapshot.map(({ path, proseSha256 }) => ({ path, proseSha256 }));
  writeRun(run, f.ports);
  const out = await approveRun({ ref: '17', cwd: run.root, said: 'I approve' }, f.agentPorts());
  assert.equal(out.exitCode, 0, out.message);
  assert.equal(f.record().decisions.length, 1);
});
