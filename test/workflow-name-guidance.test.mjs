import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, writeFileSync, readdirSync, rmSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv, CommandInputError } from '../src/argument-parser.mjs';

const capture = () => ({ text: '', write(value) { this.text += value; } });

test('a missing workflow name gives the correction without starting work', async () => {
  for (const number of ['81', '42', '1', '9007199254740993']) {
    const stdout = capture(), stderr = capture();
    const exit = await runPdd(['workflow', 'run', number], {
      stdout, stderr, cwd: '/missing/project', packageRoot: '/missing/package',
      workflowRunner: new Proxy({}, { get() { assert.fail('Must not dispatch a workflow'); } }),
    });
    assert.equal(exit, 2);
    assert.equal(stdout.text, '');
    assert.equal(stderr.text, `Name the workflow: pdd workflow run small-change ${number} (or bug, feature). See pdd workflow list.\n`);
  }
});

test('workflow names, issue forms, help and invalid options retain their parsing', () => {
  for (const name of ['small-change', 'bug', 'feature', 'team-review']) {
    for (const issue of ['81', 'owner/repo#81', 'https://github.com/owner/repo/issues/81']) {
      assert.deepEqual(parseArgv(['workflow', 'run', name, issue]).operands, [name, issue]);
    }
  }
  assert.equal(parseArgv(['workflow', 'run', '--help']).local, 'help');
  for (const name of ['0', '01', '-1', 'owner/repo#81', 'https://github.com/owner/repo/issues/81']) {
    assert.throws(() => parseArgv(['workflow', 'run', name]), error => {
      assert.ok(error instanceof CommandInputError);
      assert.doesNotMatch(error.message, /Name the workflow:/);
      return true;
    });
  }
  for (const suffix of [['--unknown'], ['--agent', 'codex', '--agent', 'codex']]) {
    assert.throws(() => parseArgv(['workflow', 'run', '81', ...suffix]), error => {
      assert.ok(error instanceof CommandInputError);
      assert.doesNotMatch(error.message, /Name the workflow:/);
      return true;
    });
  }
});


test('the executable refuses the missing name without external commands or workflow files', t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-missing-workflow-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const cwd = join(root, 'project'), home = join(root, 'home'), bin = join(root, 'bin');
  for (const folder of [cwd, home, bin]) mkdirSync(folder);
  const effects = join(root, 'effects');
  for (const command of ['gh', 'git', 'herdr', 'codex', 'claude', 'pdd']) {
    writeFileSync(join(bin, command), '#!/bin/sh\nprintf invoked >> "$EFFECT_LOG"\nexit 99\n', { mode: 0o755 });
  }
  const reply = spawnSync(process.execPath, [fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url)), 'workflow', 'run', '81'], {
    cwd, encoding: 'utf8', env: { HOME: home, PATH: bin, EFFECT_LOG: effects },
  });
  assert.equal(reply.error, undefined);
  assert.equal(reply.status, 2);
  assert.equal(reply.stdout, '');
  assert.equal(reply.stderr, 'Name the workflow: pdd workflow run small-change 81 (or bug, feature). See pdd workflow list.\n');
  assert.equal(existsSync(effects), false, 'No external workflow or authentication command ran');
  assert.deepEqual(readdirSync(cwd), [], 'No workflow files were written in the project');
  assert.deepEqual(readdirSync(home), [], 'No workflow files were written in the home folder');
});
