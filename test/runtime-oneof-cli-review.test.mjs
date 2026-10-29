import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawn } from 'node:child_process';
import { fakeRuntime, harbor, root } from './runtime-fake.mjs';

test('ONEOF2500 independent CLI replay: original addresses, overlap and numeric quantities', async t => {
  const runtime = await fakeRuntime(t, entry => runtime.normal(entry));

  const { repo, home } = harbor(t), tools = join(home, 'bin');
  mkdirSync(tools); writeFileSync(join(tools, 'gh'), '#!/bin/sh\nif [ \"$1\" = auth ]; then echo fake_test_token; else echo \"octo 4242\"; fi\n'); chmodSync(join(tools, 'gh'), 0o755);
  const promptPath = join(repo, 'prompts/place_order.prompt.md');
  const prompt = readFileSync(promptPath, 'utf8');
  const block = /```json\n([\s\S]*?)\n```/.exec(prompt), contract = JSON.parse(block[1]);
  const testPath = join(repo, 'tests/place-order.json'), doc = JSON.parse(readFileSync(testPath, 'utf8'));
  const run = async () => {
    writeFileSync(promptPath, prompt.replace(block[1], JSON.stringify(contract, null, 2)));
    writeFileSync(testPath, JSON.stringify(doc, null, 2));
    return await new Promise(resolve => {
      const child = spawn(process.execPath, [join(root, 'bin/pdd.mjs'), 'check', 'user_stories/place-order.md'], {
        cwd: repo, env: { ...process.env, HOME: home, PATH: `${tools}:${process.env.PATH}`, PDD_RUNTIME_URL: runtime.origin },
      });
      let stdout = '', stderr = '';
      child.stdout.on('data', bytes => { stdout += bytes; }); child.stderr.on('data', bytes => { stderr += bytes; });
      t.after(() => child.kill());
      child.on('close', status => resolve({ status, stdout, stderr }));
    });
  };
  const schema = { oneOf: [
    { type: 'string', pattern: '^ws://127\\.0\\.0\\.1:[1-9][0-9]{0,3}/?$' },
    { type: 'string', pattern: '^unix://[^\\s]+$' },
    { type: 'string', pattern: '^[^\\s:]+$' },
  ] };
  contract.entries[0].input_schema.properties.customerName = schema;
  for (const address of ['ws://127.0.0.1:8080', 'unix:///tmp/app.sock', 'app']) {
    doc.steps[0].input.customerName = address;
    const result = await run(), output = result.stdout + result.stderr;
    assert.equal(result.status, 0, output);
    assert.doesNotMatch(output, /more than one|does not match the pattern/);
  }
  schema.oneOf = [{ type: 'string', pattern: '^app$' }, { type: 'string', pattern: '^a' }];
  const overlap = await run(); assert.equal(overlap.status, 4, overlap.stdout + overlap.stderr);
  assert.match(overlap.stdout + overlap.stderr, /more than one/);
  contract.entries[0].input_schema.properties.customerName = { type: 'string' };
  const storyPath = join(repo, 'user_stories/place-order.md'), story = readFileSync(storyPath, 'utf8');
  const oldText = doc.criteria[1].text;
  const check = doc.steps[0].checks.find(row => row.criterion_id === 'AC2');
  check.path = '/score'; check.value = 28;
  for (const [text, warns] of [
    ['Starting from seed 42, I can play the fixed 30 moves and get the established replay result.', false],
    ['After 28 moves, the score is 30.', true],
  ]) {
    doc.criteria[1].text = text; writeFileSync(storyPath, story.replace(oldText, text));
    const result = await run(), output = result.stdout + result.stderr;
    assert.equal(result.status, 0, output);
    assert.equal(/possible numeric mismatch/.test(output), warns, output);
    if (warns) assert.match(output, /score.*28.*AC2.*30/);
  }
});
