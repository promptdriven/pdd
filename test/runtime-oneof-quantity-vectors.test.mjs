import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { checkInput, numberWarnings } from '../src/runtime-preflight.mjs';
import { harbor, root } from './runtime-fake.mjs';

// Independent bounded oracle: overlap means starts with a and ends with b.
// All strings over {a,b} of length 0..4, including recursive field/item use.
test('ONEOF2500 bounded oracle: overlap iff both complete languages contain the value', () => {
  const variants = [{ type: 'string', pattern: '^a[ab]*$' }, { type: 'string', pattern: '^[ab]*b$' }];
  for (let length = 0; length <= 4; length++) for (let bits = 0; bits < 2 ** length; bits++) {
    const value = Array.from({ length }, (_, i) => bits & (1 << i) ? 'b' : 'a').join('');
    const expected = value.startsWith('a') && value.endsWith('b');
    const result = checkInput({ entries: [value] }, { type: 'object', properties: {
      entries: { type: 'array', items: { oneOf: variants } },
    }, required: ['entries'], additionalProperties: false }, 0);
    assert.equal(result.refusals.some(row => /more than one/.test(row.message)), expected, JSON.stringify(value));
  }
});

test('NUMERIC2500 bounded oracle: move numbers cannot mask a differing nearby score', () => {
  for (let score = 25; score <= 35; score++) for (let moves = 25; moves <= 35; moves++) {
    const result = numberWarnings({ criteria: [{ id: 'AC1', text: `After ${moves} moves, the score is 30.` }],
      steps: [{ checks: [{ criterion_id: 'AC1', target: 'result', path: '/score', op: 'equals', value: score }] }] });
    const expected = score !== 30 && Math.abs(score - 30) <= 0.1 * Math.max(score, 30);
    assert.equal(result.length, Number(expected), `${score} score, ${moves} moves`);
  }
});

test('ONEOF2500 CLI: check accepts exclusive patterns and refuses concrete overlap', t => {
  const { repo, home } = harbor(t), path = join(repo, 'prompts/place_order.prompt.md');
  const tools = join(home, 'bin'); mkdirSync(tools);
  writeFileSync(join(tools, 'gh'), '#!/bin/sh\nexit 1\n'); chmodSync(join(tools, 'gh'), 0o755);
  const original = readFileSync(path, 'utf8');
  const block = /```json\n([\s\S]*?)\n```/.exec(original);
  const contract = JSON.parse(block[1]);
  const schema = { oneOf: [{ type: 'string', pattern: '^Sam$' }, { type: 'string', pattern: '^Alex$' }] };
  contract.entries[0].input_schema.properties.customerName = schema;
  const run = () => {
    writeFileSync(path, original.replace(block[1], JSON.stringify(contract, null, 2)));
    return spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'test', 'user_stories/place-order.md', '--json'], {
      cwd: repo, encoding: 'utf8', env: { ...process.env, HOME: home, PATH: `${tools}:${process.env.PATH}`, PDD_RUNTIME_URL: 'http://127.0.0.1:9' },
    });
  };
  const exclusive = run();
  // Reaching the credential boundary proves local preflight accepted the input;
  // no credential or live Runtime call is needed for this CLI regression.
  assert.equal(exclusive.status, 5, exclusive.stdout + exclusive.stderr);
  assert.match(exclusive.stderr, /gh auth login/);
  assert.doesNotMatch(exclusive.stdout + exclusive.stderr, /more than one|does not match the pattern/);
  schema.oneOf[1].pattern = '^S';
  const overlap = run();
  assert.equal(overlap.status, 4, overlap.stdout + overlap.stderr);
  assert.match(overlap.stdout + overlap.stderr, /more than one/);
});
