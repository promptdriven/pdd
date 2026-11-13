import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { root } from './runtime-fake.mjs';

test('no runtime source line names pdd check or pdd try', () => {
  const files = readdirSync(join(root, 'src/runtime')).filter(file => file.endsWith('.mjs')).map(file => join('src/runtime', file));
  assert.ok(files.length >= 25, `expected full src/runtime scan, got ${files.length}`);
  const found = [];
  for (const file of files) {
    readFileSync(join(root, file), 'utf8').split('\n').forEach((text, index) => {
      if (!text.trim().startsWith('//') && /\bpdd (?:check|try)\b/.test(text)) found.push(`${file}:${index + 1}: ${text.trim().slice(0, 120)}`);
    });
  }
  assert.deepEqual(found, []);
});
