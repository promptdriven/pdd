import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const skills = fileURLToPath(new URL('../skills', import.meta.url));

// Validate the bundle's small YAML subset without accepting ambiguous plain scalars.
// This is deliberately not a general YAML parser: other structures need explicit support.
function scalar(value) {
  assert.ok(value.length > 0);
  if (value.startsWith('"')) return JSON.parse(value);
  if (value.startsWith("'")) {
    assert.match(value, /^'(?:[^']|'')*'$/);
    return value.slice(1, -1).replaceAll("''", "'");
  }
  assert.doesNotMatch(value, /^[-?:,[\]{}#&*!|>"'%@`]/, 'plain YAML scalar starts with an indicator');
  assert.doesNotMatch(value, /:(?:\s|$)|\s#|[\t\r\n]/, 'plain YAML scalar contains a mapping, comment or control character');
  return value;
}

function frontmatter(text) {
  const match = /^---\n([\s\S]*?)\n---\n/.exec(text);
  assert.ok(match, 'missing YAML frontmatter');
  const result = {};
  let metadata = false;
  for (const line of match[1].split('\n')) {
    if (line.startsWith('  ')) {
      assert.ok(metadata);
      const field = /^  (pdd-skills): (.+)$/.exec(line);
      assert.ok(field, 'unsupported metadata field');
      assert.ok(!Object.hasOwn(result.metadata, field[1]), 'duplicate metadata key');
      result.metadata[field[1]] = scalar(field[2]);
    } else {
      const field = /^(name|description|metadata):(.*)$/.exec(line);
      assert.ok(field, 'unsupported frontmatter field');
      assert.ok(!Object.hasOwn(result, field[1]), 'duplicate frontmatter key');
      metadata = field[1] === 'metadata';
      if (metadata) { assert.equal(field[2], ''); result.metadata = {}; }
      else { assert.ok(field[2].startsWith(' ')); result[field[1]] = scalar(field[2].trim()); }
    }
  }
  assert.deepEqual(Object.keys(result).sort(), ['description', 'metadata', 'name']);
  assert.deepEqual(Object.keys(result.metadata), ['pdd-skills']);
  return result;
}

for (const entry of readdirSync(skills, { withFileTypes: true }).filter(entry => entry.isDirectory())) {
  test(`bundled skill frontmatter is valid YAML: ${entry.name}`, () => {
    const result = frontmatter(readFileSync(join(skills, entry.name, 'SKILL.md'), 'utf8'));
    assert.equal(result.name, entry.name);
    assert.equal(typeof result.description, 'string');
    assert.match(result.metadata['pdd-skills'], /^\d+\.\d+\.\d+$/);
  });
}

test('YAML scalar check rejects ambiguous plain values and preserves quoted words', () => {
  for (const value of ['repo: pick', 'Use Autopilot:', ...'-?:,[]{}#&*!|>%@`'.split('').map(char => `${char}value`)]) {
    assert.throws(() => scalar(value), { name: 'AssertionError' }, value);
  }
  for (const value of ['repo: pick', 'Use Autopilot:', 'a "quote"', "a person's skill"]) {
    assert.equal(scalar(JSON.stringify(value)), value);
    assert.equal(scalar(`'${value.replaceAll("'", "''")}'`), value);
  }
  assert.equal(scalar('Use Autopilot:ready'), 'Use Autopilot:ready');
});

for (const suffix of ['', ' ', '\t']) {
  test(`YAML frontmatter rejects a terminal mapping colon with suffix ${JSON.stringify(suffix)}`, () => {
    const header = `---\nname: pdd-autopilot\ndescription: Use Autopilot:${suffix}\nmetadata:\n  pdd-skills: 0.1.23\n---\n`;
    assert.throws(() => frontmatter(header), { name: 'AssertionError' });
  });
}
