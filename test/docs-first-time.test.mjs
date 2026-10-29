import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';

// The docs describe pdd as it is now, as if this were the first version. History goes only in the GitHub release notes.
// "New in" is case-sensitive, so that "a new install" or "new information" do not match.
const HISTORY = [/\bno longer\b/i, /\bused to\b/i, /\bwas renamed\b/i, /\bmoved to\b/i, /\bsince 0\.1/i, /\bNew in\b/, /\(new\)/i,
  /There is no `pdd session`/i];
const root = new URL('../', import.meta.url);
const docs = ['README.md', 'AGENTS.md',
  ...readdirSync(new URL('docs/', root)).filter(name => name.endsWith('.md') && name !== 'prompting-guide.md').map(name => `docs/${name}`)];

// Wrong: a doc says what changed ("no longer", "since 0.1.4", "(new)") instead of only how pdd works today.
test('README, AGENTS and docs contain no history or change notes', () => {
  const found = docs.flatMap(path => readFileSync(new URL(path, root), 'utf8').split('\n')
    .flatMap((line, index) => HISTORY.filter(pattern => pattern.test(line))
      .map(pattern => `${path}:${index + 1}: "${line.match(pattern)[0]}"`)));
  assert.deepEqual(found, [], `Describe only how pdd works now:\n${found.join('\n')}`);
});
