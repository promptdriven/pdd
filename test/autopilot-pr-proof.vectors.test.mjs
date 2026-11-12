import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

// These narrative native cases name public core behaviors. Each mapped test builds
// its own real Git fixture and drives tickCore or coreStatus, rather than comparing prose.
const cases = JSON.parse(readFileSync(new URL('../fixtures/native-cases/autopilot-pr-proof.json', import.meta.url), 'utf8'));
const core = fileURLToPath(new URL('./autopilot-core.test.mjs', import.meta.url));
const formal = fileURLToPath(new URL('./autopilot-pr-proof.formal.test.mjs', import.meta.url));
const routes = {
  'initial-merge': [core, 'current head review records'],
  'not-applicable': [core, 'PR proof rejects'],
  'invalid-proof': [core, 'PR proof rejects'],
  'new-head': [core, 'D1 base refresh'],
  'behavioral-repair': [core, 'long suite failure|repair finding references'],
  'missing-regression': [formal, 'bounded proof gate'],
  'nonbehavioral-repair': [core, 'nonbehavioral repair reason'],
  'attention': [core, 'attention snapshot|R5 should-fix'],
  'authority': [core, 'N1b a strict repository'],
};
for (const entry of cases.cases) test(`native case ${entry.id}`, () => {
  assert.ok(routes[entry.id], `No native execution for ${entry.id}`);
  const [file, pattern] = routes[entry.id];
  const env = { ...process.env }; delete env.NODE_TEST_CONTEXT;
  const run = spawnSync(process.execPath, ['--test', `--test-name-pattern=${pattern}`, file], { encoding: 'utf8', timeout: 180000, env });
  assert.equal(run.status, 0, `${entry.id}: ${run.stdout}\n${run.stderr}`);
  assert.match(run.stdout, /# pass [1-9]/, `${entry.id} must execute at least one test`);
});
test('every native route is declared in the inventory', () => {
  assert.deepEqual(Object.keys(routes).sort(), cases.cases.map(c => c.id).sort());
});
