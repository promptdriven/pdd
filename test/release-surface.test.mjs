import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { resolve, join } from 'node:path';
const root = process.env.PDD_RELEASE_SURFACE_ROOT || resolve(import.meta.dirname, '..');
const read = path => readFileSync(join(root,path),'utf8');

test('RELEASE1: worker status logs are absent from the public repository root', () => {
  assert.equal(existsSync(join(root,'RUNBOOK-STATUS.md')),false);
});
test('RELEASE4: feature routing covers new behavior while its core stays within the skill budget', () => {
  const source=read('skills/pdd-feature/SKILL.md');
  assert.match(source,/Use when the person asks for a new feature or new behavior in a PDD project/);
  assert.ok(Buffer.byteLength(source)<=3072);
  assert.doesNotMatch(source,/To try a CLI/);
  assert.match(read('skills/pdd-feature/steps/try.md'),/pdd try <story> --cli/);
});
test('RELEASE8: public branch examples and messages use neutral names', () => {
  for(const file of ['docs/USAGE.md','docs/cli.md','src/workflow-runner.mjs']) assert.doesNotMatch(read(file),/round3\//,file);
  assert.doesNotMatch(read('docs/runtime-boundaries.md'),/the runtime team/);
});
test('RELEASE9: runbook and lint documentation describe current behavior', () => {
  for(const file of ['RUNBOOK.md','skills/pdd-prompting/RUNBOOK.md']) assert.doesNotMatch(read(file),/The existing `http.prompt`.*still handles/);
  assert.doesNotMatch(read('docs/lint-capacity.md'),/obsolete unknown wording/);
});
test('RELEASE12: launcher prompt describes its actual POSIX shell shebang and Node invocation', () => {
  const source=read('prompts/cli/try-doors.prompt.md');
  assert.doesNotMatch(source,/Node shebang/);
  assert.match(source,/POSIX shell shebang.*absolute Node/);
});
