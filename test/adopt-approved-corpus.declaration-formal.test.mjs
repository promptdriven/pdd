import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';

const {adoptReplayCorpus} = await import(process.env.PDD_ADOPTION_MODULE || '../src/workflow-replay.mjs');

// Story "Rules to check": an available snapshot with an empty or duplicate
// declaration is invalid before either inventory is considered. Otherwise both
// inventories must be nonempty, unique, and exactly the declared set. This is a
// finite supplied-snapshot check; it does not exercise native Git or hashing.
const alphabet = ['tests/a.json', 'tests/b.json', 'tests/c.json'];
const lists = [[]];
for (let length = 1; length <= 3; length++) {
  const extend = prefix => {
    if (prefix.length === length) { lists.push(prefix); return; }
    for (const path of alphabet) extend([...prefix, path]);
  };
  extend([]);
}
const uniqueNonempty = paths => paths.length > 0 && new Set(paths).size === paths.length;
const sameMembers = (left, right) => left.length === right.length && left.every(path => right.includes(path));
const rows = paths => paths.map(path => ({path, sha256:'1'.repeat(64), checks:['original']}));

test('2906 bounded declaration precedence: 40 declarations x 40 x 40 inventories', async () => {
  const counts = {'invalid-approval':0, 'inventory-mismatch':0, adopted:0};
  for (const scenarios of lists) for (const approved of lists) for (const current of lists) {
    const declaration = {
      schema_version:'pdd.replay-adoption.v1', repository:'example/project', commit:'a'.repeat(40),
      prompts:['prompts/main.prompt.md'], scenarios,
      approval:{kind:'external-human-assertion', reference:'review:finite', asserted_by:'Finite Reviewer'},
    };
    const context = [{path:'prompts/main.prompt.md', sha256:'2'.repeat(64)}];
    const snapshot = {
      available:true, repository:declaration.repository, commit:declaration.commit, declaration,
      declaration_sha256:'3'.repeat(64), approved_commit_ancestor:true, cause:'',
      approved_vectors:rows(approved), current_vectors:rows(current),
      approved_context:context, current_context:context,
    };
    const expected = !uniqueNonempty(scenarios) ? 'invalid-approval' :
      !uniqueNonempty(approved) || !uniqueNonempty(current) ||
      !sameMembers(scenarios, approved) || !sameMembers(scenarios, current) ? 'inventory-mismatch' : 'adopted';
    const label = JSON.stringify({scenarios, approved, current});
    let calls = 0;
    const result = await adoptReplayCorpus('/finite/repo', 'approved.json', {
      readAdoptionSnapshot:async () => { calls++; return {snapshot}; },
    });
    assert.equal(calls, 1, label);
    assert.equal(result.outcome, expected === 'adopted' ? 'adopted' : 'blocked', label);
    assert.equal(result.reason, expected === 'adopted' ? '' : expected, label);
    assert.deepEqual(result.paths, expected === 'adopted' ? [...scenarios].sort() : [], label);
    counts[expected]++;
  }
  assert.deepEqual(counts, {'invalid-approval':40000, 'inventory-mismatch':23757, adopted:243});
});
