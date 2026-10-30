import test from 'node:test';
import assert from 'node:assert/strict';
const {adoptReplayCorpus} = await import(process.env.PDD_ADOPTION_MODULE || '../src/workflow-replay.mjs');

// Independent oracle: user_stories/adopt-approved-corpus.md, Rules to check:
// every letter case of a .git segment is forbidden; an otherwise valid identical
// corpus can be adopted. This proof covers the supplied-snapshot public boundary.
function snapshot(field, path) {
  const declaration = {
    schema_version:'pdd.replay-adoption.v1', repository:'example/project', commit:'a'.repeat(40),
    prompts:[field === 'prompts' ? path : 'prompts/main.prompt.md'],
    scenarios:[field === 'scenarios' ? path : 'tests/main.json'],
    approval:{kind:'external-human-assertion', reference:'review:paths', asserted_by:'Formal Reviewer'},
  };
  const vectors = [{path:declaration.scenarios[0],sha256:'1'.repeat(64),checks:['original']}];
  const context = [{path:declaration.prompts[0],sha256:'2'.repeat(64)}];
  return {available:true,repository:declaration.repository,commit:declaration.commit,declaration,
    declaration_sha256:'3'.repeat(64),approved_commit_ancestor:true,cause:'',
    approved_vectors:structuredClone(vectors),current_vectors:structuredClone(vectors),
    approved_context:structuredClone(context),current_context:structuredClone(context)};
}
async function adopt(field,path) {
  let calls=0;
  const result=await adoptReplayCorpus('/finite/repo','approved.json',{
    readAdoptionSnapshot:async()=>{calls++;return {snapshot:snapshot(field,path)};},
  });
  assert.equal(calls,1);
  return result;
}

test('2640 bounded path refusal: all 8 .git cases x 2 depths x 2 declaration fields (32 states)',async()=>{
  let visited=0;
  for (const g of ['g','G']) for (const i of ['i','I']) for (const t of ['t','T'])
  for (const prefix of ['', 'nested/']) for (const field of ['prompts','scenarios']) {
    const path=`${prefix}.${g}${i}${t}/entry.json`, label=`${field}: ${path}`;
    const result=await adopt(field,path);
    assert.equal(result.outcome,'blocked',label);
    assert.equal(result.reason,'invalid-approval',label);
    assert.deepEqual(result.paths,[],label);
    assert.match(result.cause,/noncanonical/i,label);
    assert.ok(result.cause.includes(path),label);
    visited++;
  }
  assert.equal(visited,32);
});

test('2640 bounded path valid witnesses: 3 allowed segments x 2 depths x 2 declaration fields (12 states)',async()=>{
  let visited=0;
  for (const segment of ['.github','git','.gitkeep'])
  for (const prefix of ['', 'nested/']) for (const field of ['prompts','scenarios']) {
    const path=`${prefix}${segment}/entry.json`, result=await adopt(field,path);
    assert.equal(result.outcome,'adopted',`${field}: ${path}`);
    assert.deepEqual(result.paths,snapshot(field,path).declaration.scenarios);
    visited++;
  }
  assert.equal(visited,12);
});
