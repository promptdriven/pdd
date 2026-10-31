import test from 'node:test';
import assert from 'node:assert/strict';
const {adoptReplayCorpus} = await import(process.env.PDD_ADOPTION_MODULE || '../src/workflow-replay.mjs');

// Oracle: approved Story "Rules to check", AC1–AC5. Authorization can be
// reused only for a complete identical declared corpus/context and an explicit same-repo
// immutable approval. Hashes and identities below are symbolic snapshot facts;
// native Git enumeration, hashing and lifecycle are outside this finite proof.
const digest = digit => digit.repeat(64);
const vectors = [0, 1].map(i => ({path:`tests/${i}.json`, sha256:digest(String(i + 1)), checks:[`original-${i}`]}));
const context = [
  {path:'prompts/count.prompt.md', sha256:digest('3')},
  {path:'rules/count.md', sha256:digest('4')},
];
const declaration = {
  schema_version:'pdd.replay-adoption.v1', repository:'example/project', commit:'a'.repeat(40),
  prompts:['prompts/count.prompt.md'],scenarios:vectors.map(v=>v.path),
  approval:{kind:'external-human-assertion', reference:'review:finite', asserted_by:'Finite Reviewer'},
};

test('2640 bounded declared-corpus authorization: all 13824 finite snapshots', async () => {
  let visited = 0, accepted = 0;
  // Each original vector: absent, identical, changed raw-byte hash, changed check.
  // Each required context row: absent, identical, changed hash. One optional extra
  // vector, availability/repo/commit bits, and valid/missing/malformed approval.
  for (let v0=0; v0<4; v0++) for (let v1=0; v1<4; v1++)
  for (let extra=0; extra<2; extra++) for (let c0=0; c0<3; c0++) for (let c1=0; c1<3; c1++)
  for (let available=0; available<2; available++) for (let sameRepo=0; sameRepo<2; sameRepo++)
  for (let ancestor=0; ancestor<2; ancestor++)
  for (let sameCommit=0; sameCommit<2; sameCommit++) for (let approval=0; approval<3; approval++) {
    const d = structuredClone(declaration);
    if (approval===1) delete d.approval;
    if (approval===2) d.approval.kind='machine-assertion';
    const current_vectors = [v0,v1].flatMap((state,i) => {
      if (state===0) return [];
      const row=structuredClone(vectors[i]);
      if (state===2) row.sha256=digest('f');
      if (state===3) row.checks=[`changed-${i}`];
      return [row];
    });
    if (extra) current_vectors.push({path:'tests/extra.json',sha256:digest('5'),checks:['extra']});
    const current_context = [c0,c1].flatMap((state,i) => state===0 ? [] :
      [{...context[i],sha256:state===1 ? context[i].sha256 : digest('f')}]);
    const snapshot={available:!!available, repository:sameRepo ? declaration.repository : 'foreign/project',
      commit:sameCommit ? declaration.commit : 'b'.repeat(40), declaration:d,
      approved_vectors:structuredClone(vectors), current_vectors,
      approved_context:structuredClone(context), current_context, declaration_sha256:digest('9'),approved_commit_ancestor:!!ancestor,cause:''};
    // Independently derived conjunction; no private validator or normalization
    // helper supplies expected authorization or copies implementation output.
    const allowed=!!(available && ancestor && sameRepo && sameCommit && approval===0 &&
      v0===1 && v1===1 && !extra && c0===1 && c1===1);
    const label=JSON.stringify({v0,v1,extra,c0,c1,ancestor,available,sameRepo,sameCommit,approval});
    let calls=0;
    const result=await adoptReplayCorpus('/finite/repo','approved.json',{
      readAdoptionSnapshot:async () => {calls++; return {snapshot};},
    });
    assert.equal(calls,1,label);
    assert.equal(result.outcome,allowed ? 'adopted' : 'blocked',label);
    assert.deepEqual(result.paths,allowed ? vectors.map(v=>v.path) : [],label);
    assert.equal(result.provenance.trust,'external-assertion-unverified',label);
    if (allowed) {
      accepted++;
      assert.equal(result.provenance.repository,declaration.repository,label);
      assert.equal(result.provenance.commit,declaration.commit,label);
      assert.equal(result.provenance.reference,declaration.approval.reference,label);
      assert.equal(result.provenance.asserted_by,declaration.approval.asserted_by,label);
    }
    visited++;
  }
  assert.equal(visited,13824);
  assert.equal(accepted,1);
});
