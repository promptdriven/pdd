import assert from 'node:assert/strict';
import test from 'node:test';
import {readFileSync,writeFileSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {recordEvidence,storyCount} from '../src/workflow-runner.mjs';
import {evidenceFixture,assertProtected,selection} from './helpers/workspace-evidence-fixture.mjs';

// Oracle: approved Story import-authorized-workspace-evidence, Rules to check.
// Permission and complete stage-source equality are independent requirements.
// Every member of this finite Cartesian product calls the real public import.
const layouts=['clone','nested'];
const stages=['current','pr1'];
const custody=['owned','absent','receipt-claim','foreign-run','foreign-owner','foreign-producer'];
const sources=['equal','changed-story','changed-dependency','missing-dependency','extra-selection'];
const permitted=(authority,source)=>authority==='owned' && source==='equal';

test('2899 formal: owned authority and exact stage source are jointly necessary over 120 combinations',async t=>{
  let checked=0,accepted=0,refused=0;
  for(const layout of layouts)for(const stage of stages) {
    const f=await evidenceFixture(t),producer=f[layout];
    const original=f.receipt(producer),extra=f.receipt(producer,[...selection,'tests/unknown-item.json']);
    if(stage==='pr1')f.pr1();
    const registration=await f.register(producer,stage);
    if(stage==='pr1')f.enterCode();
    const baseline=f.read(),anchor=registration.sourceAnchor.root;
    const story=join(anchor,'user_stories/place-order.md'),dependency=join(anchor,'docs/menu.md');
    const storyBytes=readFileSync(story),dependencyBytes=readFileSync(dependency);
    const head=f.git(f.root,'rev-parse','HEAD');
    for(const authority of custody)for(const source of sources) {
      const label=`${layout}/${stage}/${authority}/${source}`;
      writeFileSync(story,storyBytes);writeFileSync(dependency,dependencyBytes);
      const run=structuredClone(baseline);
      if(authority==='absent'||authority==='receipt-claim')delete run.evidenceAssociations;
      if(authority==='foreign-run')run.evidenceAssociations[0].runId='another-run';
      if(authority==='foreign-owner')run.evidenceAssociations[0].repo='another-owner/project';
      if(authority==='foreign-producer')run.evidenceAssociations[0].workspaceRoot=f.other;
      f.save(run);
      if(source==='changed-story')writeFileSync(story,Buffer.concat([storyBytes,Buffer.from('\n')]));
      if(source==='changed-dependency')writeFileSync(dependency,Buffer.concat([dependencyBytes,Buffer.from('\n')]));
      if(source==='missing-dependency')rmSync(dependency);
      const saved=source==='extra-selection'?extra:original;
      const receipt=structuredClone(saved.doc);
      // An otherwise valid registration copied into a receipt has no custody.
      if(authority==='receipt-claim')receipt.evidenceAssociations=[structuredClone(registration)];
      const bytes=JSON.stringify(receipt,null,2)+'\n';writeFileSync(saved.file,bytes);
      const before=readFileSync(f.status,'utf8'),gitStatus=f.git(f.root,'status','--porcelain');
      const result=await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports);
      const allowed=permitted(authority,source);
      assert.equal(result.exitCode,allowed?0:1,`2899 formal permission/source oracle ${label}: ${result.message}`);
      assert.equal(readFileSync(saved.file,'utf8'),bytes,`${label}: original receipt bytes`);
      assert.equal(f.git(f.root,'rev-parse','HEAD'),head,`${label}: Git head`);
      assert.equal(f.git(f.root,'status','--porcelain'),gitStatus,`${label}: Git worktree`);
      if(allowed) {
        const after=f.read(),evidence=after.evidence.at(-1);
        assertProtected(run,after);
        assert.deepEqual(after.evidenceAssociations,run.evidenceAssociations,`${label}: custody unchanged`);
        assert.deepEqual(evidence.receipt,receipt,`${label}: complete original provenance`);
        assert.equal(evidence.association.stage,stage,`${label}: stage retained`);
        assert.equal(evidence.source.sha256,receipt.source_sha256,`${label}: source retained`);
        assert.equal(storyCount(after).pass,stage==='current'?1:0,`${label}: current-code eligibility`);
        if(stage==='pr1')assert.equal(storyCount(after,{stage:'pr1'}).pass,1,`${label}: frozen PR 1 eligibility`);
        accepted++;
      } else {
        assert.equal(readFileSync(f.status,'utf8'),before,`${label}: refusal saves nothing`);
        refused++;
      }
      checked++;
    }
  }
  assert.deepEqual({checked,accepted,refused},{checked:120,accepted:4,refused:116});
  t.diagnostic('2899 formal bounded: 120 combinations; 4 accepted; 116 refused; receipt/state/stage invariants checked.');
});
