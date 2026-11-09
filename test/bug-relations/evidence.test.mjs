import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { applyReproducedBugRelations } from '../../src/issue-dependencies-github.mjs';

const plan = JSON.parse(await readFile(new URL('./bug-relation-evidence-cases.json',import.meta.url)));
const input = {repository:'owner/repo',issue:1,relations:[{issue:2,classification:'related',quote:'exact text',source:{kind:'issue',repository:'owner/repo',issue:2,revision:'r1'},effect:{kind:'none'}}]};
const ports = text => ({github:{}, evidence:{read:async () => ({json:JSON.stringify({requirements:[{key:'https://github.com/owner/repo/issues/2',revision:'r1',text,authority:'trusted'}]})})}});
test('native evidence plan: exact trusted quote and changed text',async () => {
  assert.ok(plan.cases.some(x => x.id === 'matching'));
  assert.deepEqual((await applyReproducedBugRelations(input,ports('the exact text here'))).outcomes,[{index:0,status:'none',reason:''}]);
  assert.equal((await applyReproducedBugRelations(input,ports('different'))).outcomes[0].status,'held');
});
test('native evidence plan: invalid locator is rejected before reads',async () => {
  const value = structuredClone(input); value.relations[0].source = {kind:'code',repository:'owner/repo',path:'../secret',revision:'r1'};
  await assert.rejects(applyReproducedBugRelations(value,ports('exact text')),/invalid-input/);
});
