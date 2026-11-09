import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { applyReproducedBugRelations } from '../../src/issue-dependencies-github.mjs';
const plan = JSON.parse(await readFile(new URL('./bug-relation-links-cases.json',import.meta.url)));
const key = n => `https://github.com/owner/repo/issues/${n}`;
const relation = effect => ({issue:2,classification:'duplicate',quote:'quote',source:{kind:'issue',repository:'owner/repo',issue:2,revision:'v'},effect});
const make = () => {
  let writes = 0, state = null;
  const github = {issue:async ({issue}) => ({json:JSON.stringify({id:issue,html_url:key(issue),state:'open'})}),duplicateActor:async () => 'writer',duplicateTimeline:async () => [],markDuplicate:async () => { writes++; throw Error('lost response'); }};
  return {ports:{github,evidence:{read:async () => ({json:JSON.stringify({requirements:[{key:key(2),revision:'v',text:'quote',authority:'trusted'}]})})},owners:{read:async () => ({json:JSON.stringify({localOwner:'owner',claims:[{issue:key(1),active:true,owner:'owner',coordinatorId:'owner',machine:'machine',commentId:'1',labelEventId:'2'}]})})},relationClaim:{coordinatorId:'owner',machine:'machine',commentId:'1',labelEventId:'2'},clock:{now:async () => ({iso:'2026-01-01T00:00:00Z'})},settings:{read:async () => ({mode:'auto'})},checkpoint:{read:async () => state,write:async x => {state=x;}}}, writes:() => writes};
};
test('native links plan: unknown duplicate dispatch is never resent',async () => {
  assert.ok(plan.cases.some(x => x.id === 'unknown-post'));
  const f=make(), input={repository:'owner/repo',issue:1,relations:[relation({kind:'duplicate',duplicate:1,canonical:2})]};
  assert.equal((await applyReproducedBugRelations(input,f.ports)).outcomes[0].status,'unknown');
  assert.equal((await applyReproducedBugRelations(input,f.ports)).outcomes[0].status,'unknown');
  assert.equal(f.writes(),1);
});
test('native links plan: unrelated endpoint is held',async () => {
  const f=make(), input={repository:'owner/repo',issue:1,relations:[relation({kind:'duplicate',duplicate:1,canonical:9})]};
  assert.equal((await applyReproducedBugRelations(input,f.ports)).outcomes[0].status,'held');
  assert.equal(f.writes(),0);
});
