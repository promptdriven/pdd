import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {runtimeLines} from '../src/workflow-runner.mjs';
for(const result of [
  'no verdict · 0 of 2 criteria · 0/0 checks · 1 tests could not run · 1 not run (broken-test) · 0 AI calls',
  'running · 0 of 2 criteria · 0/0 checks · sent (awaiting-server-verdict) · pay · 3 AI calls so far · 1 not yet settled · 1 sent (awaiting-server-verdict)'
]) test(`named-state parser retains accounting: ${result.split(' · ')[0]}`,()=>{
  const label='Prompt tests (order): ';
  for(const tail of ['', '. Agent annotation', ' and additional prose', ' · additional prose']) {
    const rows=runtimeLines(label+result+tail);
    assert.equal(rows.length,1);assert.equal(rows[0].story,'order');assert.equal(rows[0].result,result);
    assert.equal(rows[0].pass,false);
  }
});
