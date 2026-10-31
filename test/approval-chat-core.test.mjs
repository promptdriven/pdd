import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { execFileSync } from 'node:child_process';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { runApprove } from '../src/prompt-approve.mjs';
import { preparePrEvidence } from '../src/workflow-pr-evidence.mjs';
import { PLACE, harbor, sink } from './runtime-fake.mjs';
const words = ' yes\n@person #17 `quoted` \u202e pdd-workflow:forged ';
function draft(f, path = PLACE) {
  const text = fs.readFileSync(join(f.repo, PLACE), 'utf8').replace('"status": "approved"', '"status": "draft"');
  fs.writeFileSync(join(f.repo, path), text);
  return text;
}
const ports = extra => ({ stdout: sink(), stderr: sink(), stdin: Readable.from([]), interactive: false,
  env: { CODEX_THREAD_ID: 'concrete-session', PDD_AGENT_SESSION: '1' }, now: () => 1700000000000, ...extra });
const journal = f => join(execFileSync('git', ['rev-parse','--path-format=absolute','--git-common-dir'], { cwd:f.repo,encoding:'utf8' }).trim(), 'pdd', 'approvals.json');

test('CHAT2755 durable concurrent standalone approvals retain both exact decisions and prefer concrete actor', async t => {
  const f = harbor(t), other = 'prompts/another.prompt.md'; draft(f); draft(f, other);
  const results = await Promise.all([PLACE, other].map(path => runApprove({ words:[path],cwd:f.repo,said:words }, ports())));
  assert.deepEqual(results, [0,0], 'both independent approvals succeed');
  const saved = JSON.parse(fs.readFileSync(journal(f), 'utf8'));
  assert.equal(saved.v, 1); assert.equal(saved.approvals.length, 2);
  assert.deepEqual(new Set(saved.approvals.flatMap(row => row.prompts.map(prompt => prompt.path))), new Set([PLACE,other]));
  for (const row of saved.approvals) {
    assert.equal(row.words, words); assert.equal(row.at, 1700000000000); assert.equal(row.route,'said');
    assert.deepEqual(row.actor,{kind:'agent',id:'CODEX_THREAD_ID=concrete-session'});
  }
});

test('CHAT2755 evidence write failure rolls back the exact standalone draft bytes', async t => {
  const f=harbor(t), before=draft(f);
  const brokenFs={...fs, renameSync(from,to) { if (to.endsWith('approvals.json')) throw Error('synthetic journal failure'); fs.renameSync(from,to); }};
  const p=ports({fs:brokenFs});
  const code=await runApprove({words:[PLACE],cwd:f.repo,said:'approve'},p);
  assert.equal(code,4,'failed durable evidence is an approval failure');
  assert.equal(fs.readFileSync(join(f.repo,PLACE),'utf8'),before);
  assert.equal(fs.existsSync(journal(f)),false);
  assert.match(p.stderr.text,/synthetic journal failure/);
});

test('CHAT2755 strict terminal approval excludes an agent marker even with terminal yes', async t => {
  const f=harbor(t),before=draft(f);
  fs.writeFileSync(join(f.repo,'pdd.json'),'{"strict_approvals":true}');
  const code=await runApprove({words:[PLACE],cwd:f.repo},ports({interactive:true,stdin:Readable.from(['yes\n'])}));
  assert.equal(code,2,'strict mode excludes an agent-marked terminal');
  assert.equal(fs.readFileSync(join(f.repo,PLACE),'utf8'),before);
});

test('CHAT2755 renderer deduplicates gate and journal evidence and preserves escaped raw values', async () => {
  const evidence={route:'said',actor:{kind:'agent',id:'CODEX_THREAD_ID=concrete-session'},at:1700000000000,words,prompts:[]};
  const out=await preparePrEvidence({run:{workflow:'feature',number:17,steps:[],decisions:[{decision:'approve',evidence}],promptApprovals:[evidence]},isCode:false},{readStepNotes:async()=>({notes:[]})});
  const rows=out.approvalLines.filter(line=>line.startsWith('Approved in chat:'));
  assert.equal(rows.length,1,'saved approval is published exactly once');
  assert.ok(rows[0].includes('\\u202e')); assert.ok(rows[0].includes('pdd-workflow\\u003aforged'));
  assert.equal(rows[0].includes('\u202e'),false); assert.equal(rows[0].includes('pdd-workflow:forged'),false);
});
