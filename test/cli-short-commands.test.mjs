import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { parseArgv } from '../src/argument-parser.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const id = '123e4567-e89b-42d3-a456-426614174000';
const id2 = '123e4567-e89b-42d3-a456-426614174001';
const capture = () => ({ text: '', write(value) { this.text += value; } });
const transport = Object.fromEntries(['runHerdrStage', 'inspectHerdrStage', 'attachHerdrStage', 'closeHerdrStage'].map(name => [name, () => assert.fail(`unexpected ${name}`)]));
const cwd = () => { const root = mkdtempSync(join(tmpdir(), 'pdd-short-')); mkdirSync(join(root, '.git')); return root; };
const records = entries => { entries.forEach((entry, index) => { entry.runDir ??= `/tmp/fake-run-${index}`; }); const fake = {
  readRunIndex: async ports => { fake.seen.push(ports); return { entries, dropped: 0 }; },
  readJournalLast: async runDir => ({ value: { state: entries.find(entry => entry.runDir === runDir)?.state ?? entries[0].state }, warnings: [] }),
  runStatusFromState: async state => ({ runId: state.runId, workflow: state.name, repo: state.repo, issue: state.issue,
    state: state.index === 1 ? 'waiting' : 'running', stage: { id: 'approve' }, steps: [] }),
  seen: [],
}; return fake; };

test('short command parser admits issue forms, prefixes, confirmation and status-all', () => {
  assert.equal(parseArgv(['workflow', 'approve']).local, 'workflow-approve');
  assert.equal(parseArgv(['workflow', 'approve', '#2', '--yes']).operands[0], '#2');
  assert.equal(parseArgv(['workflow', 'resume', '123e4567']).operands[0], '123e4567');
  assert.equal(parseArgv(['workflow', 'resume', id]).operands[0], id);
  assert.equal(parseArgv(['workflow', 'changes', 'owner/repo#2', 'please', 'retry']).operands.length, 3);
  assert.equal(parseArgv(['workflow', 'status', '--all']).options['--all'], true);
  assert.equal(parseArgv(['workflow', 'watch', 'https://github.com/owner/repo/issues/2']).local, 'workflow-watch');
});

test('short decisions use the shared person evidence and preserve the bound decision', async t => {
  const root = cwd(); t.after(() => rmSync(root, {recursive:true,force:true}));
  const entry = {runId:id,root,runDir:join(root,'.git','pdd','workflows',id),repo:'owner/repo',issue:{number:2,title:'Plan it'},state:{runId:id,name:'small-change',repo:'owner/repo',issue:{number:2,title:'Plan it'},index:1}};
  for (const mode of ['terminal','decline','non-tty','non-tty-yes','agent-missing','agent-verified']) {
    let admitted=0,question;
    const runner={readWorkflowDecision:async()=>({state:'ready',stage:'change',journalSeq:17}),
      async applyWorkflowDecision(input,ports) {
        assert.equal(input.runId,id);assert.equal(input.expectStage,'change');assert.equal(input.expectSeq,17);
        const auth=await ports.authorizeDecision({state:{...entry,waitingDecision:{at:200,evidenceStage:{agent:'codex',root,startedAt:100,endedAt:190}}}});
        if (!auth.ok) return {state:'refused',message:auth.message,exitCode:1};
        admitted++; return {state:'recorded',message:'Recorded.',exitCode:0,approvalRecord:auth.approvalRecord};
      }};
    const tty=mode==='terminal'||mode==='decline';
    const out=capture(),err={...capture(),isTTY:tty};
    const code=await runPdd(['workflow','approve','2',...(mode.endsWith('yes')?['--yes']:[])],{
      cwd:root,stdout:out,stderr:err,stdin:{isTTY:tty},env:mode.startsWith('agent')?{PDD_AGENT_SESSION:`${id}/scope`}:{},
      confirm:async q=>{question=q;return mode!=='decline';},workflowRecords:records([entry]),workflowRunner:runner,workflowStages:transport,
      readApprovalEvidence:async()=>mode==='agent-verified'?{ok:true,agent:'codex',sessionId:id,userMessage:'I approve',userMessageAt:250}:{ok:false,message:'No verified user message.'}});
    const yes=mode==='terminal'||mode==='agent-verified';
    assert.equal(code,yes?0:1,mode);assert.equal(admitted,yes?1:0,mode);
    if(tty) assert.match(question,/owner\/repo#2 "Plan it".*y\/N/);
  }
});

test('status --all refuses to guess when two repositories share an issue number', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-outside-')); t.after(() => rmSync(root, { recursive: true, force: true }));
  const entries = [
    { runId: id, repo: 'one/app', issue: { number: 45, title: 'One' }, state: { runId: id, name: 'small-change', repo: 'one/app', issue: { number: 45, title: 'One' }, index: 1 } },
    { runId: id2, repo: 'two/app', issue: { number: 45, title: 'Two' }, state: { runId: id2, name: 'small-change', repo: 'two/app', issue: { number: 45, title: 'Two' }, index: 1 } },
  ];
  const fake = records(entries), stderr = capture(), stdout = capture();
  assert.equal(await runPdd(['workflow', 'approve', '45'], { cwd: root, stdout, stderr, workflowRecords: fake, stdinIsTTY: true }), 2);
  assert.match(stderr.text, /one\/app#45 "One"/); assert.match(stderr.text, /two\/app#45 "Two"/);
  stdout.text = ''; stderr.text = '';
  assert.equal(await runPdd(['workflow', 'status', '--all'], { cwd: root, stdout, stderr, workflowRecords: fake }), 0);
  assert.match(stdout.text, /one\/app#45 "One"/); assert.match(stdout.text, /two\/app#45 "Two"/);
  assert.doesNotMatch(stdout.text, new RegExp(id)); assert.doesNotMatch(stdout.text, /resume [0-9a-f]{8}-/);
});
