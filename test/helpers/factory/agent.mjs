// Generated from prompts/test/autopilot-factory.prompt.md.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {sourceFingerprint} from '../../../src/workflow-replay.mjs';
import {put,readJson,scenario,valuePrompt,sha,packageRoot} from './world.mjs';

const nativeCommand='node --test test/value.test.mjs';
const nativeTest=`import test from 'node:test';
import assert from 'node:assert/strict';
import {value} from '../value.mjs';
test('value follows the issue',()=>assert.equal(process.env.FACTORY_MUTANT?value+1:value,2,'FACTORY_VALUE'));
`;
export function scriptedAgent(w) {
  const a={steps:[],briefs:[],suites:[],checks:[]};
  a.prepare=async()=>{
    const {root,runDir}=w.record();
    if(!w.codeOnly)put(root,'value.prompt.md',valuePrompt(2));
    put(root,'user_stories/value.md','As a user, I want the value to be two, so that the result follows my request.\n\n## Acceptance criteria\n\n1. The value is 2.\n');
    put(root,'tests/value.json',scenario);
    put(root,'test/value.test.mjs',nativeTest);
    if(!w.omitDraftReview){
      const reviewLine=w.draftReviewMustFix?`Review: ${w.draftReviewMustFix} must-fix\n`:'Review: no must-fix\n';
      const contractLine=w.contractQuestion?`Contract change question: ${w.contractQuestion}\n`:'';
      put(runDir,w.workflow==='small-change'?'plan-review.md':'story-review.md',reviewLine+contractLine);
    }
    await w.command(['test','--fill-hash'],{cwd:root});
  };
  a.native=(mutant=false)=>{
    const r=spawnSync(process.execPath,['--test','test/value.test.mjs'],{cwd:w.record().root,env:{...w.env,...(mutant?{FACTORY_MUTANT:'1'}:{})},encoding:'utf8',timeout:10000});
    return {code:r.status,output:r.stdout+r.stderr};
  };
  a.evidence=()=>{
    const run=w.record(),path='tests/value.json',bytes=readFileSync(join(run.root,path)),doc=JSON.parse(bytes),step=doc.steps[0],check=step.checks[0];
    const good=a.native(),control=a.native(true);assert.equal(good.code,0,good.output);assert.equal(control.code,1,control.output);assert.match(control.output,/ERR_ASSERTION/);
    const identity={vector:path,step_id:step.step_id,entry_path:step.entry_path,operation:step.operation};
    put(run.runDir,'replay-evidence.json',{schema_version:'pdd.replay-evidence.v1',run_id:run.runId,source:{kind:'git-content-v1',sha256:sourceFingerprint(run.root)},vectors:[{path,sha256:sha(bytes)}],
      checks:[{...identity,check_index:0,criterion_id:check.criterion_id,target:check.target,path:check.path,op:check.op,outcome:'pass'}],
      operations:[{...identity,executed:true,outcome:'returned',boundary:{kind:'function',name:'value'},command:nativeCommand,exit_code:good.code}],
      counts:{total:1,pass:1,fail:0,blocked:0,not_replayed:0},mutation:{kind:'semantic',description:'Add one to the public value',command:'FACTORY_MUTANT=1 '+nativeCommand,exit_code:control.code,outcome:'assertion_failure',failed_checks:[{vector:path,step_id:step.step_id,check_index:0}]},
      formal:{result:'not_applicable',scope:'Constant value',reason:'No separate Rules to check in this synthetic Story',control_outcome:'not_run'}});
  };
  a.gate=async()=>{
    const run=w.record();assert.ok(run.gate);
    // Synthetic operator setup/start is the authorization. No real prompt is approved.
    const words=`The factory operator started Autopilot in auto mode for example/project. This covers the ordinary ${run.gate.kind} gate for issue 17 and automatic merge under the bundled rules.`;
    await w.command(['workflow','approve',String(w.record().number),'--said','-'],{cwd:run.root,actor:'coordinator',stdin:words});
  };
  a.step=async({allowFailure=false}={})=>{
    await w.command(['workflow','status',String(w.record().number)]);
    const run=w.record(),area=run.areas[run.area];
    if(run.gate){await a.gate();return;}
    const step=area.steps.find(s=>!run.done[s]);assert.ok(step,`no step at ${area.name}`);
    const brief=readFileSync(join(run.skillDir,'steps',step+'.md'),'utf8');assert.ok(brief.trim());
    a.briefs.push({area:area.name,step,sha256:sha(brief)});
    if(['scope','prompt-story'].includes(step))await a.prepare();
    if(['change','build'].includes(step))put(run.root,'value.mjs','export const value = 2;\n');
    if(step==='check') {
      const r=await w.command(['test','value','--cache-clear','--json'],{cwd:run.root,allowFailure:true});a.checks.push(r);
      if(r.code!==0)return {check:r};
    }
    if(step==='verify') {
      if(w.git(run.root,'status','--porcelain')){w.git(run.root,'add','.');w.git(run.root,'commit','-qm','Factory implementation and native checks');}
      const result=await w.command(['workflow','suite','--command',nativeCommand],{cwd:run.root});a.suites.push(result);
      await w.command(['workflow','prove',String(w.record().number),'--test',nativeCommand,'--expect','FACTORY_VALUE'],{cwd:run.root});
      const proof=readJson(join(run.runDir,'old-code-proof.json'));assert.equal(proof.outcome,'proved');assert.equal(proof.base.exitCode,1);assert.equal(proof.head.exitCode,0);
      if(area.replay_evidence)a.evidence();
    }
    // Recompute after formal/review in case a step committed source.
    if(step==='review' && !w.omitCodeReview)put(run.runDir,'review.md',w.codeReviewMustFix?`Review: ${w.codeReviewMustFix} must-fix\n`:'Review: no must-fix\n');
    if(['formal','review'].includes(step) && area.replay_evidence)a.evidence();
    const verdict=w.codeOnly?'Verdict: the prompt is right; the bug is only in the CODE.':'Verdict: the bug is in the PROMPT (its check fails on the issue case).';
    const details=w.codeOnly?'Prompt unchanged; passing on old and new snapshots. Native old code fails the value assertion; corrected code passes.':'Prompt correction: old fails; new passes.';
    const argv=['workflow','done',step,'--summary',`${step==='reproduce'?verdict+'\n':''}${w.codeOnly?'This PR: '+details+'\nFix: Keep the prompt unchanged; correct the native value.\n':''}Factory ${step}; ${step==='check'?'Prompt tests: 1 of 1 pass':'native evidence retained'}\nResult: ${details}`];
    if(area.optional.includes(step))argv.push('--skipped','Autopilot optional default');
    const done=await w.command(argv,{cwd:run.root,actor:'worker',allowFailure});a.steps.push(step);
    if(done.code!==0)return {step,refused:done};
    return {step};
  };
  a.until=async predicate=>{
    for(let n=0;n<30;n++) {if(predicate(w.record()))return;const result=await a.step();if(result?.check)return result;}
    assert.fail(`GAP progress: ${JSON.stringify({state:w.record().state,area:w.record().area,gate:w.record().gate,done:Object.keys(w.record().done)})}`);
  };
  a.finish=()=>a.until(run=>run.state==='waiting' && run.pr?.length===(w.workflow==='small-change'?1:2) && !run.gate);
  a.merge=async()=>{
    // There is no production merge function: these are the pdd-check/pdd-merge actor duties.
    for(const skill of ['pdd-check','pdd-merge'])assert.ok(readFileSync(join(packageRoot,'skills',skill,'SKILL.md'),'utf8').length);
    const config=readJson(join(w.cwd,'pdd.json')),state=w.state(),owned=w.github.issues.get(17);
    assert.equal(config.autopilot.mode,'auto');assert.ok(!config.strict_approvals);
    assert.equal(state.startAction?.command,'pdd autopilot start','merge needs the actual operator action');
    assert.ok([w.github.owner,...(config.autopilot.trust??[])].includes(owned.user),'issue author must be trusted');
    assert.equal(w.record().automaticOrigin.coordinatorId,state.coordinatorId);
    const codePr=w.github.prs.find(pr=>w.record().pr.some(p=>p.number===pr.number&&p.stage==='code'));
    let pairedNative;
    if(codePr){
      w.git(w.mergeCheckout,'fetch','-q','origin');w.git(w.mergeCheckout,'switch','-q','-C','factory-paired-check',`origin/${codePr.headRefName}`);
      pairedNative=spawnSync(process.execPath,['--test','test/value.test.mjs'],{cwd:w.mergeCheckout,env:w.env,encoding:'utf8'});
      assert.equal(pairedNative.status,0,pairedNative.stdout+pairedNative.stderr);
    }
    for(const saved of w.record().pr) {
      const pr=w.github.prs.find(pr=>pr.number===saved.number);
      if(pr.state==='MERGED')continue;
      if(pr.baseRefName!==w.record().baseBranch)await w.github.gh(['pr','edit',String(pr.number),'--base',w.record().baseBranch]);
      // A separate native checkout checks the published head, independent of worker memory.
      w.git(w.mergeCheckout,'fetch','-q','origin');w.git(w.mergeCheckout,'switch','-q','-C','factory-check',`origin/${pr.headRefName}`);
      const r=spawnSync(process.execPath,['--test','test/value.test.mjs'],{cwd:w.mergeCheckout,env:w.env,encoding:'utf8'});
      let promptResult=null,oldPromptResult=null,oldNative=null,oldPrompt=null,newPrompt=null;
      // Read native Story-step records, independently of worker options and editable PR prose.
      const storyVerdicts=w.record().areas[0].steps.flatMap(step=>[...String(w.record().done[step]?.summary??'').matchAll(/^Verdict: (.+)$/gm)].map(m=>m[1]));
      assert.ok(new Set(storyVerdicts).size<=1,'conflicting recorded Story verdicts');
      const codeOnly=w.workflow==='bug' && storyVerdicts[0]==='the prompt is right; the bug is only in the CODE.';
      if(saved.stage==='prompt-pr' && w.workflow==='bug') {
        const bodyCodeOnly=/the prompt is right; the bug is only in the CODE/.test(pr.body);
        assert.equal(bodyCodeOnly,codeOnly,'PR must match the recorded Story verdict');
        if(codeOnly)assert.doesNotMatch(pr.body,/the bug is in the PROMPT/,'conflicting PR Story verdicts');
      }
      const snapshot=path=>{
        const result=spawnSync('git',['show',`${w.record().baseSha}:${path}`],{cwd:w.mergeCheckout,env:w.env,encoding:'utf8'});
        assert.equal(result.status,0,result.stderr);return result.stdout;
      };
      if(saved.stage==='prompt-pr') {
        oldPrompt=snapshot('value.prompt.md');newPrompt=readFileSync(join(w.mergeCheckout,'value.prompt.md'),'utf8');
        if(codeOnly)assert.equal(newPrompt,oldPrompt,'code-only checker requires unchanged prompt bytes');
        promptResult=await w.command(['test','value','--cache-clear','--json'],{cwd:w.mergeCheckout,actor:'checker'});
        const fresh=JSON.parse(promptResult.stdout);assert.ok(fresh.rows.every(row=>row.state==='passed'));
        // Keep the expected vector fixed; only the source snapshot changes.
        put(w.mergeCheckout,'value.prompt.md',oldPrompt);
        await w.command(['test','--fill-hash'],{cwd:w.mergeCheckout,actor:'checker'});
        oldPromptResult=await w.command(['test','value','--cache-clear','--json'],{cwd:w.mergeCheckout,actor:'checker',allowFailure:true});
        if(codeOnly) {
          assert.equal(oldPromptResult.code,0,'unchanged old prompt must pass');
          assert.ok(JSON.parse(oldPromptResult.stdout).rows.every(row=>row.state==='passed'));
          put(w.mergeCheckout,'value.mjs',snapshot('value.mjs'));
          oldNative=spawnSync(process.execPath,['--test','test/value.test.mjs'],{cwd:w.mergeCheckout,env:w.env,encoding:'utf8'});
          assert.equal(oldNative.status,1,'code-only checker needs native old-code failure');
          assert.match(oldNative.stdout+oldNative.stderr,/ERR_ASSERTION/,'old code must reach the assertion');
          assert.match(oldNative.stdout+oldNative.stderr,/FACTORY_VALUE/,'old code must fail for the issue reason');
          assert.equal(pairedNative?.status,0,'code-only checker needs a passing corrected code head');
          w.git(w.mergeCheckout,'restore','value.mjs');
        } else {
          assert.notEqual(oldPromptResult.code,0);assert.equal(JSON.parse(oldPromptResult.stdout).rows[0].state,'failed','old prompt must fail the value criterion');
        }
        w.git(w.mergeCheckout,'restore','value.prompt.md');
        assert.ok(r.status===0 || r.status===1&&pairedNative?.status===0,'red PR 1 native checks require its passing paired code PR');
      } else assert.equal(r.status,0,r.stdout+r.stderr);
      pr.statusCheckRollup=[{name:saved.stage==='prompt-pr'?'factory-prompt':'factory-native',status:'COMPLETED',conclusion:'SUCCESS',headSha:pr.headRefOid}];
      await w.github.gh(['pr','comment',String(pr.number),'--body-file','-'],{input:JSON.stringify({verdict:'PASS',head:pr.headRefOid,risk:1,family:'script',session:'fresh-'+pr.number,checker_mode:'scripted',evidence:{nativeExit:r.status,promptVerdict:promptResult?.code??null,oldPromptExit:oldPromptResult?.code??null,pairedNativeExit:pairedNative?.status??null,
        codeOnly,oldNativeExit:oldNative?.status??null,oldNativeOutput:oldNative?oldNative.stdout+oldNative.stderr:null,nativeCommand,
        base:w.record().baseSha,pairedHead:codePr?.headRefOid??null,oldPromptSha256:oldPrompt===null?null:sha(oldPrompt),newPromptSha256:newPrompt===null?null:sha(newPrompt)}})});
      await w.command(['workflow','status',String(w.record().number)]);
      await w.command(['autopilot','check-base','17',String(pr.number)]);
      const head=JSON.parse((await w.github.gh(['pr','view',String(pr.number),'--json','headRefOid'])).stdout).headRefOid;
      await w.github.gh(['pr','comment',String(pr.number),'--body-file','-'],{input:'Merge authorized by the synthetic factory operator auto setup and start; checked head '+head});
      await w.github.gh(['pr','merge',String(pr.number),'--merge','--match-head-commit',head]);
      await w.command(['autopilot','check-base','17',String(pr.number)]);
      assert.equal(JSON.parse((await w.github.gh(['pr','view',String(pr.number),'--json','state'])).stdout).state,'MERGED');
    }
    await w.github.gh(['issue','close','17']);await w.github.gh(['issue','edit','17','--remove-label','pdd:working']);await w.command(['workflow','status',String(w.record().number)]);
    assert.ok(w.github.prs.every(pr=>pr.state==='MERGED'));assert.equal(w.github.issues.get(17).state,'closed');assert.deepEqual(w.leadActions,[]);
  };
  return a;
}
