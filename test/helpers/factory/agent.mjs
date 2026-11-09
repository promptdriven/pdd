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
    const {root}=w.record();
    put(root,'value.prompt.md',valuePrompt(2));
    put(root,'user_stories/value.md','As a user, I want the value to be two, so that the result follows my request.\n\n## Acceptance criteria\n\n1. The value is 2.\n');
    put(root,'tests/value.json',scenario);
    put(root,'test/value.test.mjs',nativeTest);
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
    await w.command(['workflow','approve','17','--said','-'],{cwd:run.root,actor:'coordinator',stdin:words});
  };
  a.step=async({allowFailure=false}={})=>{
    await w.command(['workflow','status','17']);
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
      await w.command(['workflow','prove','17','--test',nativeCommand,'--expect','FACTORY_VALUE'],{cwd:run.root});
      const proof=readJson(join(run.runDir,'old-code-proof.json'));assert.equal(proof.outcome,'proved');assert.equal(proof.base.exitCode,1);assert.equal(proof.head.exitCode,0);
      if(area.replay_evidence)a.evidence();
    }
    // Recompute after formal/review in case a step committed source.
    if(['formal','review'].includes(step) && area.replay_evidence)a.evidence();
    const argv=['workflow','done',step,'--summary',`Factory ${step}; ${step==='check'?'Prompt tests: 1 of 1 pass':'native evidence retained'}`];
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
      let promptResult=null,oldPromptResult=null;
      if(saved.stage==='prompt-pr') {
        promptResult=await w.command(['test','value','--cache-clear','--json'],{cwd:w.mergeCheckout,actor:'checker'});
        const fresh=JSON.parse(promptResult.stdout);assert.ok(fresh.rows.every(row=>row.state==='passed'));
        // Run the same expected vector against the old prompt in this private checkout.
        put(w.mergeCheckout,'value.prompt.md',w.git(w.record().root,'show',`${w.record().baseSha}:value.prompt.md`)+'\n');
        await w.command(['test','--fill-hash'],{cwd:w.mergeCheckout,actor:'checker'});
        oldPromptResult=await w.command(['test','value','--cache-clear','--json'],{cwd:w.mergeCheckout,actor:'checker',allowFailure:true});
        assert.notEqual(oldPromptResult.code,0);assert.equal(JSON.parse(oldPromptResult.stdout).rows[0].state,'failed','old prompt must fail the value criterion');
        w.git(w.mergeCheckout,'restore','value.prompt.md');
        assert.ok(r.status===0 || r.status===1&&pairedNative?.status===0,'red PR 1 native checks require its passing paired code PR');
      } else assert.equal(r.status,0,r.stdout+r.stderr);
      pr.statusCheckRollup=[{name:saved.stage==='prompt-pr'?'factory-prompt':'factory-native',status:'COMPLETED',conclusion:'SUCCESS',headSha:pr.headRefOid}];
      await w.github.gh(['pr','comment',String(pr.number),'--body-file','-'],{input:JSON.stringify({verdict:'PASS',head:pr.headRefOid,risk:1,family:'script',session:'fresh-'+pr.number,checker_mode:'scripted',evidence:{nativeExit:r.status,promptVerdict:promptResult?.code??null,oldPromptExit:oldPromptResult?.code??null,pairedNativeExit:pairedNative?.status??null}})});
      await w.command(['workflow','status','17']);
      await w.command(['autopilot','check-base','17',String(pr.number)]);
      const head=JSON.parse((await w.github.gh(['pr','view',String(pr.number),'--json','headRefOid'])).stdout).headRefOid;
      await w.github.gh(['pr','comment',String(pr.number),'--body-file','-'],{input:'Merge authorized by the synthetic factory operator auto setup and start; checked head '+head});
      await w.github.gh(['pr','merge',String(pr.number),'--merge','--match-head-commit',head]);
      await w.command(['autopilot','check-base','17',String(pr.number)]);
      assert.equal(JSON.parse((await w.github.gh(['pr','view',String(pr.number),'--json','state'])).stdout).state,'MERGED');
    }
    await w.github.gh(['issue','close','17']);await w.github.gh(['issue','edit','17','--remove-label','pdd:working']);await w.command(['workflow','status','17']);
    assert.ok(w.github.prs.every(pr=>pr.state==='MERGED'));assert.equal(w.github.issues.get(17).state,'closed');assert.deepEqual(w.leadActions,[]);
  };
  return a;
}
