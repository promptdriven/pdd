import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {cancelRun, stepDone} from '../src/workflow-runner.mjs';
import {stopChats} from '../src/workflow-chat.mjs';
import {readRun, writeRun} from '../src/workflow-runs.mjs';
import {allocateIssueWorktree, releaseIssueClaim} from '../src/workflow-worktree.mjs';
import {cancellationFixture} from './helpers/cancellation-fixture.mjs';

const bytes=path=>readFileSync(path,'utf8');
const modes=['pane_not_found','server_not_running','no-pane'];
// Outcomes are requirements from cancel-when-herdr-cannot-answer Rules to check,
// not values harvested from the scanner. All OS data below are synthetic.
const classes=[
  ['sibling',true],['physical-alias-outside',true],['foreign-unreadable',true],
  ['root-ordinary',false],['descendant-detached',false],['root-idle',false],['root-caller',false],
  ['unreadable-cwd',false],['unknown-row-uid',false],['unknown-current-uid',false],
  ['missing-command',false],['malformed-birth',false],['reused-birth',false],
  ['malformed-inventory',false],['truncated-inventory',false],['hidden-caller',false],
  ['new-pid',false],['missing-ps',false],['inaccessible-root',false],
  ['positive-exit',true],['zombie',true],['final-uid-change',false],
  ['final-command-change',false],['incomplete-cwd',false],
];
const error=(message,code='EACCES')=>Object.assign(Error(message),{code});
const retained=run=>{
  const value=structuredClone(run);
  for(const key of ['state','cancelled','gate','journalSeq','updatedAt','stage','steps','waitingFor','resumeDecisions','waitingDecision','stageAgent','runDir']) delete value[key];
  return value;
};
async function fixture(action){
  let cleanup;
  const f=await cancellationFixture({after(fn){cleanup=fn;}});
  try{return await action(f);}finally{await cleanup();}
}
function request(f,operation){return operation==='cancel'?cancelRun({ref:f.old.runId,cwd:f.source},f.ports):f.start({name:'feature',replace:f.old.runId});}
function preserve(f,old,directory){
  assert.deepEqual(retained(readRun(directory)),retained(old),'all non-lifecycle data including decisions/PRs retained');
  for(const [path,value] of [[join(old.root,'work.txt'),'keep original work\n'],[join(old.root,'uncommitted.txt'),'keep uncommitted work\n'],[join(directory,'journal.md'),'keep journal bytes\n'],[join(directory,'evidence.txt'),'keep artifact bytes\n']]) assert.equal(bytes(path),value);
  assert.ok(f.git('show-ref','--verify',`refs/heads/${old.branch}`));
}
function durable(f,old,directory=f.runDir){
  const saved=readRun(directory);
  assert.equal(saved.state,'cancelled');assert.deepEqual(saved.cancelled,{state:'cancelled',at:600000});
  for(const key of ['gate','stage','stageAgent','waitingDecision']) assert.equal(saved[key],null);
  assert.deepEqual(saved.waitingFor,{decisions:[],what:null});assert.deepEqual(saved.resumeDecisions,[]);
  assert.equal(saved.journalSeq,old.journalSeq+1);
  const entries=JSON.parse(bytes(join(f.stateDir,'runs.json'))).runs;
  assert.equal(entries.find(row=>row.runDir===directory)?.state,'cancelled');
  assert.deepEqual(retained(saved),retained(old));
}
function setup(f,mode,platform,kind){
  if(mode==='no-pane'){
    f.old.chats=[];f.old.state='waiting';f.old.chatFailure={area:'plan',phase:'start',code:'server_not_running',message:'unconfirmed failed start',at:1};
    writeRun(f.old,f.ports);f.old=f.read();
  }
  const trace=[],reads=[],signals=[],herdrCalls=[],calls={};
  const root=f.old.root,outside=root+'-sibling',alias=root+'-outside-alias';
  let listCount=0;
  const command=kind==='root-idle'?'zsh':kind==='root-caller'?'node pdd.mjs':kind==='descendant-detached'?'node detached-writer.mjs':'node ordinary.mjs';
  const inside=['root-ordinary','root-idle','root-caller','descendant-detached'].includes(kind);
  const cwd=kind==='descendant-detached'?join(root,'nested'):inside?root:kind==='physical-alias-outside'?alias:outside;
  const system={platform,getpid:()=>7000,getuid:()=>kind==='unknown-current-uid'?null:123,
    realpath(path){reads.push(['realpath',path]);if(kind==='inaccessible-root'&&path===root)throw error('physical root permission denied');return path===alias?outside:path;},
    async execFile(file,args){
      reads.push([file,...args]);
      if(file==='ps'&&args[0]==='-axo'){
        listCount++;if(listCount===1)trace.push('inspect');
        if(kind==='missing-ps')throw error('ps tool missing','ENOENT');
        const caller=kind==='hidden-caller'?'':'7000 123 caller\n';
        if(kind==='malformed-inventory')return {stdout:caller+'not a process\n',stderr:''};
        const uid=kind==='unknown-row-uid'?'unknown':kind==='foreign-unreadable'?456:123;
        const cmd=kind==='missing-command'?'':kind==='final-command-change'&&listCount>1?'changed-command':command;
        const extra=kind==='new-pid'&&listCount>1?'7003 123 new-writer\n':'';
        const stdout=caller+`7001 ${uid} ${cmd}\n`+extra;
        return {stdout:kind==='truncated-inventory'?stdout.trimEnd():stdout,stderr:''};
      }
      if(file==='ps'&&args[0]==='-p'){
        const pid=+args[1],n=calls[pid]=(calls[pid]??0)+1;
        assert.ok(!(kind==='foreign-unreadable'&&pid===7001),'foreign metadata must not be inspected');
        if(pid===7001&&kind==='positive-exit')throw Object.assign(error('positive native exit',1),{stdout:'',stderr:''});
        if(pid===7001&&kind==='malformed-birth')return {stdout:'invalid birth\n',stderr:''};
        const uid=pid===7001&&kind==='final-uid-change'&&n>=3?456:123;
        const second=pid===7001&&kind==='reused-birth'&&n>1?'01':'00';
        return {stdout:`${uid} Fri Oct 30 01:00:${second} 2026 ${pid===7001&&kind==='zombie'?'Z':'S'}\n`,stderr:''};
      }
      if(file==='lsof'){
        const current=`p7000\nfcwd\nn${outside}\n`;
        const item=kind==='foreign-unreadable'||kind==='incomplete-cwd'?'':`p7001\nfcwd\nn${cwd}\n`;
        if(kind==='unreadable-cwd')throw error('cwd permission denied');
        return {stdout:current+item,stderr:''};
      }
      assert.fail(`Unexpected native command ${file} ${args}`);
    },
    readFile(path){
      reads.push(['read',path]);const pid=+path.split('/')[2];
      assert.ok(!(kind==='foreign-unreadable'&&pid===7001),'foreign metadata must not be read');
      if(path.endsWith('/stat')){
        const n=calls[pid]=(calls[pid]??0)+1;
        if(pid===7001&&kind==='positive-exit')throw error('positive native exit','ENOENT');
        if(pid===7001&&kind==='malformed-birth')return 'invalid stat\n';
        const birth=pid===7001&&kind==='reused-birth'&&n>1?'456':'123';
        return `${pid} (node ordinary) ${[pid===7001&&kind==='zombie'?'Z':'S',1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,birth].join(' ')}\n`;
      }
      if(path.endsWith('/status'))return `Uid: ${pid===7001&&kind==='final-uid-change'&&calls[pid]>=3?456:123} 123 123 123\n`;
      assert.fail(`Unexpected native file ${path}`);
    },
    readlink(path){
      reads.push(['readlink',path]);const pid=+path.split('/')[2];
      assert.ok(!(kind==='foreign-unreadable'&&pid===7001),'foreign cwd must not be read');
      if(pid===7001&&kind==='unreadable-cwd')throw error('cwd permission denied');
      if(pid===7001&&kind==='incomplete-cwd')return undefined;
      return pid===7000?outside:cwd;
    },
  };
  f.events.length=0;
  f.ports.confirm=async()=>{trace.push('confirm');return f.answer;};
  f.ports.herdr=async args=>{herdrCalls.push(args);throw error(`observed ${mode}`,mode);};
  f.ports.machineSystem=system;
  f.ports.stopProcessGroup=group=>{signals.push(group);assert.fail('No automatic fallback signals');};
  f.ports.closeChats=async()=>{trace.push('close');return {warnings:[]};};
  assert.equal(f.ports.stopChats,undefined,'runner must call production stop owner');
  assert.equal(f.ports.inspectMachineProcesses,undefined,'production raw scanner must decide observation');
  return {trace,reads,signals,herdrCalls};
}

for(const operation of ['cancel','replace']) test(`D1 bounded raw composition ${operation}: all 144 confirmed native cases`,async t=>{
  let checked=0;
  for(const mode of modes)for(const platform of ['linux','darwin'])for(const [kind,allowed]of classes){
    try{await fixture(async f=>{
      const {trace,signals,herdrCalls}=setup(f,mode,platform,kind),old=f.old;
      const before=bytes(join(f.runDir,'status.json')),index=bytes(join(f.stateDir,'runs.json')),claim=bytes(f.claim);
      f.ports.writeRun=(run,ports)=>{if(run.runId===old.runId)trace.push('save');return writeRun(run,ports);};
      f.ports.releaseIssueClaim=async(input,ports)=>{
        trace.push('release');durable(f,old);assert.equal(bytes(f.claim),claim);
        assert.deepEqual(input,{cwd:f.source,runId:old.runId,issueNumber:17});
        return releaseIssueClaim(input,ports);
      };
      f.ports.allocateIssueWorktree=async(input,ports)=>{trace.push('allocate');durable(f,old);assert.equal(existsSync(f.claim),false);return allocateIssueWorktree(input,ports);};
      const start=f.ports.startChat;f.ports.startChat=async input=>{trace.push('start');return start(input);};
      const out=await request(f,operation);
      assert.deepEqual(signals,[],'fallback cannot send a process signal');
      assert.ok(herdrCalls.every(args=>args[0]==='pane'&&args[1]==='process-info'),'fallback sends no alternate Herdr effects');
      assert.equal(out.exitCode,allowed?0:1,`${kind}: ${out.message}`);
      if(!allowed){
        assert.ok(!trace.some(name=>['close','save','release','allocate','start'].includes(name)),'live or unknown forbids every custody effect');
        assert.equal(bytes(join(f.runDir,'status.json')),before);assert.equal(bytes(join(f.stateDir,'runs.json')),index);assert.equal(bytes(f.claim),claim);
        assert.ok(out.message.includes(operation==='cancel'?`Retry: pdd workflow cancel ${old.runId}`:`Retry: pdd workflow run feature 17 --replace ${old.runId}`),out.message);
        assert.match(out.message,/outside the worktree/);
        if(['root-ordinary','descendant-detached','root-idle','root-caller','unreadable-cwd'].includes(kind)){assert.match(out.message,/7001/);assert.ok(out.message.includes(kind==='root-idle'?'zsh':kind==='root-caller'?'node pdd.mjs':kind==='descendant-detached'?'node detached-writer.mjs':'node ordinary.mjs'));}
        if(['root-idle','root-caller','missing-command','malformed-birth','reused-birth'].includes(kind))assert.doesNotMatch(out.message,/kill -TERM 7001/);
        preserve(f,old,f.runDir);
      }else{
        assert.deepEqual(trace,['confirm','inspect','close','save','release',...(operation==='replace'?['allocate','start']:[])]);
        const archived=operation==='replace'?`${f.runDir}-cancelled-${old.runId.slice(0,8)}`:f.runDir;
        durable(f,old,archived);preserve(f,old,archived);
        if(operation==='replace'){
          const fresh=f.read();assert.notEqual(fresh.runId,old.runId);assert.notEqual(fresh.root,old.root);assert.notEqual(fresh.branch,old.branch);assert.equal(JSON.parse(bytes(f.claim)).runId,fresh.runId);
          const current=bytes(join(f.runDir,'status.json')),newIndex=bytes(join(f.stateDir,'runs.json')),newClaim=bytes(f.claim);
          assert.match((await stepDone({step:'scope',summary:'late old completion',cwd:old.root},f.ports)).message,/cancelled.*Stop/s);
          assert.equal(bytes(join(f.runDir,'status.json')),current);assert.equal(bytes(join(f.stateDir,'runs.json')),newIndex);assert.equal(bytes(f.claim),newClaim);
        }else assert.equal(existsSync(f.claim),false);
      }
    });checked++;}catch(error){error.message=`${operation}/${mode}/${platform}/${kind}: ${error.message}`;throw error;}
  }
  assert.equal(checked,144);t.diagnostic(`Exhausted144/144 confirmed raw native cases for ${operation}; synthetic OS observations, real records/claims.`);
});

test('D1 bounded no-confirmation gate: all 12 unreachable-inspection cases',async t=>{
  let checked=0;
  for(const operation of ['cancel','replace'])for(const answer of [false,undefined])for(const mode of modes)await fixture(async f=>{
    const {trace,reads,signals,herdrCalls}=setup(f,mode,'linux','root-ordinary');f.answer=answer;
    const before=bytes(join(f.runDir,'status.json')),index=bytes(join(f.stateDir,'runs.json')),claim=bytes(f.claim);
    assert.equal((await request(f,operation)).exitCode,0);assert.deepEqual(trace,['confirm']);assert.deepEqual(reads,[]);assert.deepEqual(signals,[]);assert.deepEqual(herdrCalls,[]);assert.deepEqual(f.events,[],'decline has no persistence/start effect');
    assert.equal(bytes(join(f.runDir,'status.json')),before);assert.equal(bytes(join(f.stateDir,'runs.json')),index);assert.equal(bytes(f.claim),claim);preserve(f,f.old,f.runDir);checked++;
  });
  assert.equal(checked,12);t.diagnostic('Exhausted12/12 declines; native data is unreachable until confirmation.');
});

test('D1 bounded public stop owner: all 3240 observation schema combinations',async t=>{
  const root='/bounded/worktree';let checked=0;
  for(const currentUid of [123,null])for(const uid of [123,456,null])for(const birth of ['birth','',null])for(const command of ['node worker','',null])
    for(const cwd of [root,root+'/nested',root+'-sibling',null,'relative'])for(const pidShape of ['valid','zero','duplicate'])for(const complete of [true,false])for(const reason of ['','actual incomplete cause']){
      const foreign=currentUid===123&&uid===456;
      const permitted=currentUid===123&&complete&&reason===''&&(foreign||(pidShape==='valid'&&uid===123&&birth==='birth'&&command==='node worker'&&cwd===root+'-sibling'));
      let closes=0,signals=0;
      const row={pid:pidShape==='zero'?0:7001,uid,birth,command,cwd},processes=pidShape==='duplicate'?[row,{...row}]:[row];
      const out=await stopChats({root,state:'waiting',chats:[]},{inspectMachineProcesses:async()=>({currentUid,complete,reason,processes}),closeChats:async()=>{closes++;return {warnings:[]};},stopProcessGroup:()=>{signals++;}});
      assert.equal(out.stopped,permitted,JSON.stringify({currentUid,uid,birth,command,cwd,pidShape,complete,reason,out}));
      assert.equal(closes,permitted?1:0,'unknown/live forbids tab close');assert.equal(signals,0,'fallback never signals');checked++;
    }
  assert.equal(checked,3240);t.diagnostic('Exhausted3240/3240 owner observations; independent Story oracle excludes foreign rows before metadata and requires complete current-user absence.');
});

test('D1 bounded durable custody faults: all 9 boundary cases',async t=>{
  let checked=0;
  for(const operation of ['cancel','replace'])for(const fault of ['save-before','save-after','wrong-owner','release','allocation']){
    if(operation==='cancel'&&fault==='allocation')continue;
    await fixture(async f=>{
      const {trace,signals}=setup(f,'pane_not_found','linux','sibling'),old=f.old;
      const before=bytes(join(f.runDir,'status.json')),index=bytes(join(f.stateDir,'runs.json'));
      if(fault==='wrong-owner'){const claim=JSON.parse(bytes(f.claim));claim.runId='foreign-claim-owner';writeFileSync(f.claim,JSON.stringify(claim));}
      const claim=bytes(f.claim);
      f.ports.writeRun=(run,ports)=>{
        if(run.runId===old.runId){trace.push('save');if(fault==='save-before')throw Error('actual save-before fault');}
        const result=writeRun(run,ports);
        if(run.runId===old.runId&&fault==='save-after')throw Error('actual save-after lost reply');
        return result;
      };
      f.ports.releaseIssueClaim=async(input,ports)=>{
        trace.push('release');durable(f,old);assert.equal(bytes(f.claim),claim);
        assert.deepEqual(input,{cwd:f.source,runId:old.runId,issueNumber:17});
        if(fault==='release')throw Error('actual release fault');
        return releaseIssueClaim(input,ports);
      };
      f.ports.allocateIssueWorktree=async()=>{trace.push('allocate');durable(f,old);assert.equal(existsSync(f.claim),false);return {state:'recovery_required',message:'actual allocation fault'};};
      const out=await request(f,operation);assert.deepEqual(signals,[]);assert.equal(out.exitCode,1,`${operation}/${fault}: ${out.message}`);
      assert.deepEqual(trace,['confirm','inspect','close','save',...(['wrong-owner','release','allocation'].includes(fault)?['release']:[]),...(fault==='allocation'?['allocate']:[])]);
      if(fault==='save-before'){assert.equal(bytes(join(f.runDir,'status.json')),before);assert.equal(bytes(join(f.stateDir,'runs.json')),index);}else durable(f,old);
      if(fault==='allocation')assert.equal(existsSync(f.claim),false);else assert.equal(bytes(f.claim),claim,'failure never releases another owner or uncertain durable custody');
      assert.equal(f.chats.length,1,'no replacement after boundary failure');preserve(f,old,f.runDir);checked++;
    });
  }
  assert.equal(checked,9);t.diagnostic('Exhausted9/9 save-before/save-after/wrong-owner/release/allocation fault cases with real persisted records/claims.');
});
