import test from 'node:test';
import assert from 'node:assert/strict';
import {spawn} from 'node:child_process';
import {once} from 'node:events';
import {mkdirSync, readFileSync, symlinkSync} from 'node:fs';
import {join} from 'node:path';
import {stopChats} from '../src/workflow-chat.mjs';
import {disposableFixture} from './helpers/disposable-fixture.mjs';

const missing=()=>{throw Object.assign(Error('closed pane'),{code:'pane_not_found'});};
const run=root=>({root,state:'waiting',agent:'codex',chats:[{paneId:'missing',tabId:'old'}]});
const stat=(pid,birth='123',state='S')=>`${pid} (node worker) ${[state,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,birth].join(' ')}\n`;
const gone=()=>Object.assign(Error('positively gone'),{code:'ENOENT'});

// Raw OS command/file fixtures exercise the production scanner. No alternate
// scanner, check-only export or stopped receipt is supplied here.
function machine(t,platform='linux',options={}) {
  const {path:base}=disposableFixture(t,'pdd-d1-native-'),root=join(base,'worktree');
  mkdirSync(root);mkdirSync(root+'-sibling');mkdirSync(join(root,'nested'));symlinkSync(root,join(base,'alias'));
  const calls=[],reads=[],closed=[],counts={};
  const cwd=options.inside?root:options.descendant?join(root,'nested'):options.alias?join(base,'alias'):root+'-sibling';
  const inventory=options.inventory??'7001 123 node\n7002 456 foreign\n';
  const system={platform,getuid:()=>options.uid??123,getpid:()=>7000,
    realpath:path=>path===join(base,'alias')?root:path,
    execFile:async(file,args)=>{
      calls.push([file,...args]);
      if(file==='ps'&&args[0]==='-axo') {
        counts.list=(counts.list??0)+1;
        if(options.psError)throw Object.assign(Error('ps missing'),{code:'ENOENT'});
        let stdout=counts.list>1&&options.laterInventory!==undefined?options.laterInventory:inventory;
        if (!options.hidden) stdout='7000 123 caller\n'+stdout;
        return {stdout,stderr:options.psStderr??''};
      }
      if(file==='ps'&&args[0]==='-p') {
        const pid=+args[1];counts[pid]=(counts[pid]??0)+1;
        assert.notEqual(pid,7002,'Exclude foreign UID before identity access');
        if(pid!==7000&&(options.reappear&&counts[pid]===1||options.gone&&(options.gone!=='after'||counts[pid]>1)))throw Object.assign(Error('gone'),{code:1,stdout:'',stderr:''});
        if(pid!==7000&&options.identityError)throw Object.assign(Error('ps permission denied'),{code:1,stdout:'',stderr:'EACCES'});
        return {stdout:pid!==7000&&options.badIdentity?'malformed':`${pid!==7000&&options.finalUidChanged&&counts[pid]>=3?456:123} Fri Oct 30 01:00:0${pid!==7000&&options.reuse&&counts[pid]>1?1:0} 2026 ${pid!==7000&&options.badState?'?':pid!==7000&&options.reappearZombie&&counts[pid]===1?'Z':'S'}\n`,stderr:''};
      }
      if(file==='lsof') {
        const stdout=`p7000\nfcwd\nn${root}-sibling\n`+(options.lsof??`p7001\nfcwd\nn${cwd}\n`);
        if(options.lsofCode)throw Object.assign(Error('lsof failed'),{code:options.lsofCode,stdout,stderr:options.lsofStderr??''});
        return {stdout,stderr:options.lsofStderr??''};
      }
      assert.fail(`Unexpected OS boundary ${file} ${args}`);
    },
    readFile:path=>{
      reads.push(path);assert.ok(!path.startsWith('/proc/7002/'),'No foreign metadata read');
      const pid=+path.split('/')[2];
      if(path.endsWith('/stat')) {
        counts[pid]=(counts[pid]??0)+1;
        if(pid!==7000&&(options.reappear&&counts[pid]===1||options.gone&&(options.gone!=='after'||counts[pid]>1)))throw gone();
        if(pid!==7000&&options.identityError)throw Object.assign(Error('stat access denied'),{code:'EACCES'});
        return pid!==7000&&options.badIdentity?'invalid stat':stat(pid,pid!==7000&&options.reuse&&counts[pid]>1?'456':'123',pid!==7000&&(options.zombie||options.reappearZombie&&counts[pid]===1)?'Z':pid!==7000&&options.badState?'?':options.state??'S');
      }
      if(path.endsWith('/status'))return pid!==7000&&options.badUid?'Uid: unreadable\n':`Uid:\t${pid!==7000&&(options.changedUid||options.finalUidChanged&&counts[pid]>=3)?999:123}\t123\t123\t123\n`;
      assert.fail(`Unexpected file ${path}`);
    },
    readlink:path=>{reads.push(path);assert.ok(!path.startsWith('/proc/7002/'));if(!path.startsWith('/proc/7000/')&&options.cwdError)throw Object.assign(Error('cwd permission denied'),{code:options.cwdError});return path.startsWith('/proc/7000/')?root+'-sibling':cwd;},
  };
  return {root,base,calls,reads,closed,ports:{herdr:missing,machineSystem:system,closeChats:async()=>{closed.push(true);return {warnings:[]};},stopProcessGroup:()=>assert.fail('Never signal fallback processes')}};
}
for(const platform of ['linux','darwin']) for(const [name,options,expected] of [
  ['complete outside and foreign unreadable',{},true],['ordinary live in root',{inside:true},false],
  ['descendant',{descendant:true},false],['symlink physical root',{alias:true},false],
  ['positive gone',{gone:true},true],['exit during metadata',{gone:'after'},true],
  ['birth reused',{reuse:true},false],['unreadable identity',{identityError:true},false],['malformed identity',{badIdentity:true},false],
  ['malformed inventory',{inventory:'7001 ??? node\n'},false],['truncated inventory',{inventory:'7001 123 node'},false],
  ['duplicate inventory',{inventory:'7001 123 node\n7001 123 node\n'},false],['ps diagnostic',{psStderr:'permission denied'},false],
  ['hidden caller',{hidden:true},false],['missing ps',{psError:true},false],['new live PID',{laterInventory:'7001 123 node\n7003 123 writer\n'},false],
  ['unknown row UID',{inventory:'7001 unknown node\n'},false],['missing current command',{inventory:'7001 123\n'},false],
  ['foreign absent command',{inventory:'7001 123 node\n7002 456\n'},true],
  ['new final unknown UID',{laterInventory:'7001 123 node\n7003 unknown service\n'},false],
  ['absence then reused PID',{reappear:true},false],['zombie then reused PID',{reappearZombie:true},false],
  ['final native UID changed',{finalUidChanged:true},false],['unknown native state',{badState:true},false],
]) test(`D1 production ${platform} ${name}`,async t=>{
  const f=machine(t,platform,options),out=await stopChats(run(options.alias?join(f.base,'alias'):f.root),f.ports);
  assert.equal(out.stopped,expected,JSON.stringify(out));assert.equal(f.closed.length,expected?1:0);
  if(options.inside||options.descendant||options.alias){assert.match(out.warnings[0],/7001.*node/);assert.match(out.warnings[0],/kill -TERM 7001/);}
});
for(const [name,options,expected] of [
  ['cwd EACCES',{cwdError:'EACCES'},false],['cwd vanished but identity live',{cwdError:'ENOENT'},false],
  ['traced outside process',{state:'t'},true],['zombie',{zombie:true},true],['UID unreadable',{badUid:true},false],['UID changed',{changedUid:true},false],
]) test(`D1 production linux ${name}`,async t=>{
  const f=machine(t,'linux',options),out=await stopChats(run(f.root),f.ports);assert.equal(out.stopped,expected,JSON.stringify(out));
  if(options.cwdError)assert.match(out.warnings[0],new RegExp(`7001.*node.*${options.cwdError}`));
});
for(const [name,options,expected] of [
  ['clean partial exit1',{lsofCode:1},true],['foreign unreadable metadata',{lsof:'p7002\nfcwd\nnunreadable\np7001\nfcwd\nn/outside\n'},true],['omitted live cwd',{lsofCode:1,lsof:''},false],
  ['omitted positively gone',{lsofCode:1,lsof:'',gone:'after'},true],['diagnostic exit1',{lsofCode:1,lsofStderr:'permission denied'},false],
  ['hard error',{lsofCode:2},false],['relative cwd',{lsof:'p7001\nfcwd\nnrelative\n'},false],['incomplete cwd',{lsof:'p7001\nfcwd\n'},false],
  ['unknown field',{lsof:'p7001\nfcwd\nxBAD\n'},false],['duplicate cwd',{lsof:'p7001\nfcwd\nn/outside\np7001\nfcwd\nn/outside\n'},false],
  ['truncated lsof',{lsof:'p7001\nfcwd\nn/outside'},false],['lsof-only process',{lsof:'p7003\nfcwd\nn/worktree\n'},false],
]) test(`D1 production darwin ${name}`,async t=>{
  const f=machine(t,'darwin',options),out=await stopChats(run(f.root),f.ports);assert.equal(out.stopped,expected,JSON.stringify(out));
});

test('D1 actual Linux owned ordinary/detached/idle/caller blockers; protected cwd stays UNKNOWN',{skip:process.platform!=='linux'},async t=>{
  const tracked=[],birth=pid=>readFileSync(`/proc/${pid}/stat`,'utf8').split(') ')[1].split(' ')[19];
  // Registered before fixture cleanup: recheck positively owned birth identities,
  // signal only owned handles, and reap before any directory is removed.
  t.after(async()=>{for(const {child,identity,closed}of tracked){if(child.exitCode===null&&child.signalCode===null){assert.equal(birth(child.pid),identity);child.kill('SIGTERM');}await closed;}});
  const {path:base,ownChild}=disposableFixture(t,'pdd-d1-owned-'),root=join(base,'worktree');mkdirSync(root);mkdirSync(join(root,'nested'));
  const children=[];
  for(const [cwd,shell,detached]of [[root,false,false],[join(root,'nested'),false,false],[root,false,true],[root,true,false]]) {
    const child=spawn(shell?'/bin/bash':process.execPath,shell?['--noprofile','--norc','-c',"printf 'ready\\n'; read -r disposable_input"]:['-e',"process.stdout.write('ready\\n');setInterval(()=>{},1000)"],{cwd,detached,stdio:['pipe','pipe','pipe']});
    ownChild(child);tracked.push({child,identity:birth(child.pid),closed:once(child,'close')});await once(child.stdout,'data');children.push(child);
  }
  const births=children.map(child=>birth(child.pid));
  const out=await stopChats(run(root),{herdr:missing,stopProcessGroup:()=>assert.fail('Native fallback may not signal')});assert.equal(out.stopped,false,JSON.stringify(out));
  for(const [index,child]of children.entries()){assert.ok(out.warnings[0].includes(String(child.pid)),out.warnings[0]);assert.equal(birth(child.pid),births[index]);}
  assert.match(out.warnings[0],/node/);assert.match(out.warnings[0],/bash/);
  const program=`import {stopChats} from ${JSON.stringify(new URL('../src/workflow-chat.mjs',import.meta.url).href)};const out=await stopChats(${JSON.stringify(run(root))},{herdr:()=>{throw Object.assign(Error('closed'),{code:'pane_not_found'})}});console.log(JSON.stringify({pid:process.pid,out}));`;
  const caller=spawn(process.execPath,['--input-type=module','-e',program],{cwd:root,stdio:['ignore','pipe','pipe']});ownChild(caller);let output='';caller.stdout.on('data',data=>output+=data);
  const [code]=await once(caller,'close');assert.equal(code,0,output);const result=JSON.parse(output);assert.equal(result.out.stopped,false);assert.ok(result.out.warnings[0].includes(String(result.pid)));
  assert.ok(!result.out.warnings[0].includes(`kill -TERM ${result.pid}`),'Do not advise killing the calling cancellation request');
  for(const {child,identity,closed}of tracked){assert.equal(birth(child.pid),identity);child.kill('SIGTERM');await closed;assert.throws(()=>birth(child.pid),error=>['ENOENT','ESRCH'].includes(error.code));}
  const after=await stopChats(run(root),{herdr:missing,stopProcessGroup:()=>assert.fail('No fallback signals')});
  // This retry is from outside after the owned caller/writers exit. A host with
  // protected same-user services still refuses UNKNOWN; do not fake emptiness.
  if(after.stopped===false)assert.match(after.warnings[0],/unreadable|unknown|unavailable|changed|permission|EACCES|EPERM|incomplete|inventory/i);
  t.diagnostic(`Retry after owned-child exit: ${after.stopped?'complete absence within scan window':'UNKNOWN: '+after.warnings[0]}`);
  t.diagnostic(`Actual finite Linux scan refused and named owned blockers; protected cwd EACCES observed: ${out.warnings[0].includes('EACCES')}. No empty-machine proof or production signals.`);
});
