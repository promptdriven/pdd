import test from 'node:test';
import assert from 'node:assert/strict';
import {EventEmitter} from 'node:events';
import {PassThrough,Writable} from 'node:stream';
import {createClaudeSession} from '../src/agent-claude-session.mjs';
const tick=()=>new Promise(r=>setImmediate(r));
function fixture(handler=()=>{}){
 const child=new EventEmitter(),writes=[],calls=[];child.stdout=new PassThrough();child.stderr=new PassThrough();
 child.stdin=new Writable({write(chunk,enc,done){const row=JSON.parse(String(chunk));writes.push(row);done();queueMicrotask(()=>handler(row,child));}});
 child.kill=signal=>{calls.push(signal);queueMicrotask(()=>child.emit('close',0,signal));return true;};
 const spawn=(...args)=>{calls.push(args);return child;};
 const send=row=>child.stdout.write(JSON.stringify(row)+'\n');
 return{child,writes,calls,spawn,send};
}
function ready(row,child){if(row.type==='control_request')child.stdout.write(JSON.stringify({type:'control_response',response:{subtype:'success',request_id:row.request_id,response:{}}})+'\n');}
const result=(text='answer',extra={})=>({type:'result',session_id:'session-one',is_error:false,result:text,...extra});
test('one restricted named child serves two sequential messages, not assistant prose',async()=>{
 const f=fixture(ready),env={HOME:'/personal',CLAUDE_CONFIG_DIR:'/named'},session=createClaudeSession({command:'/named/claude',cwd:'/project',env,spawn:f.spawn});
 const first=session.run('first');await tick();assert.equal(f.writes.at(-1).message.content,'first');
 f.send({type:'assistant',message:{content:[{type:'text',text:'not terminal'}]}});let done=false;first.then(()=>done=true);await tick();assert.equal(done,false);
 f.send(result());assert.equal(JSON.parse((await first).stdout).result,'answer');
 const second=session.run('second');await tick();f.send(result('next'));assert.equal(JSON.parse((await second).stdout).result,'next');
 assert.equal(f.calls.filter(Array.isArray).length,1);const [command,args,options]=f.calls[0];assert.equal(command,'/named/claude');assert.equal(options.env,env);assert.equal(options.shell,false);assert.ok(args.includes('--safe-mode'));assert.ok(args.includes('--verbose'));assert.equal(args[args.indexOf('--output-format')+1],'stream-json');assert.ok(!args.some(x=>/model|effort|dangerously/.test(x)));assert.equal(f.writes.filter(r=>r.type==='user').length,2);assert.equal(f.writes.at(-1).client_composed,true);await session.close();
});
test('split UTF8 and lines preserve exact terminal content',async()=>{
 const f=fixture(ready),s=createClaudeSession({spawn:f.spawn});const p=s.run('hi');await tick();const b=Buffer.from(JSON.stringify(result('é🙂'))+'\n');for(const byte of b)f.child.stdout.write(Buffer.from([byte]));assert.equal(JSON.parse((await p).stdout).result,'é🙂');await s.close();
});
test('initialize is correlated and no user prompt precedes readiness',async()=>{
 const f=fixture(),s=createClaudeSession({spawn:f.spawn});const p=s.run('private');await tick();assert.equal(f.writes.length,1);assert.equal(f.writes[0].request.subtype,'initialize');f.send({type:'control_response',response:{subtype:'success',request_id:'wrong',response:{}}});await assert.rejects(p,e=>e.safeToFallback===false);assert.equal(f.writes.some(r=>r.type==='user'),false);await s.close();
});
test('explicit unsupported startup is safe fallback, post-submission is never safe',async()=>{
 const f=fixture(),s=createClaudeSession({spawn:f.spawn});const p=s.run('hi');await tick();f.child.stderr.write("error: unknown option '--input-format'\n");f.child.emit('close',1);await assert.rejects(p,e=>e.safeToFallback===true);await s.close();
 const g=fixture(ready),t=createClaudeSession({spawn:g.spawn});const q=t.run('hi');await tick();g.child.stderr.write("error: unknown option '--input-format'\n");g.child.emit('close',1);await assert.rejects(q,e=>e.safeToFallback===false);await t.close();
});
test('known permission request is denied; unknown tool terminates closed',async()=>{
 const f=fixture(ready),s=createClaudeSession({spawn:f.spawn});const p=s.run('hi');await tick();f.send({type:'control_request',request_id:'deny1',request:{subtype:'can_use_tool',tool_name:'Read',input:{}}});await tick();assert.equal(f.writes.at(-1).response.response.behavior,'deny');f.send(result());await p;
 const q=s.run('next');await tick();f.send({type:'assistant',message:{content:[{type:'tool_use',name:'Bash'}]}});await assert.rejects(q,e=>e.safeToFallback===false);await s.close();
});
test('timeout cancellation malformed oversized exit and early results never replay',async()=>{
 for(const mode of ['timeout','abort','malformed','overflow','exit','early']){
  const f=fixture(mode==='early'?()=>{}:ready),s=createClaudeSession({spawn:f.spawn,timeoutMs:mode==='timeout'?10:1000,maxBytes:500}),controller=new AbortController();const p=s.run('hi',{signal:controller.signal});const rejected=assert.rejects(p,e=>e.safeToFallback===false);await tick();
  if(mode==='abort')controller.abort();if(mode==='malformed')f.child.stdout.write('not-json\n');if(mode==='overflow')f.child.stdout.write('x'.repeat(501));if(mode==='exit')f.child.emit('close',1);if(mode==='early')f.send(result());await rejected;await assert.rejects(s.run('never'),e=>e.safeToFallback===false);await s.close();
 }
});
test('concurrent run refuses without interfering and output bounds reset per turn',async()=>{
 const f=fixture(ready),s=createClaudeSession({spawn:f.spawn,maxBytes:700});const p=s.run('one');await tick();await assert.rejects(s.run('two'),/active/i);f.child.stderr.write('a'.repeat(300));f.send(result());assert.equal((await p).stderr.length,300);const q=s.run('three');await tick();f.child.stderr.write('b'.repeat(300));f.send(result());assert.equal((await q).stderr,'b'.repeat(300));await s.close();await s.close();
});
test('unsafe duplicate flags or positional prompt never spawn',async()=>{
 const base=['-p','--safe-mode','--tools','Read,Grep,Glob','--permission-mode','plan','--permission-prompts','none','--strict-mcp-config','--no-chrome','--no-session-persistence'];
 for(const extra of [['--permission-mode','bypassPermissions'],['--tools','Bash'],['execute before handshake'],['--dangerously-skip-permissions']]){
  let spawned=false;assert.throws(()=>createClaudeSession({args:[...base,...extra],spawn:()=>{spawned=true;}}));assert.equal(spawned,false);
 }
 const f=fixture(ready),s=createClaudeSession({args:[...base,'--output-format','json'],spawn:f.spawn});const p=s.run('hi');await tick();f.send(result());await p;assert.equal(f.calls[0][1].filter(x=>x==='--output-format').length,1);await s.close();
});
test('error envelopes, wrong identity, unknown controls and duplicate results stay closed',async()=>{
 const f=fixture(ready),s=createClaudeSession({spawn:f.spawn});const p=s.run('one');await tick();f.send({type:'result',session_id:'session-one',is_error:true,errors:['rate limit'],subtype:'error_during_execution'});assert.equal(JSON.parse((await p).stdout).is_error,true);await assert.rejects(s.run('retry'),e=>e.safeToFallback===false);await s.close();
 for(const mode of ['identity','control','duplicate']){
  const g=fixture(ready),t=createClaudeSession({spawn:g.spawn});const q=t.run('one');await tick();
  if(mode==='identity'){g.send({type:'system',session_id:'session-one'});g.send(result('wrong',{session_id:'session-two'}));}
  if(mode==='control')g.send({type:'control_request',request_id:'unknown',request:{subtype:'set_permission_mode',mode:'bypassPermissions'}});
  if(mode==='duplicate')g.child.stdout.write(JSON.stringify(result())+'\n'+JSON.stringify(result())+'\n');
  await assert.rejects(q,e=>e.safeToFallback===false);await t.close();
 }
});
test('split stderr UTF8 preserves diagnostics and provider failures never allow fallback',async()=>{
 const f=fixture(ready),s=createClaudeSession({spawn:f.spawn});const p=s.run('hi');await tick();for(const byte of Buffer.from('é🙂'))f.child.stderr.write(Buffer.from([byte]));f.send(result());assert.equal((await p).stderr,'é🙂');await s.close();
 const g=fixture(),t=createClaudeSession({spawn:g.spawn});const q=t.run('hi');await tick();g.child.stderr.write('Usage limit reached; try again later');g.child.emit('close',1);await assert.rejects(q,e=>e.safeToFallback===false);await t.close();
});
test('partial trailing or replayed terminal output cannot cross turn boundaries',async()=>{
 const f=fixture(ready),s=createClaudeSession({spawn:f.spawn});const p=s.run('one');await tick();f.child.stdout.write(JSON.stringify(result())+'\n'+JSON.stringify(result()).slice(0,10));await assert.rejects(p,e=>e.safeToFallback===false);await s.close();
 const g=fixture(ready),t=createClaudeSession({spawn:g.spawn});const q=t.run('one');await tick();g.send(result('one',{uuid:'unique-terminal'}));await q;const r=t.run('two');await tick();g.send(result('one',{uuid:'unique-terminal'}));await assert.rejects(r,e=>e.safeToFallback===false);await t.close();
});
test('close and already-cancelled requests never leave a pending turn',async()=>{
 const f=fixture(ready),s=createClaudeSession({spawn:f.spawn}),controller=new AbortController();controller.abort();await assert.rejects(s.run('no',{signal:controller.signal}),e=>e.safeToFallback===false);assert.equal(f.calls.length,0);const p=s.run('hi');const rejected=assert.rejects(p,/closed/);await tick();await s.close();await rejected;await s.close();
});
test('group teardown kills a TERM-ignoring descendant after direct child exits',async t=>{
 if(process.platform==='win32'){t.skip('POSIX process-group regression');return;}
 const fs=await import('node:fs'),path=await import('node:path'),os=await import('node:os');
 const folder=fs.mkdtempSync(path.join(os.tmpdir(),'pdd-claude-group-')),command=path.join(folder,'claude.cjs'),ready=path.join(folder,'ready'),beat=path.join(folder,'beat');let descendant;
 t.after(()=>{if(descendant)try{process.kill(descendant,'SIGKILL');}catch{}fs.rmSync(folder,{recursive:true,force:true});});
 const program=`const fs=require('node:fs');process.on('SIGTERM',()=>{});fs.writeFileSync(${JSON.stringify(ready)},String(process.pid));setInterval(()=>fs.writeFileSync(${JSON.stringify(beat)},String(Date.now())),20);`;
 fs.writeFileSync(command,`#!${process.execPath}\nconst readline=require('node:readline'),fs=require('node:fs');readline.createInterface({input:process.stdin}).on('line',line=>{const row=JSON.parse(line);if(row.type==='control_request')process.stdout.write(JSON.stringify({type:'control_response',response:{subtype:'success',request_id:row.request_id,response:{}}})+'\\n');else if(row.type==='user'){require('node:child_process').spawn(process.execPath,['-e',${JSON.stringify(program)}],{stdio:'ignore'});const poll=setInterval(()=>{if(fs.existsSync(${JSON.stringify(ready)})){clearInterval(poll);process.stdout.write('not-json\\n');}},10);}});`,{mode:0o700});
 const s=createClaudeSession({command,timeoutMs:3000});await assert.rejects(s.run('private'),e=>e.safeToFallback===false);descendant=Number(fs.readFileSync(ready,'utf8'));await s.close();
 await new Promise(r=>setTimeout(r,150));const first=fs.existsSync(beat)?fs.readFileSync(beat,'utf8'):'';await new Promise(r=>setTimeout(r,150));assert.equal(fs.existsSync(beat)?fs.readFileSync(beat,'utf8'):'',first,'descendant still alive after close');
});

test('spontaneous child exit cleans descendants without waiting for caller close',async t=>{
 if(process.platform==='win32'){t.skip('POSIX process-group regression');return;}
 const fs=await import('node:fs'),path=await import('node:path'),os=await import('node:os');
 const folder=fs.mkdtempSync(path.join(os.tmpdir(),'pdd-claude-group-')),command=path.join(folder,'claude.cjs'),ready=path.join(folder,'ready'),beat=path.join(folder,'beat');let descendant;
 t.after(()=>{if(descendant)try{process.kill(descendant,'SIGKILL');}catch{}fs.rmSync(folder,{recursive:true,force:true});});
 const program=`const fs=require('node:fs');process.on('SIGTERM',()=>{});fs.writeFileSync(${JSON.stringify(ready)},String(process.pid));setInterval(()=>fs.writeFileSync(${JSON.stringify(beat)},String(Date.now())),20);`;
 fs.writeFileSync(command,`#!${process.execPath}\nconst readline=require('node:readline'),fs=require('node:fs');readline.createInterface({input:process.stdin}).on('line',line=>{const row=JSON.parse(line);if(row.type==='control_request')process.stdout.write(JSON.stringify({type:'control_response',response:{subtype:'success',request_id:row.request_id,response:{}}})+'\\n');else if(row.type==='user'){require('node:child_process').spawn(process.execPath,['-e',${JSON.stringify(program)}],{stdio:'ignore'});const poll=setInterval(()=>{if(fs.existsSync(${JSON.stringify(ready)})){clearInterval(poll);process.exit(4);}},10);}});`,{mode:0o700});
 const s=createClaudeSession({command,timeoutMs:3000});await assert.rejects(s.run('private'),e=>e.safeToFallback===false);descendant=Number(fs.readFileSync(ready,'utf8'));await new Promise(r=>setTimeout(r,750));
 await new Promise(r=>setTimeout(r,150));const first=fs.existsSync(beat)?fs.readFileSync(beat,'utf8'):'';await new Promise(r=>setTimeout(r,150));assert.equal(fs.existsSync(beat)?fs.readFileSync(beat,'utf8'):'',first,'descendant still alive after spontaneous CLI exit');await s.close();
});
