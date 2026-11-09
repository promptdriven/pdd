// Generated from prompts/test/autopilot-factory.prompt.md.
import '../test-home.mjs';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,readFileSync,writeFileSync,rmSync,existsSync,readdirSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join,resolve,dirname} from 'node:path';
import {fork,execFileSync,execFile} from 'node:child_process';
import {createHash,randomUUID} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {fakeHerdr} from '../fake-herdr.mjs';
import {analysisFor} from '../autopilot-github-world.mjs';
import {factoryGithub} from './github.mjs';
import {factoryInterpreter} from './interpreter.mjs';

export const packageRoot=resolve(import.meta.dirname,'../../..');
export const readJson=path=>JSON.parse(readFileSync(path,'utf8'));
export const put=(root,path,value)=>{mkdirSync(dirname(join(root,path)),{recursive:true});writeFileSync(join(root,path),typeof value==='string'?value:JSON.stringify(value,null,2)+'\n');};
export const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
export const scenario={schema_version:'prompt-runtime.program-scenario.v1',story_path:'user_stories/value.md',criteria:[{id:'AC1',text:'The value is 2.'}],initial_world:{},simulation:{},context:[],steps:[{step_id:'value',entry_path:'value.prompt.md',operation:'value',input:{},checks:[{criterion_id:'AC1',target:'result',path:'/value',op:'equals',value:2}]}]};
export function valuePrompt(value) {
  return `# Value\nReturn the value ${value}.\n\n## Dependencies\n\n<details><summary>Runtime interface</summary>\n\`\`\`json\n${JSON.stringify({status:'draft',prose_sha256:'',entries:[{operation:'value',input_schema:{type:'object',properties:{},required:[],additionalProperties:false},result_schema:{type:'object',properties:{value:{type:'integer'}},required:['value'],additionalProperties:false},errors:[]}],calls:[],resources:[],limits:{max_steps:1,max_model_calls:1},conventions:[]})}\n\`\`\`\n</details>\n`;
}

export async function factoryWorld(t,{workflow='small-change',repository='example/project',shared}={}) {
  const base=mkdtempSync(join(tmpdir(),'pdd-factory-world-'));
  const w={repository,sessionName:shared?.sessionName??process.env.PDD_FACTORY_HERDR_SESSION??`pdd-factory-${randomUUID()}`,base,cwd:join(base,'repo'),home:shared?.home??join(base,'home'),remote:join(base,'origin.git'),mergeCheckout:join(base,'merge'),workflow,time:Date.now(),commands:[],warnings:[],alerts:[],packets:[],dependencyRequests:[],seenCalls:0,children:new Set()};
  Object.defineProperty(w,'leadActions',{get:()=>w.commands.filter(c=>!['agent','worker','coordinator','operator','timer','person','other-worker','old-coordinator','resend-child','checker'].includes(c.actor))});
  for(const dir of [w.cwd,w.home,join(base,'bin')])mkdirSync(dir,{recursive:true});
  for(const name of ['gh','herdr','codex','claude','gemini','agy','curl','wget'])writeFileSync(join(base,'bin',name),'#!/bin/sh\necho factory-external-program-denied >&2\nexit 97\n',{mode:0o700});
  writeFileSync(join(base,'bin/gh'),'#!/bin/sh\nif [ \"$1\" = auth ] && [ \"$2\" = token ]; then echo factory-token; elif [ \"$1\" = api ] && [ \"$2\" = user ]; then echo \"example 1\"; else echo factory-native-gh-denied >&2; exit 97; fi\n',{mode:0o700});
  w.env={CI:'1',HOME:w.home,USERPROFILE:w.home,PATH:join(base,'bin')+':'+dirname(process.execPath)+':/usr/bin:/bin',XDG_CONFIG_HOME:join(base,'config'),PDD_STATE_DIR:join(base,'runtime'),PDD_INTERPRETER_QUEUE:join(base,'interpreter-queue'),PDD_SUITE_QUEUE:join(base,'suite-queue'),PDD_INTERPRETER_CONCURRENCY:'1',GIT_CONFIG_NOSYSTEM:'1',GIT_CONFIG_GLOBAL:'/dev/null',GIT_ALLOW_PROTOCOL:'file',LANG:'C.UTF-8'};
  w.git=(cwd,...a)=>execFileSync('git',a,{cwd,env:w.env,encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim();
  w.git(w.cwd,'init','-q','-b','main');w.git(w.cwd,'config','user.email','factory@example.invalid');w.git(w.cwd,'config','user.name','Factory');
  put(w.cwd,'pdd.json',{autopilot:{mode:'auto',trust:['example'],base:'main',parking:{hours:24,maxParked:20}}});
  put(w.cwd,'value.mjs','export const value = 1;\n');put(w.cwd,'value.prompt.md',valuePrompt(1));
  put(w.cwd,'CONTRIBUTING.md','Run node --test test/value.test.mjs. Open PRs against main.\n');
  put(w.cwd,'package.json',{type:'module',scripts:{test:'node --test test/value.test.mjs'}});
  w.git(w.cwd,'add','.');w.git(w.cwd,'commit','-qm','Initial synthetic project');
  w.git(base,'clone','-q','--bare',w.cwd,w.remote);w.git(w.cwd,'remote','add','origin',`https://github.com/${repository}.git`);
  w.git(w.cwd,'fetch','-q',w.remote,'main:refs/remotes/origin/main');
  w.git(base,'clone','-q',w.remote,w.mergeCheckout);w.git(w.mergeCheckout,'config','user.email','factory@example.invalid');w.git(w.mergeCheckout,'config','user.name','Factory');
  w.commonDir=w.git(w.cwd,'rev-parse','--path-format=absolute','--git-common-dir');
  w.stateRoot=join(w.home,'.local/state/pdd/autopilot');w.stateDir=join(w.home,'.local/state/pdd');w.layoutDirectory=join(w.stateDir,'herdr-layout');
  w.stateFile=join(w.stateRoot,sha(w.cwd).slice(0,20)+'.json');
  w.state=()=>readJson(w.stateFile);
  w.record=(number=17)=>readJson(join(w.commonDir,`pdd/runs/${number}/status.json`));
  w.github=factoryGithub(w);w.interpreter=factoryInterpreter();w.herdr=shared?.herdr??fakeHerdr();w.herdr.now=()=>w.time;
  const externalHerdr=async a=>{
    if(a[0]==='status')return {...await w.herdr.herdr(a),session:w.sessionName};
    if(a[0]==='pane'&&a[1]==='get') {
      const p=w.herdr.panes.find(p=>p.pane_id===a[2]);if(!p)throw Object.assign(Error('pane_not_found'),{code:'pane_not_found'});
      return {result:{pane:{...p,agent:p.agent?.agent,agent_status:p.agent?.agent_status,agent_session:p.agent?.agent_session,foreground_cwd:p.cwd}}};
    }
    const sessionsBefore=w.herdr.sessions.length;
    const result=await w.herdr.herdr(a);
    if(a[0]==='pane'&&a[1]==='run') {
      const p=w.herdr.panes.find(p=>p.pane_id===a[2]);
      if(a[3].includes("codex")) {
        const resumed=/\bresume '?([0-9a-f-]{36})/.exec(a[3])?.[1];
        const id=resumed??randomUUID();
        const name=p.agent?.name;
        p.agent={agent:'codex',agent_status:'idle',agent_session:{agent:'codex',kind:'id',value:id},prompts:[],...(name?{name}:{})};
        w.herdr.sessions.splice(sessionsBefore);
        if(!w.herdr.sessions.some(s=>s.id===id&&s.root===p.cwd))w.herdr.sessions.push({agent:'codex',id,root:p.cwd,at:w.time});
      }
    }
    return result;
  };
  w.execute=async(file,a,o={})=>{
    if(file==='gh') {
      const other=shared && (o.cwd?.startsWith(shared.base) || a.some(arg=>String(arg).includes(shared.repository)));
      return (other?shared.github:w.github).gh(a,o);
    }
    if(file==='herdr') {
      if(a[0]==='--version')return {code:0,stdout:'1.0.0',stderr:''};
      const args=a[0]==='--session'?a.slice(2):a;
      return {code:0,stdout:JSON.stringify(await externalHerdr(args)),stderr:''};
    }
    if(file===process.execPath && a[0]?.endsWith('/bin/pdd.mjs')) {
      const r=await w.command(a.slice(1),{cwd:o.cwd,env:o.env,allowFailure:true,actor:'resend-child'});
      return {code:r.code,stdout:r.stdout,stderr:r.stderr};
    }
    assert.equal(file,'git',`external program denied: ${file}`);
    assert.ok(o.cwd?.startsWith(base) || shared && o.cwd?.startsWith(shared.base),'Git must stay in the factory');
    if(shared && o.cwd?.startsWith(shared.base))return shared.execute(file,a,o);
    if(a[0]==='push'||a[0]==='fetch'||a[0]==='ls-remote')a=['-c',`url.${w.remote}.insteadOf=https://github.com/${repository}.git`,...a];
    return new Promise((done,reject)=>{
      const child=execFile('git',a,{cwd:o.cwd,env:w.env,encoding:o.encoding??'utf8',maxBuffer:o.maxBuffer??32*1024*1024},(error,stdout,stderr)=>{
        if(!error && a.includes('push'))w.github.syncHeads();
        if(error && !Number.isInteger(error.code))reject(error);else done({code:error?.code??0,stdout,stderr});
      });
      child.stdin.on('error',()=>{});child.stdin.end(o.input);
    });
  };
  w.command=async(argv,{cwd=w.cwd,actor='agent',env={},stdin,allowFailure=false,operation}={})=>{
    const child=fork(fileURLToPath(new URL('./worker.mjs',import.meta.url)),[],{cwd:base,env:{...w.env,...env,GIT_CONFIG_COUNT:'1',GIT_CONFIG_KEY_0:`url.${w.remote}.insteadOf`,GIT_CONFIG_VALUE_0:`https://github.com/${repository}.git`},execArgv:[],stdio:['ignore','pipe','pipe','ipc'],serialization:'advanced'});
    w.children.add(child);
    let processOut='',processErr='';child.stdout.on('data',s=>{processOut+=s;});child.stderr.on('data',s=>{processErr+=s;});
    const request={base,cwd,packageRoot,stateRoot:w.stateRoot,stateDir:w.stateDir,layoutDirectory:w.layoutDirectory,env:{...w.env,PDD_RUNTIME_URL:w.interpreter.origin,...env},argv,stdin,operation,stateFile:w.stateFile,now:w.time};
    const result=await new Promise((done,reject)=>{
      let settled=false;
      const timer=setTimeout(()=>{child.kill('SIGTERM');reject(Error(`factory command deadline: ${argv?.join(' ')??operation}`));},25000);
      const finish=(err,value)=>{if(settled)return;settled=true;clearTimeout(timer);if(child.connected)child.disconnect();err?reject(err):done(value);};
      child.on('error',err=>finish(err));child.on('exit',code=>{w.children.delete(child);if(!settled)finish(Error(`factory worker exited ${code}: ${processErr}`));});
      child.on('message',async m=>{
        if(m.done){finish(null,m.done);return;}
        if(m.failed){finish(Error(m.failed.stack));return;}
        if(!m.id)return;
        try {
          let value;
          if(m.method==='exec')value=await w.execute(...m.args);
          else if(m.method==='herdr')value=await externalHerdr(...m.args);
          else if(m.method==='sessions')value=await w.herdr.findNativeSessions(...m.args);
          else if(m.method==='warning')w.warnings.push(m.args[0]);
          else if(m.method==='runtimeHealth')value={state:w.interpreter.mode==='refused'?'unavailable':'healthy',detail:'factory interpreter program'};
          else if(m.method==='alert'){w.alerts.push(m.args[0]);value={exitCode:0};}
          else if(m.method==='sleep'){w.time+=Math.min(m.args[0],1000);await new Promise(r=>setTimeout(r,1));}
          else if(m.method==='fetch') {
            const [url,o]=m.args;let body;
            if(o.payload){body=new FormData();body.set('request',new Blob([o.payload.request]));body.set('source',new Blob([o.payload.tar]));}
            const r=await w.interpreter.fetch(url,{method:o.method,body});value={body:await r.text(),status:r.status,headers:Object.fromEntries(r.headers)};
          } else assert.fail(`unknown factory port ${m.method}`);
          if(child.connected)child.send({reply:m.id,value});
        } catch(error){if(child.connected)child.send({reply:m.id,error:{message:error.message,code:error.code,stdout:error.stdout,stderr:error.stderr}});}
      });
      child.send({start:request});
    });
    if(child.exitCode===null && child.signalCode===null)await new Promise(r=>child.once('exit',r));
    result.nativeOutput=processOut;
    w.time=Math.max(w.time,result.time)+100;w.herdr.idle();
    w.commands.push({actor,pid:child.pid,argv:argv??['tick'],code:result.code,stdout:result.stdout,stderr:result.stderr});
    if(!allowFailure)assert.equal(result.code,0,`${actor}: pdd ${argv?.join(' ')??'tick'}\n${result.stdout}\n${result.stderr}\n${w.warnings.slice(-3).join('\n')}`);
    return result;
  };
  w.tick=()=>w.command(undefined,{operation:'tick',actor:'timer'});
  w.context=()=>{const s=w.state();return {PDD_AUTOPILOT_CONTEXT:JSON.stringify(s.ownerLaunch.coordinator),HERDR_PANE_ID:s.paneId,HERDR_SOCKET_PATH:join(base,'sessions/pdd-autopilot/socket')};};
  w.messages=()=>{
    const calls=w.herdr.calls.slice(w.seenCalls);w.seenCalls=w.herdr.calls.length;
    for(const a of calls)if(a[0]==='agent'&&a[1]==='prompt') {
      const path=/Artifact path: (.+)/.exec(a.at(-1))?.[1];
      const text=path?readFileSync(JSON.parse(path),'utf8'):a.at(-1);
      if(text.includes('snapshotJson')) {try {const value=JSON.parse(text.trim().split('\n').at(-1));if(value.snapshotJson)w.dependencyRequests.push(value);}catch{}}
      try {const value=JSON.parse(text.trim().split('\n').at(-1));if(value.repository&&value.issues)w.packets.push(value);}catch{}
    }
  };
  w.start=async()=>{await w.command(['autopilot','start','--runs','2','--checks','1'],{actor:'operator'});w.messages();};
  w.reviewDependencies=async()=>{
    w.messages();
    for(let n=0;n<8;n++) {
      const request=w.dependencyRequests.shift();if(!request)break;
      await w.command(['dependencies','complete','--input','-'],{actor:'coordinator',env:w.context(),stdin:JSON.stringify({request,analysis:analysisFor(request)})});w.messages();
    }
  };
  w.begin=async({beforeRun,number=17}={})=>{
    await w.start();await w.reviewDependencies();await w.tick();w.messages();
    const packet=[...w.packets].reverse().find(p=>p.issues.some(i=>i.number===number&&i.eligible));
    assert.ok(packet,`GAP intake: no eligible work packet; ${w.commands.at(-1)?.stdout}; ${w.warnings.join('; ')}`);
    const issue=packet.issues.find(i=>i.number===number);
    await w.github.gh(['issue','edit',String(number),'--add-label','pdd:working']);
    const event=w.github.issues.get(number).timeline.at(-1);
    await w.github.gh(['issue','comment',String(number),'--body-file','-'],{input:'Factory coordinator claim.\n\n```json\n'+JSON.stringify({repository:packet.repository,coordinatorId:packet.coordinatorId,machine:packet.machine,labelEventId:String(event.id),lastSeen:new Date(w.time).toISOString()})+'\n```'});
    w.runArgs=['workflow','run',workflow,String(number),'--agent','codex','--origin','autopilot','--decision-id',issue.decisionId,'--outcome','code'];
    if(beforeRun)await beforeRun(w);
    await w.command(['workflow','run',workflow,String(number),'--agent','codex','--origin','autopilot','--decision-id',issue.decisionId,'--outcome','code'],{actor:'coordinator',env:w.context()});
  };
  t.after(()=>{for(const child of w.children)child.kill('SIGTERM');rmSync(base,{recursive:true,force:true});});
  return w;
}
