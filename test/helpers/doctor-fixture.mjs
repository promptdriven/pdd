import {join} from 'node:path';
// Complete synthetic read-only observations. No machine program or file read.
export function doctorFixture({cwd='/project',home='/home/fake',packageRoot='/install',kind='codex',platform='linux'} = {}) {
  const calls=[], paths=new Map();
  const input={cwd,packageRoot,env:{HOME:home,PATH:'/tools',XDG_CONFIG_HOME:join(home,'config')}};
  paths.set(join(cwd,'AGENTS.md'),'<!-- pdd:start -->\nUse PDD\n<!-- pdd:end -->');
  paths.set(join(cwd,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  for (const skill of ['pdd-prompting','pdd-setup','pdd-small-change','pdd-bug','pdd-feature','pdd-product','pdd-graph','pdd-autopilot','pdd-check','pdd-merge']) paths.set(join(home,kind==='claude'?'.claude':'.agents','skills',skill,'SKILL.md'),'skill');
  const answer=(stdout='',code=0)=>({code,stdout,stderr:''});
  const f={input,calls,paths,answer,limited:false,signedIn:true,permission:'WRITE',rules:[],panes:[],coordinatorPanes:[],server:true,merge:true};
  const run=async(file,args,options)=>{
    calls.push({file,args,options});
    if(file==='/tools/pdd')return answer(args[0]==='--version'?'0.1.27':'pdd autopilot start');
    if(file==='git')return answer(args[0]==='--version'?'git version 2.48':args[0]==='remote'?(f.origin??'https://github.com/example/project.git'):args[0]==='ls-files'?(f.tracked??''):cwd);
    if(file==='gh') {
      if(args[0]==='--version')return answer('gh version 2.60');
      if(args[0]==='auth')return answer(args[1]==='token'?'FAKE_TOKEN':'');
      if(args[0]==='repo')return answer(JSON.stringify({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},viewerPermission:f.permission,mergeCommitAllowed:f.merge}));
      if(args[0]==='api')return answer(JSON.stringify(f.rules));
    }
    if(file===kind) return kind==='claude'?answer(JSON.stringify({loggedIn:f.signedIn}),f.signedIn?0:1):answer(f.signedIn?'Logged in using ChatGPT':'Not logged in',f.signedIn?0:1);
    if(file==='herdr') {
      if(args[0]==='--version')return answer('1.0');
      if(args[0]!=='--session')throw Error('Herdr session is required');
      const session=args[1],command=args.slice(2);
      if(!['pdd','pdd-autopilot'].includes(session))throw Error('Unknown Herdr session');
      const panes=session==='pdd'?f.panes:f.coordinatorPanes;
      if(command[0]==='status')return answer(JSON.stringify({running:f.server,session}));
      if(command[0]==='pane'&&command[1]==='list')return answer(JSON.stringify({result:{type:'pane_list',panes}}));
      if(command[0]==='agent'&&command[1]==='get') {
        const agent=panes.find(p=>p.pane_id===command[2]);
        return answer(JSON.stringify(agent?{result:{type:'agent_info',agent}}:{error:{code:'agent_not_found'}}),agent?0:1);
      }
      throw Error(`Unexpected Herdr command: ${args}`);
    }
    if(file==='systemctl'||file==='launchctl')return answer();
    if(file==='loginctl')return answer('yes');
    if(file==='pmset')return answer('Battery Power:\n sleep 0\nAC Power:\n sleep 0\n');
    throw Error(`Unexpected doctor command: ${file} ${args}`);
  };
  const files={
    readFileSync:path=>{if(paths.has(path))return paths.get(path);throw Object.assign(Error('missing'),{code:'ENOENT'});},
    accessSync:path=>{if(path!=='/tools/pdd')throw Error('missing');},
    statSync:()=>({isFile:()=>true}),
    realpathSync:path=>path==='/tools/pdd'?join(packageRoot,'bin/pdd.mjs'):path,
  };
  f.ports={run,files,platform,uid:501,nodeVersion:'22.20.0',nodePath:'/node',agentDefinitions:()=>[{id:kind,kind,command:kind,env:{}}],codexLimits:async()=>({state:f.limited?'limited':'healthy'}),fetch:async(url,options)=>{calls.push({url:String(url),options});return new Response('{}',{status:200});}};
  return f;
}
// Existing launcher tests isolate their new preflight as well as their old ports.
export function healthyDoctorPorts(input) {
  const f=doctorFixture({cwd:input.cwd,home:input.env?.HOME,packageRoot:input.packageRoot});
  const run=f.ports.run;
  f.ports.files.accessSync=()=>{};
  f.ports.files.realpathSync=()=>'/same-install';
  f.ports.run=(file,args,opts)=>file.endsWith('/pdd')?Promise.resolve(f.answer(args[0]==='--version'?'0.1.27':'pdd autopilot start')):run(file,args,opts);
  return f.ports;
}
