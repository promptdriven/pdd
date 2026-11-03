import assert from 'node:assert/strict';
import {mkdirSync,writeFileSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {execFile as callbackExec,execFileSync} from 'node:child_process';
import {promisify} from 'node:util';
import {fixture} from './workflow-delivery-fixture.mjs';
import {startRun} from '../../src/workflow-runner.mjs';
const exec=promisify(callbackExec),packageRoot=resolve(import.meta.dirname,'../..');
export async function adoptedCorpusRun(t,{adopt=true,multi=false,start=true}={}) {
  const f=await fixture(t,{name:'replay',agent:'codex'});
  const skill=join(f.source,'.agents/skills/pdd-replay');mkdirSync(skill,{recursive:true});
  const code={name:'code',steps:['verify'],gate:'pr',replay_evidence:'pdd.replay-evidence.v1'};
  writeFileSync(join(skill,'workflow.json'),JSON.stringify({version:2,areas:multi?[{name:'story',steps:['scope'],gate:'approve'},{name:'prompt',steps:['check'],gate:'pr',before:'approve',then:'ask-code'},code]:[code]}));
  mkdirSync(join(f.source,'tests'));mkdirSync(join(f.source,'prompts'));mkdirSync(join(f.source,'rules'));
  writeFileSync(join(f.source,'prompts/add.prompt.md'),'# Add\n## Dependencies\n[Rule](../rules/add.md)\n');writeFileSync(join(f.source,'rules/add.md'),'Addition rule.\n');
  const vector={schema_version:'prompt-runtime.program-scenario.v1',steps:[{step_id:'add',entry_path:'prompts/add.prompt.md',operation:'add',checks:[{criterion_id:'AC1',target:'result',path:'/total',op:'equals',value:3}]}]};
  writeFileSync(join(f.source,'tests/add.json'),JSON.stringify(vector));
  f.git(f.source,'add','.');f.git(f.source,'commit','-qm','Approved synthetic corpus');const commit=f.git(f.source,'rev-parse','HEAD');f.git(f.source,'update-ref','refs/remotes/origin/main',commit);
  const declaration=join(f.base,'adoption.json');writeFileSync(declaration,JSON.stringify({schema_version:'pdd.replay-adoption.v1',repository:'example/project',commit,prompts:['prompts/add.prompt.md'],scenarios:['tests/add.json'],approval:{kind:'external-human-assertion',reference:'review:fixture',asserted_by:'Synthetic human'}}));
  // Keep the canonical origin; perform real fetch/push/ls-remote against a local bare
  // server through a transport-only URL substitution. gh/Herdr remain boundary fakes.
  const bare=join(f.base,'remote.git');execFileSync('git',['init','--bare','-q',bare]);f.git(f.source,'push','-q',bare,'HEAD:refs/heads/main');
  const original=f.ports.execFile;
  f.ports.execFile=async(file,args,options)=>{
    if(file==='git'&&['fetch','push','ls-remote'].includes(args[0])) {
      if(args[0]==='push')f.pushes.push(args);
      return exec('git',['-c',`url.${bare}.insteadOf=https://github.com/example/project.git`,...args],{...options,encoding:'utf8'});
    }
    return original(file,args,options);
  };
  const begin=()=>startRun({name:'replay',issue:'17',agent:'codex',cwd:f.source,packageRoot,...(adopt?{adoptCorpus:declaration}:{})},f.ports);
  if(start){const out=await begin();assert.equal(out.exitCode,0,out.message);if(adopt)assert.match(out.message,/external-assertion-unverified/);}
  return {f,declaration,vector,commit,begin,bare};
}
