import * as fs from 'node:fs';
import {join,dirname,resolve} from 'node:path';
import {tmpdir} from 'node:os';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import {proseSha256} from '../../src/runtime-preflight.mjs';
export const implementation=resolve(dirname(fileURLToPath(import.meta.url)),'../../src/runtime-client.mjs');
export const read=(root,path)=>fs.readFileSync(join(root,path),'utf8');
export const write=(root,path,text)=>{fs.mkdirSync(dirname(join(root,path)),{recursive:true});fs.writeFileSync(join(root,path),text);};
export const json=(root,path,value)=>write(root,path,JSON.stringify(value,null,2)+'\n');
export const get=(root,path)=>JSON.parse(read(root,path));
export function fixture(t,{bounded=true}={}){
  const temporary=fs.mkdtempSync(join(tmpdir(),'pdd-workspace-')),parent=fs.realpathSync(temporary),root=join(parent,'repo'),state=join(parent,'state');fs.mkdirSync(root);
  t.after(()=>fs.rmSync(temporary,{recursive:true,force:true}));
  const git=spawnSync('git',['init','-q'],{cwd:root});if(git.status!==0)throw Error('fixture git init failed');
  const story='simulation/user_stories/order.md',prompt='simulation/prompts/order.prompt.md',test='simulation/tests/order.json',second='simulation/tests/order.second.json';
  write(root,story,'# Order\n\nI can keep my values.\n\n## Acceptance criteria\n\n1. Keep value.\n');
  let text='# Order\n\nReturn the value.\n\n## Dependencies\n\n<details><summary>Runtime interface</summary>\n```json\n'+JSON.stringify({status:'draft',prose_sha256:'',entries:[{operation:'order',input_schema:{type:'object',properties:{},required:[],additionalProperties:false},result_schema:{type:'integer'},errors:[]}],calls:[],resources:[],limits:{max_steps:1,max_model_calls:1},conventions:[]})+'\n```\n</details>\n';
  text=text.replace('"prose_sha256":""','"prose_sha256":"'+proseSha256(text)+'"');write(root,prompt,text);
  const doc={schema_version:'prompt-runtime.program-scenario.v1',story_path:story,criteria:[{id:'AC1',text:'Keep value.'}],initial_world:{count:0},simulation:{},context:[],steps:[{step_id:'prior',entry_path:prompt,operation:'order',input:{},checks:[{criterion_id:'AC1',target:'result',path:'',op:'equals',value:7},{criterion_id:'AC1',target:'world',path:'',op:'equals',value:{count:0}}]}]};
  json(root,test,doc);json(root,second,doc);write(root,'private/ordinary.md','PRIVATE-MARKER');
  if(bounded)json(root,'pdd-workspace.json',{allowed_paths:['simulation/']});
  const env={...process.env,PDD_STATE_DIR:join(temporary,'state')};
  const saved=(id='case-A',extra={})=>({id,name:id,story_path:story,original_path:second,world_before:{count:0},test:{...doc,steps:[{step_id:id,entry_path:prompt,operation:'order',input:{},checks:[{criterion_id:'AC1',target:'result',path:'',op:'equals',value:9},{criterion_id:'AC1',target:'world',path:'',op:'equals',value:{count:0}}]}]},...extra});
  return{parent,root,state,env,story,prompt,test,second,doc,saved};
}
export function pendingId(message){return message.match(/pending ([a-f0-9]{64}\.[a-f0-9]{64})/)?.[1];}
export const stream=()=>({text:'',write(text){this.text+=text;},isTTY:false});
export function cases(story){return JSON.parse(fs.readFileSync(new URL(`../runtime-workspace/${story}-cases.json`,import.meta.url),'utf8')).cases;}
export const closed=testPath=>({kind:'closed-editor',testPath});
