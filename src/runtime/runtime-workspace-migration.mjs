// Generated from prompts/cli/runtime/runtime-workspace-migration.prompt.md (sha256: 81702dedf96119cffdab11a1ba923a79b7b3d5966dcfea0d77cb34c38867552a).
// Implements prompts/cli/runtime/runtime-workspace-migration.prompt.md.
import {realpathSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {loadRuntimeWorkspace,requireRuntimePath} from './runtime-workspace.mjs';
import {captureSource,sourceFilePort,gitFiles} from './runtime-preflight.mjs';
import {runtimeWorkspaceMigrationStore,acquireCaseWriteOwnership,applyPendingCase} from './runtime-client.mjs';
import {readEvidenceEligibility} from '../workflow-runner.mjs';
const digest=value=>createHash('sha256').update(JSON.stringify(value)).digest('hex');
const safe=path=>typeof path==='string'&&path&&!/[\\\x00-\x1f*?]/.test(path)&&!path.startsWith('/')&&!path.split('/').some(p=>!p||p==='.'||p==='..'||p==='.git');
export async function migrateRuntimeWorkspace({root,projectionRoot,mappings,write=false,signal},ports={}){
  const canonical=ports.realpath??realpathSync;root=canonical(root);projectionRoot=canonical(projectionRoot);
  const result={state:write?'applied':'preview',mappings:Array.isArray(mappings)?mappings.map(x=>({...x})):[],items:[],unresolved:[]};
  const unresolved=(id,reason,recoveryPath=null)=>{result.unresolved.push({id,reason,recoveryPath});if(write)result.state='incomplete';};
  if(!Array.isArray(mappings)||mappings.some(m=>!m||Object.keys(m).length!==2||!safe(m.from)||!safe(m.to))||new Set(mappings.map(m=>m.from)).size!==mappings.length||new Set(mappings.map(m=>m.to)).size!==mappings.length){unresolved('mappings','exact unique safe from/to file mappings are required');result.state='incomplete';return result;}
  const map=new Map(mappings.map(m=>[m.from,m.to])),policy=(ports.loadRuntimeWorkspace??loadRuntimeWorkspace)({root}),store=ports.store??runtimeWorkspaceMigrationStore({root,projectionRoot,env:ports.env});
  const source=ports.sourceFilePort??sourceFilePort,capture=ports.captureSource??captureSource,eligibility=ports.readEvidenceEligibility??readEvidenceEligibility;
  let oldFiles,newFiles;
  try{oldFiles=source(projectionRoot,new Set((ports.gitFiles??gitFiles)(projectionRoot)));newFiles=source(root,new Set((ports.gitFiles??gitFiles)(root)));}
  catch(error){unresolved('source',error.message);result.state='incomplete';return result;}
  const checks=new Map();
  for(const {from,to} of mappings){try{requireRuntimePath(policy,{path:to,from});const before=oldFiles.read({path:from}).content,after=newFiles.read({path:to}).content;if(before!==after)throw Error('mapped authored bytes differ; repair the authored source without changing expectations');checks.set(from,true);}catch(error){checks.set(from,false);unresolved(from,error.message);}}
  let inventory;try{inventory=await store.inventory();}catch(error){unresolved('private-state',error.message);result.state='incomplete';return result;}
  const migrationId=(ports.hash??digest)({root,projectionRoot,mappings});
  for(const item of inventory){
    if(signal?.aborted){unresolved(item.id,'migration cancelled; originals and prepared records retained',item.id);if(write)result.state='incomplete';break;}
    const outcome={id:item.id,kind:item.kind,state:'ready',reason:null,recoveryPath:item.id};result.items.push(outcome);
    const record=item.record;
    try{
      const selected=item.kind==='case'?[record.identity?.original?.path]:Array.isArray(record.rows)?record.rows.map(row=>row.test):item.kind==='repo'?Object.keys(record.tries??{}):[record.originalPath??record.test].filter(Boolean);
      if(!selected.length)throw Error('owned source selection is unavailable; preserve the original recovery command');
      for(const path of selected)if(!map.has(path)||!checks.get(path))throw Error(`missing or incompatible exact source mapping: ${path}`);
      const oldCapture=capture(projectionRoot,{tests:selected,appMap:null}),newCapture=capture(root,{tests:selected.map(p=>map.get(p)),appMap:null});
      // Compare the complete closure. Each raw/effective member and used reference
      // must have an explicit exact destination, never a prefix assumption.
      for(const file of oldCapture.sources){const target=map.get(file.path);if(!target||!checks.get(file.path))throw Error(`required source mapping is unresolved: ${file.path}`);const next=newCapture.sources.find(f=>f.path===target);if(!next||!Buffer.from(file.bytes).equals(Buffer.from(next.bytes)))throw Error(`effective source/reference meaning changed: ${file.path}`);}
      if(newCapture.sources.length!==oldCapture.sources.length)throw Error('complete selected source closure differs');
      const owner=eligibility({root,producerRoot:projectionRoot,tests:selected,source_sha256:record.source_sha256??oldCapture.sha256,runId:record.runId??null,stage:record.association?.stage??null},ports.evidencePorts??{});
      outcome.eligibility=owner;outcome.selected=selected;outcome.readCommand=record.readCommand??(record.batch?`pdd test --read ${record.batch}`:record.id?`pdd test --read ${record.id}`:null);
      if(owner.state!=='eligible')throw Error(`evidence/source ownership ${owner.state}: ${owner.reason}`);
      // Archive names are part of source identity, even when mapped bytes agree.
      if(oldCapture.sha256!==newCapture.sha256)throw Error('mapped archive identity changed; historical evidence cannot establish the authored current source');
      if(!write)continue;
      const previous=store.readMapping(migrationId);const done=previous?.items?.[item.id];if(done?.state==='applied'){outcome.state='applied';continue;}
      let lease;try{
        const testPath=map.get(selected[0]),handoff=await ports.handoff?.({root,testPath,signal});
        lease=await (ports.acquireCaseWriteOwnership??acquireCaseWriteOwnership)({root,testPath,handoff,signal},{env:ports.env,...ports.ownershipPorts});
        const prepared={schema_version:'pdd.workspace-migration.v1',root,projectionRoot,mappings,activeItem:item.id,items:{...(previous?.items??{}),[item.id]:{state:'prepared',kind:item.kind,original:item.raw,record:item.record,selected,eligibility:owner,readCommand:outcome.readCommand}}};
        const location=store.publishMapping(migrationId,prepared);outcome.recoveryPath=location;
        await ports.fault?.('prepared',item);
        if(signal?.aborted){outcome.state='pending';outcome.reason='migration cancelled before publication';unresolved(item.id,outcome.reason,location);break;}
        if(item.kind==='case'){
          const retained=store.transferCase({...item,mappedStory:map.get(record.identity.original.storyPath)},testPath);
          {
            const applied=await (ports.applyPendingCase??applyPendingCase)({root,pendingId:retained.pendingId,writeOwnership:lease,signal},{env:ports.env,...ports.casePorts});
            if(applied.state!=='committed'){outcome.state=applied.state;outcome.reason=applied.reason;unresolved(item.id,applied.reason,applied.recoveryPath);continue;}
          }
        }
        const committed={...prepared,items:{...prepared.items,[item.id]:{...prepared.items[item.id],state:'applied'}}};
        await ports.fault?.('before-publication',item);if(signal?.aborted){outcome.state='pending';unresolved(item.id,'migration cancelled before publication',location);break;}
        store.publishMapping(migrationId,committed);
        await ports.fault?.('published',item);
        const actual=store.readMapping(migrationId);
        if(actual?.items?.[item.id]?.state!=='applied')throw Error('mapping publication is uncertain; retained recovery record required');
        outcome.state='applied';
      }catch(error){const actual=store.readMapping(migrationId);if(actual?.items?.[item.id]?.state==='applied')outcome.state='applied';else throw error;}
      finally{lease?.release();}
    }catch(error){outcome.state=signal?.aborted?'pending':'unavailable';outcome.reason=error.message;unresolved(item.id,error.message,outcome.recoveryPath);}
  }
  if(result.unresolved.length)result.state='incomplete';return result;
}
