import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdtempSync,mkdirSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {createHash} from 'node:crypto';
import {interfaceBlocks,proseSha256,fillHashes} from '../src/runtime-preflight.mjs';
const path='prompts/cli/workflow-runner.prompt.md';
// Local checks accept either status. Pin both complete declarations.
const acceptedShapes={approved:'553ec45b71833be1c7b97cde0d888c62a14eac565907c176af509e0339f105e7',draft:'26bcd39d3f1475f9dfabadbfa868b1128891e0680d0881fac6f2115e12a87487'};
const shape=doc=>{const value=structuredClone(doc);value.prose_sha256='';return createHash('sha256').update(JSON.stringify(value)).digest('hex');};
function checked(text,status) {
 const blocks=interfaceBlocks(text);assert.equal(blocks.length,1);const doc=JSON.parse(blocks[0][1]);
 assert.deepEqual(doc.entries.map(e=>e.operation),['changeRun','acknowledgeRequest','storyCount','runStatus']);assert.deepEqual(doc.resources.map(r=>r.name),['source','runs','files','program','results']);
 assert.ok(Object.hasOwn(acceptedShapes,doc.status));
 if(status!==undefined)assert.equal(doc.status,status);
 assert.equal(shape(doc),acceptedShapes[doc.status],'all accepted declarations, including current appMap schemas, remain exact');
 const withoutFences=text.replace(/```[^\n]*\n[\s\S]*?\n```/g,'');
 const stray=withoutFences.split('\n').filter(line=>{try{const value=JSON.parse(line);return value&&Array.isArray(value.entries)&&Array.isArray(value.resources);}catch{return false;}});assert.deepEqual(stray,[],'no stale second program declaration outside the canonical block');
 return doc;
}
test('runner has one draft or approved declaration with the accepted complete native interface',()=>{
 const text=readFileSync(new URL('../'+path,import.meta.url),'utf8'),doc=checked(text);assert.equal(doc.prose_sha256,proseSha256(text));
});
test('ordinary local draft hash fill preserves the whole authoritative interface',t=>{
 const root=mkdtempSync(join(tmpdir(),'pdd-origin-interface-'));t.after(()=>rmSync(root,{recursive:true,force:true}));mkdirSync(join(root,'prompts','cli'),{recursive:true});
 const original=readFileSync(new URL('../'+path,import.meta.url),'utf8');checked(original);
 const block=interfaceBlocks(original)[0][1],draft=JSON.parse(block);draft.status='draft';
 writeFileSync(join(root,path),original.replace(block,JSON.stringify(draft))+'\nAdditional controlled prose for local hash replay.\n');
 const result=fillHashes({root,files:[path]});assert.equal(result.filled.length,1);assert.deepEqual(result.refused,[]);assert.deepEqual(result.stale,[]);
 const filled=readFileSync(join(root,path),'utf8'),doc=checked(filled,'draft');assert.equal(doc.prose_sha256,proseSha256(filled));
});
