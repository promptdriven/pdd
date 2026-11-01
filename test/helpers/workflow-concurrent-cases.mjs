import {readFileSync} from 'node:fs';
import assert from 'node:assert/strict';
export const inventory=JSON.parse(readFileSync(new URL('../workflow-concurrent-progress/cases.json',import.meta.url)));
export function nativeCase(id){const row=inventory.cases.find(row=>row.id===id);assert.ok(row,`native inventory case ${id}`);return row;}
export function observations(label,checks){
 const results=Object.fromEntries(Object.entries(checks).map(([name,check])=>{try{check();return [name,true];}catch(error){return [name,{code:error.code,message:error.message}];}}));
 console.log(JSON.stringify({case:label,observations:results}));
 assert.deepEqual(Object.entries(results).filter(([,result])=>result!==true).map(([name])=>name),[],label);
}
