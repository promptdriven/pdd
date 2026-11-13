import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {productTapCallBound} from '../../src/runtime/product-composition.mjs';
const schema={type:'object',properties:{},required:[],additionalProperties:false};
function boundFixture(cap,childCalls,childCap=1,drawCap=1){
 const files={};
 const put=(path,iface)=>{files['/project/'+path]='# Fixture\n<details><summary>Runtime interface</summary>\n```json\n'+JSON.stringify(iface)+'\n```\n</details>';};
 const iface=(op,n,calls=[])=>({entries:[{operation:op,input_schema:schema,result_schema:schema}],calls,resources:[],limits:{max_steps:100,max_model_calls:n}});
 put('prompts/tap.prompt.md',iface('tap',cap,childCalls===undefined?[]:[{target:'prompts/child.prompt.md',target_operation:'child',max_calls:childCalls}]));
 put('prompts/draw.prompt.md',iface('draw',drawCap));put('prompts/child.prompt.md',iface('child',childCap));
 const map={screens:[{id:'main',prompt_path:'prompts/draw.prompt.md',operation:'draw',source:'operation'}],handlers:[{screen:'main',handler:{prompt_path:'prompts/tap.prompt.md',operation:'tap'},input:{},next:{kind:'same'},after:[]}]};
 return {map,ports:{root:'/project',statFile:p=>({exists:Object.hasOwn(files,p),is_symlink:false}),readFile:p=>files[p]}};
}
test('model budget includes rendering and declared caller resumes at the 40-call boundary',()=>{
 let f=boundFixture(39);assert.equal(productTapCallBound(f.map,f.ports),40);
 f=boundFixture(40);assert.throws(()=>productTapCallBound(f.map,f.ports),e=>e.code==='invalid-product-map'&&/41/.test(e.message));
 f=boundFixture(1,19);assert.equal(productTapCallBound(f.map,f.ports),40);
 f=boundFixture(1,20);assert.throws(()=>productTapCallBound(f.map,f.ports),e=>e.code==='invalid-product-map');
});

test('bounded tap-budget oracle covers 1024 caller/child/render combinations',()=>{
 for(let parent=1;parent<=8;parent++)for(let child=1;child<=8;child++)for(let count=1;count<=4;count++)for(let draw=1;draw<=4;draw++){
  const f=boundFixture(parent,count,child,draw),expected=Math.max(parent,1+count*(child+1))+draw;
  if(expected<=40)assert.equal(productTapCallBound(f.map,f.ports),expected);
  else assert.throws(()=>productTapCallBound(f.map,f.ports),e=>e.code==='invalid-product-map');
 }
});

test('budget oracle detects a missing destination draw without a load failure',async()=>{
 const location=new URL('../../src/runtime/product-composition.mjs',import.meta.url);
 const source=readFileSync(location,'utf8');
 const changed=source.replace('bound+=Math.max(0,...destinations', 'bound+=0*Math.max(0,...destinations');
 assert.notEqual(changed,source);
 const absolute=changed.replace(/from '(\.\/[^']+)'/g,(_all,path)=>`from '${new URL(path,location).href}'`);
 const mutant=await import('data:text/javascript;base64,'+Buffer.from(absolute).toString('base64'));
 const f=boundFixture(39);
 assert.throws(()=>assert.equal(mutant.productTapCallBound(f.map,f.ports),40),{code:'ERR_ASSERTION'});
});

test('navigation without a model handler still includes destination drawing',()=>{
 let f=boundFixture(1,undefined,1,40);f.map.handlers[0].handler=null;
 assert.equal(productTapCallBound(f.map,f.ports),40);
 f=boundFixture(1,undefined,1,41);f.map.handlers[0].handler=null;
 assert.throws(()=>productTapCallBound(f.map,f.ports),e=>e.code==='invalid-product-map'&&/41/.test(e.message));
});
