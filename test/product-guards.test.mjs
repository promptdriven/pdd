import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {composeProductTry,productTapCallBound} from '../src/runtime-seam.mjs';
import {parseProductWorldWriters} from '../src/product.mjs';
const original=JSON.parse(readFileSync(new URL('./runtime/product-compose-try.json',import.meta.url))).initial_world.files;
function fixture(){const files=structuredClone(original);return {files,ports:{root:'/project',statFile:path=>({exists:Object.hasOwn(files,path),is_symlink:false}),readFile:path=>files[path].content}};}
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
test('small product needs no shared files and preserves optional part seed values',()=>{
 const {files,ports}=fixture();
 for(const path of Object.keys(files))if(path.includes('/seed.json')||path.includes('/contracts/'))delete files[path];
 const compose=()=>composeProductTry({root:'/project',parts:['phone']},ports);
 assert.deepEqual(JSON.parse(compose().files[1].content),{});
 files['/project/prompts/phone/seed.json']={content:'{"orders":[],"enabled":false,"value":null,"zero":0}'};
 assert.deepEqual(JSON.parse(compose().files[1].content),{orders:[],enabled:false,value:null,zero:0});
});
test('only one genuine writer table supplies ownership',()=>{
 const worldText='# World\n| Key | Writer |\n|---|---|\n| orders | server |\n\n## Notes\n| Key | Note |\n|---|---|\n| arbitrary | explanation |\n';
 assert.deepEqual(parseProductWorldWriters({worldText}),[{key:'orders',writer:'server'}]);
 assert.throws(()=>parseProductWorldWriters({worldText:worldText+'\n| Key | Writer |\n|---|---|\n| orders | phone |\n'}),e=>e.code==='invalid-product');
});
test('unavailable operation bounds and unsupported map options are explicit refusals',()=>{
 const f=boundFixture(1);delete f.ports.readFile;assert.throws(()=>productTapCallBound(f.map,{...f.ports,readFile:()=>{throw Error('unavailable')}}));
 const x=fixture();const map=JSON.parse(x.files['/project/app/maps/phone.json'].content);map.timers=[];x.files['/project/app/maps/phone.json'].content=JSON.stringify(map);
 assert.throws(()=>composeProductTry({root:'/project'},x.ports),e=>e.code==='invalid-product-map'&&/timers/.test(e.message));
});
