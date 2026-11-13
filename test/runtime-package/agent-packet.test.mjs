import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {buildAgentInput} from '../../src/runtime/agent-packet.mjs';
const entry={entry:'prompts/main.prompt.md#main',input_schema:{type:'object',properties:{argv:{type:'array',items:{type:'string'}},body:{type:'object',properties:{url:{type:'string'}}}},required:['argv'],additionalProperties:false}};
const unpack=s=>JSON.parse(s.slice(s.indexOf('\n\nDATA\n')+7));
test('packet contains short signatures once and keeps stable parts first',()=>{const context={project:'A project',message:'What can I try?',criteria:[{id:'AC1',text:'Help',state:'todo',entry:entry.entry,input:{argv:['--help']},checks:[{value:'secret expected'}]}],fields:{entry:entry.entry,input:{argv:[]}}};const before=JSON.stringify(context),text=buildAgentInput({context,entries:[entry,entry]}),p=unpack(text);assert.deepEqual(Object.keys(p),['productRules','ways','project','criteria','conversation','coverage','progress','try','message','changed']);assert.equal(p.ways.length,1);assert.deepEqual(p.ways[0],{entry:entry.entry,input:{argv:'array',body:{url:'string'}},required:['argv']});assert.equal(p.criteria[0].state,undefined);assert.deepEqual(p.progress,{line:'',items:[{id:'AC1',state:'todo'}]});assert.ok(!text.includes('additionalProperties'));assert.ok(!text.includes('secret expected'));assert.equal(p.message,context.message);assert.equal(JSON.stringify(context),before);});
test('apply capability uses honest legacy wording and no model/effort settings',()=>{const legacy=buildAgentInput({context:{message:'fill it'},entries:[entry]}),modern=buildAgentInput({context:{message:'fill it'},entries:[entry],supportsApply:true});assert.match(legacy,/Press Fill fields, then Run/);assert.ok(!legacy.includes('Filled: <command>'));assert.match(modern,/Filled: <command>/);assert.ok(!modern.includes('Press Fill fields, then Run'));assert.ok(!modern.includes('reasoning_effort'));});
test('history windows, display caps and Unicode remain safe',()=>{const p=unpack(buildAgentInput({context:{message:'hi',project:'é'.repeat(2000),world:{text:'x'.repeat(2000)},runs:Array.from({length:12},(_,id)=>({id,result:{stdout:'x'.repeat(1000)}})),conversation:Array.from({length:10},(_,i)=>({person:String(i)+'🙂'.repeat(700),say:'s'.repeat(600)}))},entries:[entry]}));assert.ok(Buffer.byteLength(p.project)<=1536);assert.equal(p.runs,undefined);assert.equal(p.try.runs.length,8);assert.equal(p.try.runs[0].id,4);assert.ok(p.try.runs[0].result.length<=400);assert.ok(p.conversation.length<=6);assert.ok(Array.from(p.conversation[0].person).length<=500);assert.ok(!JSON.stringify(p).includes('�'));assert.ok(Array.from(p.try.world).length<=800);});
test('drops turns before world, runs and criterion text under total cap',()=>{const context={message:'help',fields:{input:{board:'x'.repeat(14000)}},world:'small world',criteria:[{id:'AC1',text:'Useful criterion',state:'todo'}],runs:[{id:'latest',result:'short'}],conversation:Array.from({length:6},()=>({person:'p'.repeat(500),say:'s'.repeat(500)}))};const text=buildAgentInput({context,entries:[entry]}),p=unpack(text);assert.ok(Buffer.byteLength(text)<=24576);assert.ok(p.conversation.length<6);assert.equal(p.try.world,'small world');assert.equal(p.try.runs.length,1);assert.equal(p.criteria[0].text,'Useful criterion');});
test('essential oversized structure and huge direct messages fail without payload leaks',()=>{assert.throws(()=>buildAgentInput({context:{message:'sensitive'.repeat(1000)},entries:[entry]}),e=>!/sensitive/.test(e.message));assert.throws(()=>buildAgentInput({context:{message:'hi',fields:{input:{secret:'private-value'.repeat(3000)}}},entries:[entry]}),e=>!/private-value/.test(e.message));const cyclic={};cyclic.x=cyclic;assert.throws(()=>buildAgentInput({context:cyclic}));});
test('legacy direct text/current normalized while unknown fields never serialized',()=>{const p=unpack(buildAgentInput({context:{text:'Old message',current:{input:{argv:['a']}},unknown:'omit-me'},entries:[entry]}));assert.equal(p.message,'Old message');assert.deepEqual(p.try.fields,{input:{argv:['a']}});assert.ok(!JSON.stringify(p).includes('omit-me'));});
test('cap removes world before older runs and preserves latest message and complete fields',()=>{const fields={input:{value:'x'.repeat(15500)}},context={message:'keep this exact request',fields,world:'w'.repeat(800),runs:Array.from({length:8},(_,id)=>({id,result:'r'.repeat(400)})),criteria:[{id:'AC1',text:'keep text',state:'todo'}]};const text=buildAgentInput({context,entries:[entry]}),p=unpack(text);assert.ok(Buffer.byteLength(text)<=24576);assert.equal(p.try.world,undefined);assert.ok(p.try.runs.length<8);assert.equal(p.try.runs.at(-1)?.id,7);assert.equal(p.criteria[0].text,'keep text');assert.equal(p.message,context.message);assert.deepEqual(p.try.fields,fields);});
test('large criterion text yields to essential complete input without invalid JSON',()=>{const context={message:'help',fields:{input:{value:'x'.repeat(12000)}},criteria:Array.from({length:12},(_,i)=>({id:'AC'+i,text:'long '.repeat(500),state:'todo',entry:entry.entry,input:{argv:['a']}}))};const text=buildAgentInput({context,entries:[entry]}),p=unpack(text);assert.ok(Buffer.byteLength(text)<=24576);assert.equal(p.criteria.length,12);assert.deepEqual(p.criteria[0].input,{argv:['a']});assert.ok(!p.criteria[0].text||p.criteria[0].text.length<=160);assert.equal(p.message,'help');});
test('oversized ways and cyclic entries fail plainly',()=>{assert.throws(()=>buildAgentInput({context:{message:'hi'},entries:Array.from({length:50},(_,i)=>({...entry,entry:'path'+i+'x'.repeat(100)+'#main'}))}),/signatures/);const e={};e.x=e;assert.throws(()=>buildAgentInput({entries:[e]}),/valid JSON/);});

test('malformed message and entry objects fail with plain errors',()=>{assert.throws(()=>buildAgentInput({context:{message:null}}),/message/);assert.throws(()=>buildAgentInput({entries:[null]}),/entry must be an object/);});

test('Try guide packet knows coverage, product rules and own-case context',()=>{const context={message:'Try no matches',project:'Where you are: prompt space',coverage:{text:'4 CLI commands, 3 HTTP endpoints, no screens',private:'not duplicated'},productRules:[{path:'prompts/bm.prompt.md',text:'Adds append duplicates.',summary:'# bm',truncated:false}],criteria:[{id:'AC1',knownid:'story#AC1',story_path:'user_stories/bookmarks.md',text:'Add',state:'todo'}],fields:{entry:entry.entry,input:{argv:[]},blank:true,source:'own',preloaded:false,world:'never repeat this',last_answer:'not fields'},mode:'own case'};const t=buildAgentInput({context,entries:[entry],supportsApply:true}),p=unpack(t);assert.match(t,/Try guide/);assert.match(t,/fit is only loose/);assert.match(t,/always return a fill/);assert.match(t,/ordinary conversation until the product is fully tried/);assert.match(t,/"expect"/);assert.match(t,/"save"/);assert.equal(p.coverage,context.coverage.text);assert.equal(p.productRules[0].text,'Adds append duplicates.');assert.equal(p.try.mode,'own case');assert.deepEqual(p.try.fields,{entry:entry.entry,input:{argv:[]},blank:true,source:'own',preloaded:false});assert.equal(p.criteria[0].story_path,'user_stories/bookmarks.md');assert.ok(!JSON.stringify(p).includes('never repeat this'));});
test('large optional context compacts and never repeats legacy world/last answer as fields',()=>{const context={message:'help',world:{big:'x'.repeat(100000)},conversation:Array.from({length:30},()=>({person:'x'.repeat(10000),say:'y'.repeat(10000)})),current:{entry:entry.entry,input:{argv:['--help']},world:'secret duplicate',last_answer:'duplicate answer'}};const t=buildAgentInput({context,entries:[entry]}),p=unpack(t);assert.ok(Buffer.byteLength(t)<=24576);assert.deepEqual(p.try.fields,{entry:entry.entry,input:{argv:['--help']}});assert.equal(p.conversation.length,6);assert.ok(!t.includes('secret duplicate'));});
test('ways retain HTTP and CLI meaning without full schemas',()=>{const entries=[{...entry,label:'Bookmark CLI',name:'bm',cli:true},{...entry,entry:'p#get',http:{method:'GET',path:'/api/bookmarks/:id'}}],p=unpack(buildAgentInput({context:{message:'help'},entries}));assert.match(p.ways[0].description,/CLI/);assert.match(p.ways[0].description,/bm|Bookmark/);assert.equal(p.ways[1].description,'GET /api/bookmarks/:id');assert.ok(Buffer.byteLength(JSON.stringify(p.ways))<=1024);});
test('product rules are summarized after older runs and before criterion text',()=>{const context={message:'help',fields:{entry:entry.entry,input:{data:'x'.repeat(10000)}},criteria:[{id:'AC1',text:'keep criterion',state:'todo'}],productRules:[{path:'p1',text:'RULE '.repeat(1000),summary:'# Rule one'},{path:'p2',text:'OTHER '.repeat(900),summary:'# Rule two'}],conversation:[{person:'q'.repeat(500),say:'a'.repeat(500)}],world:'w'.repeat(800),runs:[{id:'old',result:'r'.repeat(400)}]};const p=unpack(buildAgentInput({context,entries:[entry]}));assert.equal(p.conversation.length,0);assert.equal(p.try.world,undefined);assert.equal(p.try.runs.length,0);assert.equal(p.productRules[0].text,'# Rule one');assert.equal(p.criteria[0].text,'keep criterion');});
test('run-capable packet distinguishes explicit manual intent from run-event evidence',()=>{
 const modern=buildAgentInput({context:{message:'Run it',requestKind:'chat'},entries:[entry],supportsApply:true,supportsRun:true});
 assert.equal(unpack(modern).try.requestKind,'chat');assert.match(modern,/run:true/);assert.match(modern,/automatic.*(?:result|run)/i);
 const legacy=buildAgentInput({context:{message:'Run it'},entries:[entry]});assert.match(legacy,/run is unavailable/);assert.ok(!legacy.includes('shows an Undo'));assert.ok(!modern.includes('You cannot run anything'));
});
test('execution instructions avoid second manual Run and obsolete one-tap promises',()=>{
 const text=buildAgentInput({context:{message:'Execute the selected action'},entries:[entry],supportsApply:true,supportsRun:true});
 assert.match(text,/For fill-only requests/);assert.match(text,/wait for its result rather than asking for another manual Run/);
 assert.doesNotMatch(text,/accept with one tap|shows an Undo|only the person presses Run/);
 assert.match(text,/ordinary conversation/);
});

test('static prefix from byte 0 stays byte-identical across turns and conversation appends',()=>{
 const rules=[{path:'prompts/orders.prompt.md',text:'# Orders\n\n'+'_rule_'.repeat(600),summary:'# Orders',truncated:false}];
 const card=(nextStep,saved)=>`You are the Try guide.\nOpened Story: orders.\nNext step: ${nextStep}.\nSave target: tests/orders.json (exists, 2 steps, ${saved} saved cases from this Try). Append after existing steps.`;
 const turn1=buildAgentInput({
  context:{
   project:card('Finish the Try',0),
   coverage:{text:'Coverage: 0/2 criteria pass · 0/1 surfaces tried'},
   productRules:rules,
   criteria:[{id:'AC1',knownid:'orders#AC1',story_path:'user_stories/orders.md',text:'Place order',state:'todo',entry:entry.entry,input:{argv:['place']}}],
   progress:{line:'Story progress: 0 of 1 pass',items:[{id:'AC1',state:'todo'}]},
   world:{orders:[]},runs:[],fields:{entry:entry.entry,input:{argv:[]},preloaded:true},mode:'chat',
   conversation:[],message:'What first?',changed:false
  },
  entries:[entry],supportsApply:true,supportsRun:true
 });
 const turn2=buildAgentInput({
  context:{
   project:'Local copy changed: checks use your current local Story/test copy.\n'+card('pdd test orders',1),
   coverage:{text:'Coverage: 1/2 criteria pass · 1/1 surfaces tried'},
   productRules:rules,
   criteria:[{id:'AC1',knownid:'orders#AC1',story_path:'user_stories/orders.md',text:'Place order',state:'pass',entry:entry.entry,input:{argv:['place']}}],
   progress:{line:'Story progress: 1 of 1 pass',items:[{id:'AC1',state:'pass',check_passed:true}]},
   world:{orders:[{id:1}]},runs:[{id:'r1',entry:entry.entry,input:{argv:['place']},result:{stdout:'ok\n'}}],
   fields:{entry:entry.entry,input:{argv:['place']},preloaded:false},mode:'walk',
   conversation:[{person:'What first?',say:'Try place.',apply:true}],message:'Next?',changed:true
  },
  entries:[entry],supportsApply:true,supportsRun:true
 });
 const turn3=buildAgentInput({
  context:{
   project:card('pdd approve prompts/orders.prompt.md',2),
   coverage:{text:'Coverage: 2/2 criteria pass · 1/1 surfaces tried'},
   productRules:rules,
   criteria:[{id:'AC1',knownid:'orders#AC1',story_path:'user_stories/orders.md',text:'Place order',state:'pass',entry:entry.entry,input:{argv:['place']}}],
   progress:{line:'Story progress: 1 of 1 pass',items:[{id:'AC1',state:'pass',check_passed:true}]},
   world:{orders:[{id:1},{id:2}]},runs:[{id:'r1',entry:entry.entry,input:{argv:['place']},result:{stdout:'ok\n'}},{id:'r2',entry:entry.entry,input:{argv:['list']},result:{stdout:'2\n'}}],
   fields:{entry:entry.entry,input:{argv:['list']},preloaded:false},mode:'chat',
   conversation:[{person:'What first?',say:'Try place.',apply:true},{person:'Next?',say:'Try list.',apply:false}],message:'Done?',changed:false
  },
  entries:[entry],supportsApply:true,supportsRun:true
 });
 const staticBoundary=turn1.indexOf('"conversation":[')+'"conversation":['.length;
 assert.ok(staticBoundary>4500);
 assert.equal(turn2.slice(0,staticBoundary),turn1.slice(0,staticBoundary));
 const convBoundary=turn2.indexOf('],"coverage":');
 assert.ok(convBoundary>staticBoundary);
 assert.equal(turn3.slice(0,convBoundary),turn2.slice(0,convBoundary));
 const p2=unpack(turn2);
 assert.equal(p2.try.nextStep,'pdd test orders');
 assert.equal(p2.try.savedCount,1);
 assert.match(p2.try.localCopyNotice,/current local Story/);
 assert.doesNotMatch(p2.project,/Next step:|saved cases from this Try|Local copy changed:/);
});

test('permuted schema and criterion input object keys produce byte-identical ways and criteria',()=>{
 const entryA={entry:'p#op',input_schema:{type:'object',properties:{zebra:{type:'string'},alpha:{type:'object',properties:{second:{type:'integer'},first:{type:'boolean'}}}},required:['alpha']}};
 const entryB={entry:'p#op',input_schema:{type:'object',properties:{alpha:{type:'object',properties:{first:{type:'boolean'},second:{type:'integer'}}},zebra:{type:'string'}},required:['alpha']}};
 const a=buildAgentInput({context:{message:'hi',criteria:[{id:'AC1',text:'Check',entry:'p#op',input:{zebra:'z',alpha:{second:2,first:true}}}]},entries:[entryA]});
 const b=buildAgentInput({context:{message:'hi',criteria:[{id:'AC1',text:'Check',entry:'p#op',input:{alpha:{first:true,second:2},zebra:'z'}}]},entries:[entryB]});
 assert.equal(a,b);
 assert.deepEqual(Object.keys(unpack(a).ways[0].input),['alpha','zebra']);
 assert.deepEqual(Object.keys(unpack(a).ways[0].input.alpha),['first','second']);
 assert.deepEqual(Object.keys(unpack(a).criteria[0].input),['alpha','zebra']);
 assert.deepEqual(Object.keys(unpack(a).criteria[0].input.alpha),['first','second']);
});
