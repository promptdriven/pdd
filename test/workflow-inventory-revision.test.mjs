import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { execFileSync } from 'node:child_process';
import { performance } from 'node:perf_hooks';
import { inventoryModule } from './workflow-inventory-replay-helper.mjs';

const body = (name,lines) => `test(${JSON.stringify(name)}, () => {\n${lines.join('\n')}\n});\n`;
const pair = (path,before,after,extra={}) => ({oldPath:path,newPath:path,before,after,...extra});
const healthy = pair('test/healthy.js',body('kept',['assert.equal(value, 1);'])+body('gone',[]),body('kept',['assert.equal(value, 2);','t.skip("pending");']));
const reasons = ['candidate blob exceeds 1 MiB','binary candidate blob','non-UTF-8 candidate blob'];
const categories = ['Tests vs base:','Changed assertions in kept tests:','New skips:'];
function preservesHealthy(report) {
  assert.equal(report.available,true);assert.equal(report.reason,'');
  assert.ok(report.details.includes('"test/healthy.js" 2 → 1 tests. Removed: 1 ("gone").'));
  assert.ok(report.details.includes('"assert.equal(value, 1);" → "assert.equal(value, 2);"'));
  assert.ok(report.details.includes('"kept" "t.skip(\\"pending\\");"'));
}
function unavailablePair(report,path,reason) {
  for(const category of categories)assert.ok(report.details.includes(`${category} ${JSON.stringify(path)} unavailable (${JSON.stringify(reason)}).`));
  assert.ok(!report.details.includes(`${JSON.stringify(path)} 0 →`));
  for(const category of categories)assert.ok(!report.details.includes(`${category} none.`));
}
function repository(t) {
  const root=realpathSync(mkdtempSync(join(tmpdir(),'pdd-inventory-revision-')));t.after(()=>rmSync(root,{recursive:true,force:true}));
  const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8'}).trim();
  git('init','-q','-b','main');git('config','user.name','Inventory Test');git('config','user.email','test@example.invalid');
  const write=(path,bytes)=>{mkdirSync(dirname(join(root,path)),{recursive:true});writeFileSync(join(root,path),bytes);};
  const commit=()=>{git('add','-A');git('commit','-qm','snapshot');return git('rev-parse','HEAD');};
  return {root,git,write,commit};
}

test('revision native bad blobs disclose every category and preserve healthy removals, assertions and skips',async t=>{
  const {collectTestInventory,readGitTestSnapshot}=await inventoryModule(),f=repository(t);
  f.write('test/healthy.js',healthy.before);const baseSha=f.commit();
  f.write('test/healthy.js',healthy.after);
  for(const [path,bytes] of [['test/big.js',Buffer.alloc(1048577,65)],['test/binary.js',Buffer.from([0,1])],['test/latin.js',Buffer.from([0xff])]])f.write(path,bytes);
  const headSha=f.commit(),input={cwd:f.root,baseSha,headSha};
  const report=await collectTestInventory(input);preservesHealthy(report);
  for(const [path,reason] of [['test/big.js',reasons[0]],['test/binary.js',reasons[1]],['test/latin.js',reasons[2]]])unavailablePair(report,path,reason);
  const snapshot=await readGitTestSnapshot(input);assert.equal(snapshot.available,true);
  assert.equal(snapshot.files.find(file=>file.newPath==='test/latin.js').unavailableReason,reasons[2]);
});

test('revision supplied snapshots isolate invalid pairs and exclude their bytes from aggregate accounting',async()=>{
  const {analyzeTestChanges}=await inventoryModule();
  const files=[healthy,pair('test/big.js','', 'x'.repeat(1048577)),pair('test/binary.js','', '\0'),pair('test/utf.js','','\ud800')];
  const report=analyzeTestChanges({files});preservesHealthy(report);
  for(const [path,reason] of [['test/big.js',reasons[0]],['test/binary.js',reasons[1]],['test/utf.js',reasons[2]]])unavailablePair(report,path,reason);
  const marked=analyzeTestChanges({files:[healthy,...Array.from({length:20},(_,i)=>pair(`test/${i}.js`,'x'.repeat(1048577),'\0',{unavailableReason:reasons[i%3]}))]});
  preservesHealthy(marked);unavailablePair(marked,'test/0.js',reasons[0]);
});

test('revision native candidate limit ignores documentation records and includes both rename sides only once',async t=>{
  const {collectTestInventory}=await inventoryModule(),f=repository(t);
  f.write('test/healthy.js',healthy.before);const baseSha=f.commit();f.write('test/healthy.js',healthy.after);
  for(let i=0;i<1001;i++)f.write(`docs/${i}.md`,'documentation');
  const headSha=f.commit();preservesHealthy(await collectTestInventory({cwd:f.root,baseSha,headSha}));
  for(let i=0;i<1000;i++)f.write(`test/candidate-${i}.js`,'');
  const exceeded=f.commit(),nativeExceeded=await collectTestInventory({cwd:f.root,baseSha,headSha:exceeded});
  assert.equal(nativeExceeded.available,false);assert.equal(nativeExceeded.reason,'inventory limit exceeded');
  const {analyzeTestChanges}=await inventoryModule();
  const candidates=Array.from({length:1000},(_,i)=>({oldPath:`test/${i}.js`,newPath:`tests/renamed-${i}.js`,before:'',after:''}));
  const docs=Array.from({length:1001},(_,i)=>pair(`docs/${i}.md`,'','docs'));
  assert.equal(analyzeTestChanges({files:[...docs,...candidates]}).available,true);
  assert.equal(analyzeTestChanges({files:[...docs,...candidates,healthy]}).reason,'inventory limit exceeded');
});

test('revision native and supplied aggregate budgets compare exactly 16 MiB and reject the next usable byte',async t=>{
  const {collectTestInventory,analyzeTestChanges}=await inventoryModule(),f=repository(t);
  f.write('readme.md','base');const baseSha=f.commit();
  const content=' '.repeat(1048576),files=Array.from({length:16},(_,i)=>pair(`test/${i}.js`,'',content));
  for(const file of files)f.write(file.newPath,file.after);
  const boundary=f.commit();assert.equal((await collectTestInventory({cwd:f.root,baseSha,headSha:boundary})).available,true);
  f.write('test/extra.js',' ');const exceeded=f.commit();
  const native=await collectTestInventory({cwd:f.root,baseSha,headSha:exceeded});assert.equal(native.available,false);assert.equal(native.reason,'inventory limit exceeded');
  assert.equal(analyzeTestChanges({files}).available,true);
  assert.equal(analyzeTestChanges({files:files.slice(0,8).map(file=>({...file,before:content}))}).available,true);
  assert.equal(analyzeTestChanges({files:files.slice(0,8).map(file=>({...file,before:content})).concat(pair('test/last.js','',' '))}).reason,'inventory limit exceeded');
  const supplied=analyzeTestChanges({files:[...files,pair('test/extra.js','',' ')]});assert.equal(supplied.available,false);assert.equal(supplied.reason,'inventory limit exceeded');
});

test('revision assertion cap preserves each other category and case and finishes a 2000-line case in under two seconds',async()=>{
  const {analyzeTestChanges}=await inventoryModule();
  const old=Array.from({length:2000},(_,i)=>`assert.equal(v${i}, 1);`),after=old.flatMap(line=>[line,'assert.ok(added);']);
  const before=body('large',old)+healthy.before,changed=body('large',after)+healthy.after;
  const start=performance.now(),report=analyzeTestChanges({files:[pair('test/healthy.js',before,changed)]}),elapsed=performance.now()-start;
  assert.ok(elapsed<2000,`2000-line cap took ${elapsed} ms`);
  assert.equal(report.available,true);assert.ok(report.text.includes('"large" unavailable ("too many assertion lines to compare").'));
  assert.ok(report.text.includes('3 → 2 tests. Removed: 1 ("gone").'));
  assert.ok(report.text.includes('"kept" "assert.equal(value, 1);" → "assert.equal(value, 2);"'));
  assert.ok(report.text.includes('"kept" "t.skip(\\"pending\\");"'));
});

test('revision exact million-cell LCS boundary compares normally with quadratic work and preserved tie ordering',async()=>{
  const {analyzeTestChanges}=await inventoryModule();
  // A mismatch after every retained line used to rebuild an entire suffix table.
  const old=Array.from({length:1000},(_,i)=>`assert.ok(v${i});`),after=old.slice(0,500).flatMap(line=>[line,'assert.ok(inserted);']);
  const start=performance.now(),report=analyzeTestChanges({files:[pair('test/boundary.js',body('kept',old),body('kept',after))]}),elapsed=performance.now()-start;
  assert.equal(report.available,true);assert.ok(!report.details.includes('unavailable'));assert.ok(elapsed<2000,`million-cell comparison took ${elapsed} ms`);
  assert.ok(report.details.includes('(added) → "assert.ok(inserted);"'));
  assert.ok(report.details.includes('"assert.ok(v999);" → (removed)'));
  const over=analyzeTestChanges({files:[pair('test/boundary.js',body('kept',old),body('kept',[...after,'assert.ok(last);']))]});
  assert.ok(over.details.includes('"kept" unavailable ("too many assertion lines to compare").'));
});

test('revision skip forms retain suite occurrence identity independently of tests and never count a suite as a test',async t=>{
  const {analyzeTestChanges}=await inventoryModule();
  const before=`describe('same', () => {\n  test('same', () => {});\n});\ndescribe.skip('same', () => {});\ntest('strings', () => {});\ntest('double', () => {});\ntest('template', () => {});\nit('disabled', () => {});\n`;
  const after=`describe.skip('same', () => {\n  test('same', () => {});\n});\ndescribe.skip('same', () => {});\ntest('strings', {skip: 'flaky'}, () => {});\ntest('double', {skip: "why"}, () => {});\ntest('template', {skip: \`later\`}, () => {});\nxit('disabled', () => {});\n`;
  const file=pair('test/skips.js',before,after),report=analyzeTestChanges({files:[file]});
  assert.equal(report.available,true);assert.ok(report.text.includes('5 → 5 tests. Removed: none.'));
  assert.ok(report.text.includes('New skips: "test/skips.js" suite "same" "describe.skip'));
  assert.ok(!report.text.includes('suite "same" [2]'));
  for(const name of ['strings','double','template','disabled'])assert.ok(report.text.includes(`New skips: "test/skips.js" "${name}"`));
  assert.equal((report.text.match(/^New skips:/gm)||[]).length,5);
  assert.ok(!report.text.includes('Changed assertions in kept tests: "test/skips.js" suite'));
  const unchanged=analyzeTestChanges({files:[pair('test/skips.js',after,after)]});assert.ok(unchanged.text.includes('New skips: none.'));
  const quotedReasons=analyzeTestChanges({files:[pair('test/skips.js','',`test('ordinary', {skip: 'flaky'}, () => {});\ntest('function-reason', {skip: 'function failed'}, () => {});\ntest('arrow-reason', {skip: 'later => now'}, () => {});\n`)]});
  for(const name of ['ordinary','function-reason','arrow-reason'])assert.ok(quotedReasons.text.includes(`New skips: "test/skips.js" "${name}"`),quotedReasons.text);
  assert.equal((quotedReasons.text.match(/^New skips:/gm)||[]).length,3);
  const negatives=analyzeTestChanges({files:[pair('test/skips.js','',`test('empty', {skip: ''}, () => {});\ntest('dynamic', {skip: reason}, () => {});\ntest('concat', {skip: 'reason' + dynamic}, () => {});\ntest('template-concat', {skip: \`reason\` + expression}, () => {});\ntest('expression', {skip: \`why \${reason}\`}, () => {});\ntest('true-and', {skip: true && condition}, () => {});\ntest('true-or', {skip: true || condition}, () => {});\ntest('true-ternary', {skip: true ? x : y}, () => {});\ntest('todo-and', {todo: true && condition}, () => {});\ntest('body-option', () => { consume({skip: true}); });\n`)]});assert.ok(negatives.text.includes('New skips: none.'),negatives.text);
  for(const option of ['skip: true','todo: true',"skip: 'function failed'",'skip: "later => now"','skip: `later`'])for(const context of ["reason: 'todo: true,'",'timeout: {skip: true}', 'context: (() => ({todo: true}))()'])for(const options of [`${context}, ${option}`,`${option}, ${context}`]){
    const report=analyzeTestChanges({files:[pair('test/skips.js','',`test('direct', {${options}}, () => {});\n`)]});
    assert.equal(report.available,true);assert.ok(report.details.includes('0 → 1 tests. Removed: none.'));
    assert.equal((report.details.match(/^New skips:/gm)||[]).length,1);
    assert.ok(report.details.includes('New skips: "test/skips.js" "direct" '),report.details);
  }
  // Only direct declaration options supply markers. These unrelated strings,
  // nested values, callback data and body objects all retain ordinary tests.
  const unrelated=[
    ...['timeout','todo','reason'].flatMap(key=>["'",'"','`'].flatMap(quote=>['skip: true,','todo: true,'].map(data=>`{${key}: ${quote}${data}${quote}}, () => {}`))),
    `{timeout: 'skip: "reason",'}, () => {}`,
    `{timeout: "prefix \\" skip: true, suffix"}, () => {}`,
    `{timeout: {skip: true}}, () => {}`,
    `{timeout: [{todo: true}]}, () => {}`,
    `{timeout: consume({skip: 'reason'})}, () => {}`,
    `{timeout: (() => ({todo: true}))()}, () => {}`,
    `{skip: {skip: true}}, () => {}`,
    `{todo: {skip: 'reason'}}, () => {}`,
    `{context() { consume({skip: true}); }}, () => {}`,
    `{timeout: 10 /* skip: true, */}, () => {}`,
    `consume({skip: true}), () => {}`,
    `options, {skip: true}`,
    `({skip: value = true}) => {}`,
    `function ({todo: value = true}) { consume({skip: true}); }`,
    `() => { consume({skip: 'reason'}); }`,
  ];
  const f=repository(t),ordinaryBefore=unrelated.map((_,i)=>`test('ordinary-${i}', () => {});`).join('\n')+'\n';
  const ordinaryAfter=unrelated.map((args,i)=>`test('ordinary-${i}', ${args});`).join('\n')+'\n';
  f.write('test/options.js',ordinaryBefore);const baseSha=f.commit();f.write('test/options.js',ordinaryAfter);const headSha=f.commit();
  const {collectTestInventory}=await inventoryModule();
  const expected=`Tests vs base: "test/options.js" ${unrelated.length} → ${unrelated.length} tests. Removed: none.\nChanged assertions in kept tests: none.\nNew skips: none.\nStatic inventory only; tests were not run.\n`;
  assert.equal(analyzeTestChanges({files:[pair('test/options.js',ordinaryBefore,ordinaryAfter)]}).details,expected);
  assert.equal((await collectTestInventory({cwd:f.root,baseSha,headSha})).details,expected);
});

test('revision Python body skips are reported and source mentions, issue links and decorators are escaped',async()=>{
  const {analyzeTestChanges}=await inventoryModule();
  const report=analyzeTestChanges({files:[pair('test/@owner#12.js',body('@owner #2570',[]),''),pair('test_skip.py','def test_kept():\n    pass\n','@pytest.mark.xfail\ndef test_kept():\n    pytest.skip("@owner #12")\n')]});
  assert.equal(report.available,true);
  for(const value of ['"test/&#64;owner&#35;12.js"','"&#64;owner &#35;2570"','"&#64;pytest.mark.xfail"','pytest.skip(\\"&#64;owner &#35;12\\")'])assert.ok(report.text.includes(value),value);
  assert.ok(!report.text.includes('@'));assert.ok(!/#\d/.test(report.text.replace(/&#\d+;/g,'')));
  assert.equal((report.text.match(/^New skips:/gm)||[]).length,2);
});

test('manual revision native callback boundary excludes quoted and nested option data',async t=>{
  const {collectTestInventory}=await inventoryModule(),f=repository(t);
  // The first two entries are the reviewer's exact witnesses. Expectations
  // follow body ownership: each actual callback is empty, regardless of options.
  const tails=[
    `{reason: '=> t.skip("no")'}, () => {}`,
    `{reason: '=> assert.ok(no)'}, () => {}`,
    ...['t.skip("no")','t.todo("no")','assert.ok(no)','expect(no)'].flatMap(content=>[
      `{reason: 'function () { ${content} }'}, async () => {}`,
      `{nested: {reason: '=> ${content}'}}, function (t) {}`,
      `{nested: [() => { ${content}; }]}, async function named(t) {}`,
      `{nested: function () { ${content}; }}, t => {}`,
    ]),
  ];
  const before=tails.map((_,i)=>`test('${i<2?'x':`empty-${i}`}', () => {});`).join('\n')+'\n';
  const after=tails.map((tail,i)=>`test('${i<2?'x':`empty-${i}`}', ${tail});`).join('\n')+'\n';
  f.write('test/options.js',before);const baseSha=f.commit();
  f.write('test/options.js',after);const headSha=f.commit();
  const remote=join(f.root,'.git','options-remote.git');
  f.git('init','--bare','-q',remote);f.git('remote','add','origin',remote);
  f.git('push','-q','origin',`${headSha}:refs/heads/main`);
  assert.equal(f.git('ls-remote','origin','refs/heads/main').split(/\s/)[0],headSha);
  // Ambient content cannot replace the committed snapshot.
  f.write('test/options.js',`test('ambient', t => t.skip('dirty'));\n`);
  const report=await collectTestInventory({cwd:f.root,baseSha,headSha});
  const expected=`Tests vs base: "test/options.js" ${tails.length} → ${tails.length} tests. Removed: none.\nChanged assertions in kept tests: none.\nNew skips: none.\nStatic inventory only; tests were not run.\n`;
  assert.equal(report.available,true);assert.equal(report.details,expected);
});

test('manual revision native callback ownership preserves inline and nested multiline evidence',async t=>{
  const {collectTestInventory}=await inventoryModule(),f=repository(t);
  f.write('readme.md','empty');const emptySha=f.commit();
  const render=value=>[
    `test('arrow', {reason: 'function () { fake }'}, t => { assert.ok(${value}); t.skip('real'); });`,
    `test('async', {nested: () => { fake(); }}, async t => expect(${value}));`,
    `test('function', {reason: '=> fake'}, function named(t) { assert.ok(${value}); t.todo('real'); });`,
    `test('outer', {reason: '=> {'}, async function (t) {`,
    `  test('child', {reason: 'function () {'}, () => {});`,
    `  test('no-body', {reason: '=> {'});`,
    `  assert.ok(${value});`,
    `  t.skip('outer marker');`,
    `  test('inner', {nested: function () { fake(); }}, async t => {`,
    `    expect(${value});`,
    `    t.todo('inner marker');`,
    `  });`,
    `});`,
    `test('standalone-no-body', {reason: 'function () {'});`,
    `assert.ok(outside${value});`,
    `t.todo('outside');`,
    '',
  ].join('\n');
  f.write('test/owners.js',render('old'));const baseSha=f.commit();
  f.write('test/owners.js',render('new'));const headSha=f.commit();
  const report=await collectTestInventory({cwd:f.root,baseSha,headSha});
  assert.equal(report.available,true);assert.ok(report.details.includes('8 → 8 tests. Removed: none.'));
  const changes=report.details.split('\n').filter(line=>line.startsWith('Changed assertions in kept tests:'));
  assert.equal(changes.length,5);
  for(const name of ['arrow','async','function','outer','inner'])assert.equal(changes.filter(line=>line.startsWith(`Changed assertions in kept tests: "test/owners.js" "${name}" `)).length,1,report.details);
  // Inline marker lines changed with their assertions; the exact-line marker
  // rule reports those two lines as new, while multiline markers are unchanged.
  const introduced=report.details.split('\n').filter(line=>line.startsWith('New skips:'));
  assert.equal(introduced.length,2);
  for(const name of ['arrow','function'])assert.equal(introduced.filter(line=>line.startsWith(`New skips: "test/owners.js" "${name}" `)).length,1,report.details);
  assert.ok(!report.details.includes('outsideold')&&!report.details.includes('outsidenew'));
  // Adding this source introduces all four genuine body markers, with their
  // innermost owners, while neither no-body declaration gains one.
  const added=await collectTestInventory({cwd:f.root,baseSha:emptySha,headSha});
  const skips=added.details.split('\n').filter(line=>line.startsWith('New skips:'));
  assert.equal(skips.length,4,added.details);
  for(const name of ['arrow','function','outer','inner'])assert.equal(skips.filter(line=>line.startsWith(`New skips: "test/owners.js" "${name}" `)).length,1,added.details);
});

// Complete assertion lines belong to real callback bodies even when a regular
// expression contains JS-looking delimiters. These are bounded literal forms,
// not a claim to parse arbitrary JavaScript.
for(const kind of ['expression arrow','block arrow','function'])test(`manual regex native ${kind} retains exact changed assertion lines`,async t=>{
  const {collectTestInventory}=await inventoryModule(),f=repository(t);
  const patterns=[String.raw`/[)]/`,String.raw`/[}]/`,String.raw`/[(]/`,String.raw`/[{]/`,String.raw`/[\])}]/`,String.raw`/\)/`,String.raw`/\//`,String.raw`/[\/) ]/`,String.raw`/[/*)]/`,String.raw`/[)\]\/}]/g`];
  const assertions=[(v,re)=>`assert.match(${v}, ${re})`,(v,re)=>`expect(${v}).toMatch(${re})`,(v,re)=>`expect(${re}.test(${v})).toBe(true)`,(v,re)=>`assert.ok(${re}.test(${v}))`];
  const callback=content=>kind==='expression arrow'?`() => ${content}`:kind==='block arrow'?`() => { ${content}; }`:`function () { ${content}; }`;
  const rows=[];
  for(const pattern of patterns)for(const assertion of assertions)for(const options of ['',`{pattern: ${pattern}}, `]){
    const name=`regex-${rows.length}`;
    const render=value=>`test(${JSON.stringify(name)}, ${options}${callback(assertion(value,pattern))});`;
    rows.push({name,before:render('value'),after:render('changed')});
  }
  // Keep the reviewer's simplest regression explicit as an exact-line witness.
  if(kind==='expression arrow')assert.equal(rows[0].before,'test("regex-0", () => assert.match(value, /[)]/));');
  f.write('test/regex.mjs',rows.map(row=>row.before).join('\n')+'\n');const baseSha=f.commit();
  f.write('test/regex.mjs',rows.map(row=>row.after).join('\n')+'\n');const headSha=f.commit();
  execFileSync(process.execPath,['--check',join(f.root,'test/regex.mjs')]);
  f.write('test/regex.mjs','// dirty worktree is not the committed comparison\n');
  const report=await collectTestInventory({cwd:f.root,baseSha,headSha});
  const quote=line=>JSON.stringify(line).replace(/[&<>`|:@#]/g,c=>`&#${c.charCodeAt(0)};`);
  const expected=[`Tests vs base: "test/regex.mjs" ${rows.length} → ${rows.length} tests. Removed: none.`,
    ...rows.map(row=>`Changed assertions in kept tests: "test/regex.mjs" ${quote(row.name)} ${quote(row.before)} → ${quote(row.after)}.`),
    'New skips: none.','Static inventory only; tests were not run.',''].join('\n');
  assert.equal(report.available,true);assert.equal(report.details,expected);
});
