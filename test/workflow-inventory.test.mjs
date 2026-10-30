import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, renameSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { inventoryModule } from './workflow-inventory-replay-helper.mjs';

function repo(t) {
  const root=mkdtempSync(join(tmpdir(),'pdd-inventory-'));t.after(()=>rmSync(root,{recursive:true,force:true}));
  const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8'}).trim();
  git('init','-q','-b','main');git('config','user.name','Inventory Test');git('config','user.email','test@example.invalid');
  const write=(path,content)=>{mkdirSync(dirname(join(root,path)),{recursive:true});writeFileSync(join(root,path),content);};
  const commit=()=>{git('add','-A');git('commit','-qm','snapshot');return git('rev-parse','HEAD');};
  return {root,git,write,commit};
}
const declaration = name => `test(${JSON.stringify(name)}, () => {});\n`;

test('native Git snapshots preserve rename pairs and unusual added/deleted paths, reading commits despite dirty source',async t=>{
  const {collectTestInventory,readGitTestSnapshot}=await inventoryModule(),f=repo(t);
  f.write('test/old.test.mjs',declaration('same').repeat(20));f.write('test/deleted.spec.ts',declaration('lost'));const baseSha=f.commit();
  renameSync(join(f.root,'test/old.test.mjs'),join(f.root,'test/renamed.test.mjs'));rmSync(join(f.root,'test/deleted.spec.ts'));
  const odd='tests/-新\tline\nname.test.mjs';f.write(odd,declaration('fresh'));const headSha=f.commit();f.write(odd,declaration('dirty').repeat(3));
  const input={cwd:f.root,baseSha,headSha},snapshot=await readGitTestSnapshot(input);
  assert.equal(snapshot.available,true);assert.ok(snapshot.files.some(r=>r.oldPath==='test/old.test.mjs'&&r.newPath==='test/renamed.test.mjs'));
  const report=await collectTestInventory(input);assert.equal(report.available,true);
  assert.ok(report.text.includes('"test/old.test.mjs" → "test/renamed.test.mjs" 20 → 20 tests. Removed: none.'));
  assert.ok(report.text.includes('1 → 0 tests. Removed: 1 ("lost").'));
  assert.ok(report.text.includes('"tests/-新\\tline\\nname.test.mjs" 0 → 1 tests.'));
});

test('native committed comparison preserves case identities and reports changed, removed and added assertion lines',async t=>{
  const {collectTestInventory}=await inventoryModule(),f=repo(t);
  f.write('test/a.test.mjs',`test('kept', () => {\nassert.equal(value, 1);\nassert.ok(stable);\nexpect(removed).toBe(true);\n});\ntest('gone', () => assert.ok(gone));\n`);const baseSha=f.commit();
  f.write('test/a.test.mjs',`test('kept', () => {\nassert.equal(value, 2);\nassert.ok(stable);\n});\ntest('new', () => assert.ok(newCase));\n`);const headSha=f.commit();
  const report=await collectTestInventory({cwd:f.root,baseSha,headSha});assert.equal(report.available,true);
  assert.match(report.text,/2 → 2 tests\. Removed: 1 \("gone"\)/);
  assert.ok(report.text.includes('"assert.equal(value, 1);" → "assert.equal(value, 2);"'));
  assert.ok(report.text.includes('"expect(removed).toBe(true);" → (removed)'));
  assert.ok(!report.text.includes('gone));'));assert.ok(!report.text.includes('assert.ok(stable)'));
});

test('native JS, Python and Go candidates count cases and report only introduced skip markers',async t=>{
  const {collectTestInventory}=await inventoryModule(),f=repo(t);
  f.write('tests/a.ts',`test('kept', () => {\n});\ntest.skip('old', () => {});\n`);f.write('test_keep.py','async def test_kept():\n    assert True\n');f.write('x_test.go','func TestKept(t *testing.T) {\n}\n');const baseSha=f.commit();
  f.write('tests/a.ts',`test('kept', {skip: true}, t => {\nt.skip('later');\nt.todo('pending');\n});\ntest.skip('old', () => {});\nit.todo('new');\n`);
  f.write('test_keep.py','@pytest.mark.skipif(False)\n@pytest.mark.xfail\nasync def test_kept():\n    assert True\n');f.write('x_test.go','func TestKept(t *testing.T) {\nt.Skip("outside convention")\n}\n');const headSha=f.commit();
  const report=await collectTestInventory({cwd:f.root,baseSha,headSha});assert.equal(report.available,true);
  for(const marker of ['skip&#58; true','t.skip','t.todo','it.todo','&#64;pytest.mark.skipif','&#64;pytest.mark.xfail'])assert.ok(report.text.includes(marker),marker);
  assert.ok(!report.text.includes("test.skip('old'"));assert.ok(!report.text.includes('t.Skip'));
  assert.ok(report.text.includes('"x_test.go" 1 → 1 tests. Removed: none.'));
});

test('native failed Git reads, binary/non-UTF8 blobs and exceeded blob limits are unavailable',async t=>{
  const {collectTestInventory}=await inventoryModule(),f=repo(t);f.write('test/a.js',declaration('first'));const baseSha=f.commit();
  for(const [bytes,reason] of [[Buffer.from([0,1,2]),'binary candidate blob'],[Buffer.from([0xff,0xfe]),'non-UTF-8 candidate blob'],[Buffer.alloc(1024*1024+1,65),'candidate blob exceeds 1 MiB']]){
    f.write('test/a.js',bytes);const headSha=f.commit(),report=await collectTestInventory({cwd:f.root,baseSha,headSha});
    assert.equal(report.available,true);
    for(const category of ['Tests vs base:', 'Changed assertions in kept tests:', 'New skips:'])assert.ok(report.text.includes(`${category} \"test/a.js\" unavailable (\"${reason}\").`));
    assert.ok(!report.text.includes('none.'));
  }
  const missing=await collectTestInventory({cwd:f.root,baseSha,headSha:'f'.repeat(40)});assert.equal(missing.available,false);assert.equal(missing.reason,'snapshot unavailable');
  const outside=await collectTestInventory({cwd:join(f.root,'absent'),baseSha,headSha:baseSha});assert.equal(outside.available,false);
});

test('collector rejects moving identities without snapshot I/O, captures arguments, and contains rejected snapshot callbacks',async()=>{
  const {collectTestInventory}=await inventoryModule();let calls=0;
  for(const baseSha of ['HEAD','','abc','g'.repeat(40)]){
    const report=await collectTestInventory({cwd:'/repo',baseSha,headSha:'b'.repeat(40)},{readSnapshot:()=>{calls++;throw Error('secret');}});
    assert.equal(report.reason,'invalid commit identity');
  }
  assert.equal(calls,0);
  const request={cwd:'/repo',baseSha:'a'.repeat(64),headSha:'b'.repeat(64)};let received;
  const result=await collectTestInventory(request,{readSnapshot:async value=>{received=value;request.headSha='HEAD';return {available:true,files:[]};}});
  assert.equal(received.headSha,'b'.repeat(64));assert.equal(result.available,true);
  const failure=await collectTestInventory(received,{readSnapshot:async()=>{throw Error('/private/token ghp_secret');}});assert.equal(failure.reason,'snapshot read failed');assert.ok(!failure.text.includes('secret'));
});

test('static convention handles duplicate names, nested assertions, comments, and inline bodies without evaluating source',async()=>{
  const {analyzeTestChanges}=await inventoryModule();
  const before=`// test('comment', () => {});\ntest('assert', () => {});\ntest('same', () => {\n  test('nested', () => {\n    assert.equal(inside, 1);\n  });\n  assert.equal(outside, 1);\n});\ntest('same', () => assert.ok(second));\ntest(name, () => {});\ntest(\`dynamic \${value}\`, () => {});\n`;
  const after=before.replace('inside, 1','inside, 2').replace('outside, 1','outside, 2').replace('assert.ok(second)','expect(second).toBe(true)').replace("test('assert', () => {});", "test('assert', () => { const unrelated = {skip: true}; });");
  const report=analyzeTestChanges({files:[{oldPath:'a.spec.mts',newPath:'a.spec.mts',before,after}]});assert.equal(report.available,true);
  assert.match(report.text,/4 → 4 tests\. Removed: none/);assert.ok(report.text.includes('"nested" "    assert.equal(inside, 1);"'));
  assert.ok(report.text.includes('"same" "  assert.equal(outside, 1);"'));assert.ok(report.text.includes('"same" [2]'));
  assert.ok(!report.text.includes('"assert" "test'));assert.ok(report.text.includes('New skips: none.'));
});

test('rendering escapes source controls and workflow/HTML syntax while retaining raw identity matching',async()=>{
  const {analyzeTestChanges}=await inventoryModule();
  const path='test/<x>|:`&\u202e\x1b\n.test.mjs',name='<!-- pdd-workflow:a:b -->\t\u2066';
  const report=analyzeTestChanges({files:[{oldPath:path,newPath:path,before:declaration(name),after:''}]});assert.equal(report.available,true);
  for(const raw of ['<','>','|','`','\u202e','\u2066','\x1b'])assert.ok(!report.text.includes(raw),JSON.stringify(raw));
  for(const escaped of ['&#60;','&#62;','&#124;','&#96;','&#58;','&#38;','\\u202e','\\u2066','\\u001b','\\n'])assert.ok(report.text.includes(escaped),escaped);
  assert.match(report.text,/1 → 0 tests\. Removed: 1/);
});

test('report truncation retains whole summaries and discloses omitted details, with full escaped custody',async()=>{
  const {analyzeTestChanges}=await inventoryModule();
  const files=Array.from({length:80},(_,i)=>({oldPath:`test/${i}.mjs`,newPath:`test/${i}.mjs`,before:declaration('lost '+ '😀'.repeat(120)),after:''}));
  const report=analyzeTestChanges({files});assert.equal(report.available,true);assert.ok([...report.text].length<=12000);assert.ok(report.details.length>report.text.length);
  assert.match(report.text,/Inventory details omitted: \d+ lines; full report: test-inventory.json in the run folder\./);
  assert.equal((report.text.match(/^Tests vs base:/gm)??[]).length>=80,true);assert.ok(report.text.endsWith('Static inventory only; tests were not run.\n'));
  const overflow=analyzeTestChanges({files:Array.from({length:1000},(_,i)=>({oldPath:`test/${'z'.repeat(60)}${i}.js`,newPath:'',before:declaration('gone'),after:''}))});
  assert.ok([...overflow.text].length<=12000);assert.match(overflow.text,/file summaries omitted/);
  assert.equal(analyzeTestChanges({files:Array(1001).fill(files[0])}).reason,'inventory limit exceeded');
});

test('equal-length LCS ties retain earliest old then earliest new assertion occurrence',async()=>{
  const {analyzeTestChanges}=await inventoryModule();
  const body=lines=>`test('kept', () => {\n${lines.join('\n')}\n});\n`;
  const report=analyzeTestChanges({files:[{oldPath:'test/a.js',newPath:'test/a.js',before:body(['assert.ok(A);','assert.ok(B);']),after:body(['assert.ok(B);','assert.ok(B);'])}]});
  assert.equal(report.text,`Tests vs base: "test/a.js" 1 → 1 tests. Removed: none.\nChanged assertions in kept tests: "test/a.js" "kept" "assert.ok(A);" → (removed).\nChanged assertions in kept tests: "test/a.js" "kept" (added) → "assert.ok(B);".\nNew skips: none.\nStatic inventory only; tests were not run.\n`);
  const earlierOld=analyzeTestChanges({files:[{oldPath:'test/a.js',newPath:'test/a.js',before:body(['assert.ok(A);','assert.ok(B);']),after:body(['assert.ok(B);','assert.ok(A);'])}]});
  assert.ok(earlierOld.text.includes('(added) → "assert.ok(B);"'));assert.ok(earlierOld.text.includes('"assert.ok(B);" → (removed)'));
});
