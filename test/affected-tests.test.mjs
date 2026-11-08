import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync, readFileSync, renameSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { selectAffectedTests } from '../src/affected-tests.mjs';
import { affectedPlan, runAffected } from '../scripts/affected-tests.mjs';

const smoke = ['test/smoke.test.mjs'];
const files = {
  'test/smoke.test.mjs': '', 'src/leaf.mjs': 'export const value = 2;',
  'src/middle.mjs': "export * from './leaf.mjs';", 'src/cycle.mjs': "import './middle.mjs';",
  'test/leaf.test.mjs': "import '../src/middle.mjs';", 'test/unrelated.test.mjs': '',
  'prompts/cli/leaf.prompt.md': '# Leaf',
  'test/runtime/leaf-story.json': '{"entry_path":"prompts/cli/leaf.prompt.md","story_path":"user_stories/leaf-story.md"}',
  'user_stories/leaf-story.md': '# Story',
  'test/leaf-story.vectors.test.mjs': "const path = new URL('./runtime/leaf-story.json', import.meta.url);",
};
const select = (changed, extra = {}) => selectAffectedTests({ files: { ...files, ...extra }, changed, smoke });

test('module and prompt changes include transitive consumers, scenarios, replay and smoke', () => {
  assert.deepEqual(select(['src/leaf.mjs']).tests, ['test/leaf.test.mjs','test/smoke.test.mjs']);
  assert.deepEqual(select(['prompts/cli/leaf.prompt.md']).tests, ['test/leaf-story.vectors.test.mjs','test/leaf.test.mjs','test/smoke.test.mjs']);
  assert.deepEqual(select(['test/unrelated.test.mjs']).tests, ['test/smoke.test.mjs','test/unrelated.test.mjs']);
  assert.deepEqual(select([]).tests, smoke);
});

test('literal dynamic imports, require, cycles, and computed helper consumers cannot lose tests', () => {
  for (const statement of ["import('../src/leaf.mjs')", "require('../src/leaf.mjs')", "import(variable)", "fs.readFileSync(path)", "spawnSync(command, args)"]) {
    const result = select(['src/leaf.mjs'], { 'test/indirect.test.mjs': "import '../src/adapter.mjs';", 'src/adapter.mjs': statement });
    assert.ok(result.tests.includes('test/indirect.test.mjs'), statement);
  }
  assert.ok(select(['src/leaf.mjs'], { 'src/middle.mjs': "import './cycle.mjs'; export * from './leaf.mjs';" }).tests.includes('test/leaf.test.mjs'));
});

test('unsafe changes and incomplete inputs fall back to the entire suite', () => {
  for (const path of ['package.json','package-lock.json','test/helpers/world.mjs','test/fixture.mjs','scripts/run.mjs','unknown.py']) {
    const result = select([path], { [path]: '' });
    assert.equal(result.mode, 'full', path);
    assert.equal(result.tests.length, result.total);
  }
  for (const result of [select(['missing.mjs']), select(['../outside']), selectAffectedTests({ files, changed: [], smoke: ['test/missing.test.mjs'] }), select(['prompts/unmapped.prompt.md'], {'prompts/unmapped.prompt.md':''}), select(['src/leaf.mjs'], {'test/leaf.test.mjs':"import '../src/missing.mjs';"})]) {
    assert.equal(result.mode, 'full');
    assert.ok(result.reasons.length);
  }
});

function repo(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-affected-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const put = (path, text) => { mkdirSync(join(root, path, '..'), { recursive: true }); writeFileSync(join(root, path), text); };
  const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
  git('init','-q'); git('config','user.email','test@example.invalid'); git('config','user.name','Test');
  for (const [path,text] of Object.entries(files)) put(path,text);
  put('test/cli-node-version.test.mjs',''); put('test/command-catalog.test.mjs','');
  git('add','.'); git('commit','-qm','base');
  return { root, put, git, base: git('rev-parse','HEAD') };
}

test('native inventory includes dirty, staged, untracked, deleted and renamed dependencies', t => {
  const r = repo(t);
  renameSync(join(r.root,'src/leaf.mjs'),join(r.root,'src/renamed.mjs'));
  r.put('src/middle.mjs', "export * from './renamed.mjs';");
  r.put('test/new test.test.mjs', "import '../src/renamed.mjs';");
  r.git('add','src');
  const plan = affectedPlan({ root:r.root, base:r.base });
  assert.equal(plan.mode,'affected',plan.reasons.join(','));
  assert.ok(plan.tests.includes('test/leaf.test.mjs'));
  assert.ok(plan.tests.includes('test/new test.test.mjs'));
  assert.equal(plan.head,r.base);
  assert.match(plan.fingerprint,/^[a-f0-9]{64}$/);
  assert.equal(affectedPlan({root:r.root,base:'missing-ref'}).mode,'full');
});

const tap = '# tests 3\n# suites 0\n# pass 3\n# fail 0\n# cancelled 0\n# skipped 0\n# todo 0\n# duration_ms 1\n';
test('runner executes argument arrays, records actual counts and rejects stale or failed results', t => {
  const r = repo(t), report = join(r.root,'..',`${r.root.split('/').at(-1)}.json`);
  t.after(() => rmSync(report,{force:true}));
  const calls=[];
  const execute=(...args)=>{calls.push(args);return {status:0,stdout:tap,stderr:''};};
  const first=runAffected({root:r.root,base:r.base,run:true,report},{execute});
  assert.equal(first.exitCode,0);
  assert.equal(first.evidence.counts.pass,3);
  assert.equal(JSON.parse(readFileSync(report)).fingerprint,first.plan.fingerprint);
  assert.equal(calls[0][0],process.execPath);
  assert.deepEqual(calls[0][1],['--test',...first.plan.tests]);
  assert.equal(runAffected({root:r.root,base:r.base,run:true},{execute:()=>{r.put('src/leaf.mjs','changed');return {status:0,stdout:tap};}}).exitCode,1);
  assert.equal(runAffected({root:r.root,base:r.base,run:true},{execute:()=>({status:7,stdout:tap})}).exitCode,7);
  assert.equal(runAffected({root:r.root,base:r.base,run:true},{execute:()=>({status:0,stdout:'partial'})}).exitCode,1);
  assert.throws(()=>runAffected({root:r.root,base:r.base,report:'in-tree.json'}));
});

test('full fallback uses the shared suite adapter and cannot masquerade as an affected run', t => {
  const r=repo(t); r.put('package.json','{}');
  const calls=[];
  const result=runAffected({root:r.root,base:r.base,run:true},{execute:(...args)=>{calls.push(args);return {status:0,stdout:tap};}});
  assert.equal(result.evidence.mode,'full');
  assert.equal(calls[0][0],'bash');
  assert.deepEqual(calls[0][1],[join(r.root,'scripts/vm-suite-lock.sh')]);
  assert.equal(calls[0][2].env.SUITE,'npm test');
  assert.equal(result.evidence.tests.length,result.evidence.total);
  assert.equal(result.evidence.suiteMinutes,null);
  assert.ok(result.evidence.elapsedMinutes >= 0);
});

test('aliases for filesystem and child-process APIs are conservative and external packages require full', () => {
  for (const text of ["import { statSync as inspect } from 'node:fs'; inspect(variable)", "import fs from 'node:fs/promises'; fs.access(variable)", "import { fork as start } from 'child_process'; start(variable)"]) {
    assert.ok(select(['src/leaf.mjs'],{'test/opaque.test.mjs':text}).tests.includes('test/opaque.test.mjs'));
  }
  assert.equal(select(['src/leaf.mjs'],{'test/external.test.mjs':"import 'third-party'; readFileSync(variable)"}).mode,'full');
});

test('unreadable byte inventories cannot claim current passing evidence and child signals survive', t => {
  const r=repo(t);
  const command=args=>execFileSync('git',args,{cwd:r.root,encoding:'utf8'});
  const read=path=>{if(path==='src/leaf.mjs')throw Error('unreadable');return readFileSync(join(r.root,path));};
  const plan=()=>affectedPlan({root:r.root,base:r.base},{command,read});
  assert.equal(plan().inventoryComplete,false);
  const result=runAffected({root:r.root,base:r.base,run:true},{plan,execute:()=>({status:0,stdout:tap})});
  assert.equal(result.exitCode,1); assert.equal(result.evidence.stale,true);
  const signalled=runAffected({root:r.root,base:r.base,run:true},{execute:()=>({status:null,signal:'SIGTERM',stdout:tap})});
  assert.equal(signalled.exitCode,143); assert.equal(signalled.evidence.signal,'SIGTERM');
});

test('the real native runner executes selected tests and preserves their assertion failure', t => {
  const r=repo(t);
  r.put('test/cli-node-version.test.mjs', "import test from 'node:test'; import assert from 'node:assert/strict'; test('smoke',()=>assert.equal(2+2,4));");
  r.put('test/command-catalog.test.mjs', "import test from 'node:test'; test('catalog',()=>{});");
  r.git('add','.'); r.git('commit','-qm','native smoke');
  const execute=(command,args,options)=>{ const env={...options.env}; delete env.NODE_TEST_CONTEXT; return spawnSync(command,args,{...options,env}); };
  const pass=runAffected({root:r.root,base:'HEAD',run:true},{execute});
  assert.equal(pass.exitCode,0,JSON.stringify(pass)); assert.equal(pass.evidence.counts.pass,2);
  r.put('test/failure.test.mjs', "import test from 'node:test'; import assert from 'node:assert/strict'; test('failure',()=>assert.equal(1,2));");
  const fail=runAffected({root:r.root,base:'HEAD',run:true},{execute});
  assert.equal(fail.exitCode,1); assert.equal(fail.evidence.counts.fail,1);
  assert.equal(fail.evidence.counts.pass,2); assert.equal(fail.evidence.stale,false);
});


test('template interpolation imports and computed builtin acquisition cannot hide consumers', () => {
  assert.equal(select(['src/leaf.mjs'],{'test/template.test.mjs':"const x = `${await import('third-party')}`;"}).mode,'full');
  assert.ok(select(['src/leaf.mjs'],{'test/computed.test.mjs':"process.getBuiltinModule(['f','s'].join('')).statSync(variable)"}).tests.includes('test/computed.test.mjs'));
});


test('multiline import and reexport declarations preserve external fallback and local dependencies', () => {
  for (const declaration of ["import {\n value\n} from 'third-party';", "export {\n value\n} from 'third-party';"]) assert.equal(select(['src/leaf.mjs'],{'test/multiline.test.mjs':declaration}).mode,'full');
  assert.ok(select(['src/leaf.mjs'],{'test/multiline.test.mjs':"import {\n value\n} from '../src/leaf.mjs';"}).tests.includes('test/multiline.test.mjs'));
});

test('comments between dependency tokens preserve external import fallback', () => {
  for (const declaration of [
    "import /* explanation */ 'third-party';",
    "import // explanation\n 'third-party';",
    "import // explanation\r 'third-party';",
    "import // explanation\u2028 'third-party';",
    "import // explanation\u2029 'third-party';",
    "import { value } from /* explanation */ 'third-party';",
    "export { value } from // explanation\n 'third-party';",
    "await import /* explanation */ (/* argument */ 'third-party');",
    "require // explanation\n (/* argument */ 'third-party');",
    "const value = `${await import /* explanation */ ('third-party')}`;",
  ]) {
    const result = select(['src/leaf.mjs'], {'test/commented.test.mjs': declaration});
    assert.equal(result.mode, 'full', declaration);
    assert.equal(result.tests.length, result.total, declaration);
  }
});

test('commented computed imports and requires keep reverse consumers selected', () => {
  for (const statement of [
    "await import /* dependency */ ('./' + name + '.mjs');",
    "await import // dependency\n (name);",
    "require /* dependency */ (name);",
    "require( /* argument */ name);",
  ]) {
    const result = select(['src/leaf.mjs'], {
      'src/adapter.mjs': statement,
      'test/indirect.test.mjs': "import '../src/adapter.mjs';",
    });
    assert.ok(result.tests.includes('test/indirect.test.mjs'), statement);
  }
});

test('commented literal dependencies and comment markers in strings retain local edges', () => {
  for (const statement of [
    "import /* dependency */ './target';",
    "import { value } from /* dependency */ './target';",
    "export { value } from // dependency\n './target';",
    "await import /* dependency */ (/* argument */ './target');",
    "require // dependency\n (/* argument */ './target');",
  ]) {
    const result = select(['src/target.mjs'], {
      'src/target.mjs': 'export const value = 1;',
      'src/adapter.mjs': statement,
      'test/indirect.test.mjs': "import '../src/adapter.mjs';",
    });
    assert.ok(result.tests.includes('test/indirect.test.mjs'), statement);
  }
  assert.equal(select(['src/leaf.mjs'], {
    'test/external.test.mjs': "import 'third-party/*literal*/';",
  }).mode, 'full');
  for (const [specifier, target] of [
    ['./nested/*literal*/target', 'src/nested/*literal*/target.mjs'],
    ['./nested//target', 'src/nested/target.mjs'],
  ]) {
    const result = select([target], {
      [target]: 'export const value = 1;',
      'src/adapter.mjs': `import '${specifier}';`,
      'test/indirect.test.mjs': "import '../src/adapter.mjs';",
    });
    assert.equal(result.mode, 'affected', specifier);
    assert.ok(result.tests.includes('test/indirect.test.mjs'), specifier);
  }
});

test('the native runner catches a broken consumer behind a commented computed import', t => {
  const r = repo(t);
  r.put('src/leaf.mjs', 'export const value = 1;');
  r.put('test/consumer.test.mjs', [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "const name = ['l', 'eaf'].join('');",
    "const { value } = await import /* dependency */ ('../src/' + name + '.mjs');",
    "test('consumer value', () => assert.equal(value, 1));",
  ].join('\n'));
  r.git('add', '.'); r.git('commit', '-qm', 'commented consumer');
  const execute = (command, args, options) => {
    const env = { ...options.env }; delete env.NODE_TEST_CONTEXT;
    return spawnSync(command, args, { ...options, env });
  };
  // Prove the real consumer passes before changing only its dependency.
  const before = execute(process.execPath, ['--test', 'test/consumer.test.mjs'], { cwd: r.root, encoding: 'utf8', env: process.env });
  assert.equal(before.status, 0, before.stdout + before.stderr);
  r.put('src/leaf.mjs', 'export const value = 2;');
  const direct = execute(process.execPath, ['--test', 'test/consumer.test.mjs'], { cwd: r.root, encoding: 'utf8', env: process.env });
  assert.equal(direct.status, 1, direct.stdout + direct.stderr);
  const result = runAffected({ root: r.root, base: 'HEAD', run: true }, { execute });
  assert.equal(result.exitCode, 1, JSON.stringify(result));
  assert.ok(result.plan.tests.includes('test/consumer.test.mjs'));
  assert.equal(result.evidence.counts.fail, 1);
  assert.equal(result.evidence.stale, false);
});

test('unclassified regex syntax cannot hide external imports after quotes or comment markers', () => {
  for (const expression of ["/'/", '/"/', '/[\'"/]/', '/\\/\\*/', '/\\/\\//']) {
    const result = select(['src/leaf.mjs'], {
      'src/adapter.mjs': `const pattern = ${expression}; import 'third-party';`,
      'test/consumer.test.mjs': "import '../src/adapter.mjs';",
    });
    assert.equal(result.mode, 'full', expression);
    assert.equal(result.tests.length, result.total, expression);
  }
});

// Replay each reported dependency break through real Git and Node. Full-mode
// execution uses a fixture queue port, never the VM's shared queue or full suite.
function brokenRequireConsumer(t, { prefix = '', ref = './target', target, candidates, adapterSource }) {
  const r = repo(t);
  for (const [path, text] of Object.entries(candidates)) r.put(path, text);
  r.put('src/adapter.cjs', adapterSource ?? `${prefix}\nconst { value } = require('${ref}');\nmodule.exports = { value };`);
  r.put('test/consumer.test.mjs', [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import adapter from '../src/adapter.cjs';",
    "test('required value', () => assert.equal(adapter.value, 1));",
  ].join('\n'));
  r.git('add', '.'); r.git('commit', '-qm', 'require consumer');
  const plan = () => affectedPlan({ root: r.root, base: 'HEAD' });
  const execute = (command, args, options) => {
    const env = { ...options.env }; delete env.NODE_TEST_CONTEXT;
    if (command === 'bash') {
      assert.deepEqual(args, [join(r.root, 'scripts/vm-suite-lock.sh')]);
      assert.equal(options.env.SUITE, 'npm test');
      return spawnSync(process.execPath, ['--test', ...plan().tests], { ...options, env });
    }
    return spawnSync(command, args, { ...options, env });
  };
  const direct = () => execute(process.execPath, ['--test', 'test/consumer.test.mjs'], {
    cwd: r.root, encoding: 'utf8', env: process.env,
  });
  const before = direct();
  assert.equal(before.status, 0, before.stdout + before.stderr);
  r.put(target, 'module.exports = { value: 2 };');
  const broken = direct();
  assert.equal(broken.status, 1, broken.stdout + broken.stderr);
  assert.match(broken.stdout, /ERR_ASSERTION/);
  const result = runAffected({ root: r.root, base: 'HEAD', run: true }, { execute });
  assert.equal(result.exitCode, 1, JSON.stringify(result));
  assert.ok(result.plan.tests.includes('test/consumer.test.mjs'));
  assert.equal(result.evidence.counts.fail, 1);
  assert.equal(result.evidence.stale, false);
  assert.equal(result.evidence.inventoryComplete, true);
}

test('native regex quotes cannot hide the consumer of a broken required module', t => {
  brokenRequireConsumer(t, {
    prefix: "const quote = /'/;", target: 'src/target.js',
    candidates: { 'src/target.js': 'module.exports = { value: 1 };' },
  });
});

for (const [name, adapterSource] of [
  ['aliased require', "const load = require; module.exports = load('./target');"],
  ['escaped require', String.raw`module.exports = requ\u0069re('./target');`],
  ['escaped loader alias', String.raw`const load = requ\u{69}re; module.exports = load('./target');`],
]) test(`native indirect CommonJS loader preserves broken reverse consumer: ${name}`, t => {
  brokenRequireConsumer(t, {
    target: 'src/target.js',
    candidates: { 'src/target.js': 'module.exports = { value: 1 };' },
    adapterSource,
  });
});

test('native extensionless require keeps its loaded file among ESM and directory candidates', t => {
  brokenRequireConsumer(t, {
    target: 'src/target.js',
    candidates: {
      'src/target.mjs': 'export const value = 999;',
      'src/target.js': 'module.exports = { value: 1 };',
      'src/target/index.js': 'module.exports = { value: 999 };',
    },
  });
});

test('native directory require keeps the loaded CommonJS index among ESM candidates', t => {
  brokenRequireConsumer(t, {
    target: 'src/target/index.js',
    candidates: {
      'src/target/index.mjs': 'export const value = 999;',
      'src/target/index.js': 'module.exports = { value: 1 };',
    },
  });
});

test('native directory package entries cannot be replaced by an unused index', t => {
  brokenRequireConsumer(t, {
    target: 'src/target/entry.js',
    candidates: {
      'src/target/package.json': '{"main":"entry.js"}',
      'src/target/entry.js': 'module.exports = { value: 1 };',
      'src/target/index.js': 'module.exports = { value: 999 };',
    },
  });
});

for (const expression of [
  "Number(`${`` + require('./target').value}`)",
  "Number(`${`${''}` + require('./target').value}`)",
  "Number(`${`` + ({value: require('./target').value}).value}`)",
  "Number(`${ /* boundary */ `` + require('./target').value}`)",
  "Number(`${`` + require('./target' + '').value}`)",
]) test(`native nested template preserves broken reverse consumer: ${expression}`, t => {
  brokenRequireConsumer(t, {
    target: 'src/target.js',
    candidates: { 'src/target.js': 'module.exports = { value: 1 };' },
    adapterSource: `const value = ${expression}; module.exports = { value };`,
  });
});
