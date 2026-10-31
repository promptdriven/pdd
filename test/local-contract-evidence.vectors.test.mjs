import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import child from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const vectors = JSON.parse(fs.readFileSync(join(root, 'test/shared-contracts/local-contract-evidence.json'), 'utf8'));

import {checkWarnings} from './helpers/local-contract-warnings.mjs';
import {observe,snapshot} from './helpers/local-contract-observers.mjs';

test('evidence native observers detect writes, history, programs and network', () => {
  const folder=fs.mkdtempSync(join(tmpdir(),'pdd-layout-observers-'));
  const state=join(folder,'state'); fs.mkdirSync(state);
  const symlinkTarget=join(folder,'outside');fs.writeFileSync(symlinkTarget,'sentinel');
  const observed=observe({state,symlinkTarget});
  try {
    fs.writeFileSync(join(folder,'calibration'),'x');
    fs.readdirSync(state);
    const fd=fs.openSync(symlinkTarget,'r');fs.closeSync(fd);
    assert.throws(()=>child.spawnSync('layout-observer-no-program'));
    assert.throws(()=>globalThis.fetch('http://127.0.0.1:1'));
    for (const key of ['write','history','symlink_target_read','auth','runtime','model','slots']) assert.ok(observed.calls[key]>0,key);
  } finally { observed.restore();fs.rmSync(folder,{recursive:true,force:true}); }
});

for (const vector of vectors.cases.filter(vector=>vector.argv)) test(`contract evidence replay: ${vector.id}`, async () => {
  const sandbox = fs.mkdtempSync(join(tmpdir(), 'pdd-local-contract-'));
  const cwd = join(sandbox, 'repo'), state = join(sandbox, 'state');
  fs.mkdirSync(cwd); fs.mkdirSync(state);
  try {
    for (const [path, text] of Object.entries({...vectors.setup.base_files, ...vector.set_files})) {
      fs.mkdirSync(dirname(join(cwd, path)), {recursive: true}); fs.writeFileSync(join(cwd, path), text);
    }
    // The fixture defines deletion before replacement, so replacement wins.
    for (const path of vector.delete_files) if (!Object.hasOwn(vector.set_files, path)) fs.rmSync(join(cwd, path), {force: true});
    // Symlink targets are external sentinels, not another Git-visible contract
    // that independent discovery could legitimately read.
    const symlinkTarget = join(sandbox, 'outside-world.md');
    for (const [path, target] of Object.entries(vector.symlinks ?? {})) {
      fs.rmSync(join(cwd, path), {force: true});
      const outside = join(sandbox, target); fs.writeFileSync(outside, 'outside sentinel');
      fs.symlinkSync(outside, join(cwd, path));
    }
    if (vector.git_repository !== false) {
      assert.equal(child.spawnSync('git', ['init', '-q'], {cwd}).status, 0);
      assert.equal(child.spawnSync('git', ['add', '.'], {cwd}).status, 0);
    }
    const before = snapshot(cwd);
    let stdout = '', stderr = '';
    const words = vector.argv.slice(1).filter(word => !word.startsWith('--'));
    const options = Object.fromEntries(vector.argv.filter(word => word.startsWith('--')).map(word => [word, true]));
    // Import before observation: module-loader reads are not command effects.
    const { runContracts } = await import('../src/contracts.mjs');
    const observed = observe({state, symlinkTarget});
    let result;
    try {
      result = await runContracts({words, options, cwd}, {env: {...process.env, PDD_STATE_DIR: state}, stdout: {write: text => { stdout += text; }}, stderr: {write: text => { stderr += text; }}});
    } finally { observed.restore(); }
    assert.equal(result, vector.expected.exit_code);
    if (!vector.expected.syntax_error) {
      let facts;
      if (options['--json']) {
        facts = JSON.parse(stdout);
        assert.deepEqual(Object.keys(facts).sort(),['exit_code','checked_records','checked_world_values','skipped_files','diagnostics','warnings'].sort());
        assert.equal(stderr,'');
      } else {
        // Independently repeat the public boundary in JSON mode; each mode
        // satisfies the frozen expected facts, never the other mode's output.
        let jsonOut='', jsonErr='';
        const again = observe({state,symlinkTarget});
        try {
          const code=runContracts({words,options:{...options,'--json':true},cwd},{env:{...process.env,PDD_STATE_DIR:state},stdout:{write:text=>{jsonOut+=text;}},stderr:{write:text=>{jsonErr+=text;}}});
          assert.equal(code,vector.expected.exit_code);
          for (const [key,value] of Object.entries(vector.expected.calls)) assert.equal(again.calls[key],value,`JSON calls.${key}`);
        } finally { again.restore(); }
        assert.equal(jsonErr,'');
        facts=JSON.parse(jsonOut);
        assert.match(stdout,new RegExp(`Checked ${vector.expected.checked_records} records and ${vector.expected.checked_world_values} world values\\.`));
        const lines=stderr.trim() ? stderr.trim().split('\n') : [];
        assert.equal(lines.length,vector.expected.diagnostics.length,'text diagnostic count');
        for (const diagnostic of vector.expected.diagnostics) assert.ok(lines.some(line=>line.includes(diagnostic.file)&&line.includes(diagnostic.record)&&line.includes(diagnostic.field)));
        if (vector.expected.skipped_files.length) assert.ok(stdout.includes(`Skipped ${vector.expected.skipped_files.length} files that are not schemas: ${vector.expected.skipped_files.join(', ')}`));
      }
      checkWarnings(facts.warnings,vector.expected.warnings,options['--json'] ? null : stdout);
      assert.equal(facts.exit_code,vector.expected.exit_code);
      assert.equal(facts.checked_records,vector.expected.checked_records);
      assert.equal(facts.checked_world_values,vector.expected.checked_world_values);
      assert.deepEqual(facts.skipped_files,vector.expected.skipped_files);
      assert.equal(facts.diagnostics.length,vector.expected.diagnostics.length,'JSON diagnostic count');
      const keys=facts.diagnostics.map(item=>['file','record','field','kind','source_pointer','target','message'].map(key=>item[key]??''));
      assert.deepEqual(keys,[...keys].sort((a,b)=>{for(let i=0;i<a.length;i++){if(a[i]!==b[i])return a[i]<b[i]?-1:1;}return 0;}),'diagnostic order');
      for (let i=0;i<facts.diagnostics.length;i++) {
        const actual=facts.diagnostics[i], expected=vector.expected.diagnostics[i];
        assert.deepEqual(Object.fromEntries(Object.keys(expected).map(key=>[key,actual[key]])),expected);
        assert.ok(typeof actual.message==='string' && actual.message.trim() && actual.message.length<=8000);
        for (const key of Object.keys(actual)) assert.ok(['file','record','field','kind','message','source_pointer','target'].includes(key));
      }
    }
    for (const [key, value] of Object.entries(vector.expected.calls)) {
      assert.ok(Object.hasOwn(observed.calls, key), `Not replayed: calls.${key}`);
      assert.equal(observed.calls[key], value, `calls.${key}`);
    }
    if (vector.expected.source_bytes_unchanged) assert.deepEqual(snapshot(cwd), before);
    if (vector.expected.source_modes_unchanged) assert.deepEqual(snapshot(cwd),before);
    const mapped=new Set(['exit_code','diagnostics','calls','source_bytes_unchanged','source_modes_unchanged','checked_records','checked_world_values','skipped_files','syntax_error','warnings']);
    for (const key of Object.keys(vector.expected)) assert.ok(mapped.has(key),`Not replayed: expected.${key}`);
  } finally { fs.rmSync(sandbox, {recursive: true, force: true}); }
});

// Inspect every own tree entry, including opaque numeric atoms. Serialization of
// the immutable parse input or renderer bytes cannot detect child mutation.
import {parseJsonValue,jsonNumberText,schemaValuesEqual} from '../src/contract-refs.mjs';
function tree(value) {
  const number=jsonNumberText(value);
  if (number!==null) return {number};
  if (value===null || typeof value!=='object') return {primitive:value};
  return {array:Array.isArray(value),entries:Reflect.ownKeys(value).map(key=>[key,tree(value[key])])};
}
for (const vector of vectors.equality_cases) test(`schema evidence replay: ${vector.id}`,()=>{
  const a=parseJsonValue(vector.a),b=parseJsonValue(vector.b);
  const beforeA=tree(a),beforeB=tree(b);
  assert.equal(schemaValuesEqual(a,b),vector.expected);
  assert.deepEqual(tree(a),beforeA,'a own tree unchanged');
  assert.deepEqual(tree(b),beforeB,'b own tree unchanged');
});
