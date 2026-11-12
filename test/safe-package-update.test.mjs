import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join, resolve} from 'node:path';
import {runPdd} from '../src/pdd-cli.mjs';
import {runAutopilotDoctor} from '../src/autopilot-doctor.mjs';
import {doctorFixture} from './helpers/doctor-fixture.mjs';

const root = resolve(import.meta.dirname, '..');
const safe = 'npm install -g github:promptdriven/pdd';
const migrate = 'npm uninstall -g pdd && ' + safe;
const metadata = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));

test('npm identity uses the owned scope and preserves the pdd executable', () => {
  assert.equal(metadata.name, '@promptdriven/pdd');
  assert.deepEqual(metadata.bin, {pdd:'bin/pdd.mjs'});
});

for (const state of ['legacy','github','both','missing','malformed']) test(`setup package update: ${state} leaves packages unchanged`, async t => {
  const folder = mkdtempSync(join(tmpdir(), 'pdd-package-update-'));
  t.after(() => rmSync(folder, {recursive:true, force:true}));
  const pkg = state==='legacy' ? join(folder,'node_modules','pdd') : join(folder, 'node_modules', '@promptdriven', 'pdd');
  mkdirSync(pkg, {recursive:true});
  for (const name of ['src','bin']) cpSync(join(root, name), join(pkg, name), {recursive:true});
  const text = state==='malformed'?'{broken':JSON.stringify({...metadata, name:state==='legacy'?'pdd':'@promptdriven/pdd'});
  if(state!=='missing') writeFileSync(join(pkg, 'package.json'), text);
  const old=join(folder,'node_modules','pdd');
  if(state==='both') {mkdirSync(old);writeFileSync(join(old,'package.json'),JSON.stringify({name:'pdd'}));}
  let stdout = '', stderr = '';
  const code = await runPdd(['setup','--yes'], {
    packageRoot:pkg, cwd:folder, env:{HOME:folder, PATH:''}, stdin:{isTTY:false},
    stdout:{write:s=>stdout+=s}, stderr:{write:s=>stderr+=s},
    workflowAgents:{checkWorkflowAgents:async()=>({ok:true,agent:'codex'})},
    setupSkills:()=>[], setupProject:()=>({file:join(folder,'AGENTS.md'),changed:false}),
    gitContext:async()=>null, setupAgentMcp:async()=>0,
    autopilot:{runAutopilot:async()=>({exitCode:0,message:''})}
  });
  assert.equal(code,0,stdout+stderr);
  if(['missing','malformed'].includes(state)) assert.ok(!stderr.includes(migrate),stderr);
  else {
    assert.ok(stderr.includes(state==='github'?safe:migrate),stderr);
    assert.match(stderr,/npm update -g/);
  }
  if(state!=='missing') assert.equal(readFileSync(join(pkg,'package.json'),'utf8'),text);
  if(state==='both') assert.equal(readFileSync(join(old,'package.json'),'utf8'),JSON.stringify({name:'pdd'}));
});

for (const state of ['legacy','github','both','missing','malformed']) test(`doctor package update: ${state} is read-only and advisory`, async () => {
  const packageRoot='/global/node_modules/@promptdriven/pdd';
  const f=doctorFixture({packageRoot});
  const own=join(packageRoot,'package.json'), old='/global/node_modules/pdd/package.json';
  if (state!=='missing') f.paths.set(own,state==='malformed'?'{broken':JSON.stringify({name:state==='legacy'?'pdd':'@promptdriven/pdd'}));
  if (state==='both') f.paths.set(old,JSON.stringify({name:'pdd'}));
  const before=[...f.paths];
  const result=await runAutopilotDoctor(f.input,f.ports);
  assert.equal(result.exitCode,0,result.message);
  const warning=result.checks.find(c=>c.id==='package-update');
  if (['missing','malformed'].includes(state)) assert.equal(warning,undefined);
  else {
    assert.equal(warning?.status,'warn');
    assert.ok(warning.fix.includes(state==='github'?safe:migrate),warning.fix);
    assert.ok(result.message.includes(warning.fix));
  }
  assert.deepEqual([...f.paths],before);
  assert.ok(f.calls.every(c=>c.file!=='npm'));
});
