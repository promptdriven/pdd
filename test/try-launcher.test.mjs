import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync,readlinkSync,readFileSync,writeFileSync,realpathSync,symlinkSync} from 'node:fs';
import {join} from 'node:path';
import {harbor,sink} from './runtime-fake.mjs';

test('NEXT11 launcher: one installed launcher has many names without PATH edits and refuses real commands',async t=>{
  const {installNamedLauncher}=await import('../src/try-launcher.mjs');
  const setup=harbor(t),bin=join(setup.sandbox,'bin');mkdirSync(bin);
  const opts={root:setup.repo,binDir:bin,path:bin,descriptorPath:join(setup.repo,'.pdd/try/sessions/s/door.json')};
  const first=installNamedLauncher({...opts,name:'bm'}),second=installNamedLauncher({...opts,name:'paperclip'});
  assert.equal(realpathSync(first),realpathSync(second));
  assert.ok(readlinkSync(first));
  assert.match(readFileSync(realpathSync(first),'utf8'),/PDD shared Try launcher v1/);
  writeFileSync(join(bin,'occupied'),'#!/bin/sh\nexit 9\n',{mode:0o700});
  assert.throws(()=>installNamedLauncher({...opts,name:'occupied'}),/already|clash|command/i);
  assert.equal(readFileSync(join(bin,'occupied'),'utf8'),'#!/bin/sh\nexit 9\n');
});

test('NEXT11 launcher: nearest repo is selected, nested cwd works, and another repo cannot supply its Try',async t=>{
  const {runNamedShim}=await import('../src/try-launcher.mjs');
  const setup=harbor(t),nested=join(setup.repo,'nested');mkdirSync(nested);
  const out=sink(),err=sink();
  assert.equal(await runNamedShim('bm',[],{cwd:nested,stdout:out,stderr:err}),125);
  assert.equal(out.text,'');assert.match(err.text,/no open Try here/);
  const privateDir=join(setup.repo,'.pdd/try/programs');mkdirSync(privateDir,{recursive:true,mode:0o700});
  symlinkSync(join(setup.home,'escape'),join(privateDir,'bm.json'));
  const denied=sink();assert.equal(await runNamedShim('bm',[],{cwd:nested,stdout:sink(),stderr:denied}),125);
  assert.match(denied.text,/unsafe|symbolic|link/i);
});

test('NEXT11 launcher: empty PATH segments still detect a real command in cwd',async t=>{
  const {installNamedLauncher}=await import('../src/try-launcher.mjs');
  const setup=harbor(t),bin=join(setup.sandbox,'bin');mkdirSync(bin);
  writeFileSync(join(setup.repo,'bm'),'#!/bin/sh\nexit 8\n',{mode:0o700});
  for(const path of ['',':'+bin,bin+':'])assert.throws(()=>installNamedLauncher({root:setup.repo,name:'bm',descriptorPath:join(setup.repo,'.pdd/try/sessions/s/door.json'),binDir:bin,path,cwd:setup.repo}),/already exists/);
  assert.equal(readFileSync(join(setup.repo,'bm'),'utf8'),'#!/bin/sh\nexit 8\n');
});
