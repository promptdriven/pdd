import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import child from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const vectors = JSON.parse(fs.readFileSync(join(root, 'test/shared-contracts/local-contract-layouts.json'), 'utf8'));

import {replayCases} from './helpers/local-contract-replay.mjs';
import {observe} from './helpers/local-contract-observers.mjs';

test('layout native observers detect writes, history, programs and network', () => {
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

replayCases(vectors,'contract layouts replay',join(root,'test/shared-contracts/local-contract-layouts.json'));
