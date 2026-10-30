import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { spawn, spawnSync } from 'node:child_process';
import { createServer } from 'node:net';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { validateContract } from '../src/runtime-preflight.mjs';

const root = dirname(dirname(fileURLToPath(import.meta.url)));
// Person-approved raw tokens: preserve the sign through precision loss,
// underflow and overflow. No Number/JSON.stringify round trip supplies inputs.
const cases = [
  ['-0.10000000000000001', false], ['-1e-9999', false], ['-1e9999', false],
  ['0.10000000000000001', true], ['1e-9999', true], ['1e9999', true],
];
for (const [token, valid] of cases) test(`schema-only multipleOf ${token}`, () => {
  const result = validateContract({schema_json: `{"type":"number","multipleOf":${token}}`});
  assert.equal(result.schema_problems.length > 0, !valid, 'multipleOf must be above zero');
  assert.deepEqual(result.value_problems, []);
  assert.deepEqual(result.unproved, []);
});

function snapshot(folder) {
  return fs.readdirSync(folder, {recursive:true}).sort().map(path => {
    const absolute = join(folder,path), stat = fs.lstatSync(absolute);
    return [path,stat.mode,stat.isFile() ? fs.readFileSync(absolute).toString('base64') : null];
  });
}
for (const [token, valid] of cases) test(`actual Coffee CLI multipleOf ${token}`, async () => {
  const sandbox = fs.mkdtempSync(join(tmpdir(), 'pdd-schema-sign-'));
  const repo = join(sandbox,'repo'), state = join(sandbox,'state'), bin = join(sandbox,'bin');
  fs.cpSync(join(root,'examples/coffee-pickup'),repo,{recursive:true});
  fs.mkdirSync(state); fs.mkdirSync(bin); fs.writeFileSync(join(state,'sentinel'),'preserve');
  const auth = join(sandbox,'auth');
  fs.writeFileSync(join(bin,'gh'),'#!/bin/sh\nprintf called >> "$PDD_SIGN_AUTH"\nexit 97\n',{mode:0o755});
  const server = createServer(socket => { connections++; socket.destroy(); });
  let connections = 0;
  await new Promise(resolve => server.listen(0,'127.0.0.1',resolve));
  try {
    fs.writeFileSync(join(repo,'contracts/numbers.md'),`### bad\n\n\`\`\`json\n{"type":"number","multipleOf":${token}}\n\`\`\`\n`);
    assert.equal(spawnSync('git',['init','-q'],{cwd:repo}).status,0);
    assert.equal(spawnSync('git',['add','.'],{cwd:repo}).status,0);
    const before = snapshot(repo), prior = snapshot(state);
    const result = await new Promise((resolve,reject) => {
      const child = spawn(process.execPath,[join(root,'bin/pdd.mjs'),'contracts','--check'],{
        cwd:repo, env:{...process.env,PATH:`${bin}:${process.env.PATH}`,PDD_SIGN_AUTH:auth,
          PDD_STATE_DIR:state,PDD_RUNTIME_URL:`http://127.0.0.1:${server.address().port}`},
      });
      let stdout = '', stderr = '';
      child.stdout.on('data',data => { stdout += data; });
      child.stderr.on('data',data => { stderr += data; });
      child.on('error',reject); child.on('close',(code,signal) => resolve({code,signal,stdout,stderr}));
    });
    assert.equal(result.signal,null,'natural CLI termination');
    assert.equal(result.code,valid ? 0 : 4, result.stdout + result.stderr);
    if (!valid) for (const term of ['contracts/numbers.md','bad','multipleOf']) assert.ok((result.stdout+result.stderr).includes(term),term);
    assert.deepEqual(snapshot(repo),before,'source/Git bytes, inventory and modes');
    assert.deepEqual(snapshot(state),prior,'state bytes, inventory and modes');
    assert.equal(fs.existsSync(auth),false,'no gh calls');
    assert.equal(connections,0,'no configured Runtime connections');
  } finally {
    await new Promise(resolve => server.close(resolve));
    fs.rmSync(sandbox,{recursive:true,force:true});
  }
});
