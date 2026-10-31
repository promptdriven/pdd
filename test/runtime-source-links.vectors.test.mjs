import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

test('LINK native inventory replay: every frozen case executes its named public-boundary test',()=>{
  const inventory=JSON.parse(readFileSync(new URL('./runtime/read-in-repo-links.json',import.meta.url),'utf8'));
  assert.equal(inventory.schema_version,'pdd.native-cases.v1');
  const replay=spawnSync(process.execPath,['--test','--test-reporter=tap',inventory.native_test],{
    cwd:fileURLToPath(new URL('../',import.meta.url)),env:Object.fromEntries(Object.entries(process.env).filter(([key])=>key!=='NODE_TEST_CONTEXT')),encoding:'utf8',stdio:['ignore','pipe','pipe'],maxBuffer:8*1024*1024,
  });
  assert.equal(replay.status,0,`${replay.stdout}\n${replay.stderr}`);
  const executed=[...replay.stdout.matchAll(/^ok \d+ - (.+)$/gm)].map(match=>match[1]);
  assert.deepEqual(executed,inventory.cases.map(item=>item.name));
  assert.equal(executed.length,inventory.cases.length);
});
