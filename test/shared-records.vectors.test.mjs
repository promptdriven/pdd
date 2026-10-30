import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { expandSource } from '../src/contract-refs.mjs';

for (const name of ['shared-records','shared-seed']) test(`VECTOR ${name}: immutable Runtime cases through expandSource`, async t => {
  const scenario = JSON.parse(readFileSync(new URL(`runtime/${name}.json`, import.meta.url), 'utf8'));
  const world = structuredClone(scenario.initial_world);
  for (const step of scenario.steps) await t.test(step.step_id, () => {
    const counts = { 'files.stat':0, 'files.read':0 };
    const files = {
      stat({path}) {
        counts['files.stat']++;
        const file = Object.hasOwn(world.files,path) ? world.files[path] : null;
        return { exists: !!file, is_symlink: file?.is_symlink ?? false, size: Buffer.byteLength(file?.content ?? '') };
      },
      read({path}) { counts['files.read']++; return { content: world.files[path].content }; },
    };
    let result, error;
    try { result = expandSource(step.input,files); } catch (caught) { error = caught; }
    if (step.expected_error) assert.equal(error?.code,step.expected_error);
    else assert.ifError(error);
    for (const check of step.checks) {
      const roots = { result, error, world, calls: {resources:counts} };
      let got = roots[check.target];
      for (const key of check.path === '' ? [] : check.path.slice(1).split('/').map(key => key.replace(/~1/g,'/').replace(/~0/g,'~'))) got = got?.[key];
      assert.equal(check.op,'equals',`${name}/${step.step_id}: unmapped check operation`);
      assert.deepEqual(got,check.value,`${name}/${step.step_id}/${check.criterion_id} ${check.target} ${check.path}`);
    }
  });
});
