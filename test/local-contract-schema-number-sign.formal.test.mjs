import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { validateContract } from '../src/runtime-preflight.mjs';

const root = dirname(dirname(fileURLToPath(import.meta.url)));
// DefinitionSignDomain: all 12 raw literals, approved before execution.
// Canonical schema rule: multipleOf is strictly positive. This is definition
// validation only; no extreme-operand value arithmetic is claimed.
const domain = [
  ['-1', false], ['0', false], ['1', true], ['-0', false],
  ['-0.1', false], ['0.1', true],
  ['-0.10000000000000001', false], ['0.10000000000000001', true],
  ['-1e-9999', false], ['1e-9999', true],
  ['-1e9999', false], ['1e9999', true],
];
const schema = token => `{"type":"number","multipleOf":${token}}`;
for (const [token, positive] of domain) {
  test(`formal definition sign API: ${token}`, () => {
    const result = validateContract({schema_json:schema(token)});
    assert.equal(result.schema_problems.length > 0, !positive,
      `${token}: schema definition requires strictly positive multipleOf`);
    assert.deepEqual(result.value_problems, [], 'schema-only is not a value mismatch');
    assert.deepEqual(result.unproved, [], 'raw sign establishes schema validity');
    for (const problem of result.schema_problems) {
      assert.match(problem.code, /^graph-schema-/);
      assert.equal(typeof problem.pointer, 'string');
      assert.ok(problem.rule.includes('multipleOf'));
    }
  });
  test(`formal definition sign actual CLI unused record: ${token}`, () => {
    const repo = fs.mkdtempSync(join(tmpdir(), 'pdd-formal-definition-sign-'));
    try {
      fs.mkdirSync(join(repo, 'contracts'));
      const text = `### Sign\n\n\`\`\`json\n${schema(token)}\n\`\`\`\n`;
      const path = join(repo, 'contracts/sign.md');
      fs.writeFileSync(path, text);
      assert.equal(spawnSync('git', ['init', '-q'], {cwd:repo}).status, 0);
      assert.equal(spawnSync('git', ['add', '.'], {cwd:repo}).status, 0);
      const result = spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'contracts', '--check'], {
        cwd:repo, encoding:'utf8', env:{...process.env,PDD_STATE_DIR:join(repo,'.private-state')},
      });
      assert.equal(result.error, undefined, 'CLI launched');
      assert.equal(result.signal, null, 'CLI terminated naturally');
      const output = result.stdout + result.stderr;
      assert.equal(result.status, positive ? 0 : 4, `${token}: ${output}`);
      if (!positive) for (const term of ['contracts/sign.md', '#Sign', 'multipleOf'])
        assert.ok(output.includes(term), `${term}: ${output}`);
      assert.equal(fs.readFileSync(path,'utf8'),text,'raw source unchanged');
      assert.equal(fs.existsSync(join(repo,'.private-state')),false,'no private state created');
    } finally { fs.rmSync(repo,{recursive:true,force:true}); }
  });
}
