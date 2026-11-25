import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {
  FORMAL_VECTORS_SCHEMA,
  exportFormalVectors,
  normalizeItfValue,
} from '../../../src/core/lint/vector-export.mjs';
import { compileScenario, parseExactScenarioJson } from '../../../src/scenario-compile.mjs';

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

test('formal PRNG (250 seeded formal specs & ITF traces): every accepted export compiles cleanly, respects maxSteps, and preserves exact BigInt', () => {
  const rng = mulberry32(0x3704FACE);

  for (let trial = 0; trial < 250; trial++) {
    const caseCount = 1 + Math.floor(rng() * 32);
    const maxSteps = 2 + Math.floor(rng() * 14);
    const split = rng() < 0.65;
    const useBigInt = rng() < 0.5;
    const unsafeInt = 9007199254740993n + BigInt(trial * 7);

    const cases = Array.from({ length: caseCount }, (_, i) => {
      const isErr = rng() < 0.25;
      const val = useBigInt && i === 0 ? unsafeInt : Math.floor(rng() * 10000);
      return isErr
        ? { id: `c-${i + 1}`, criterion: '1', input: { v: val }, error: 'rejected' }
        : { id: `c-${i + 1}`, criterion: '1', input: { v: val }, expect: { '/out': val } };
    });

    const spec = {
      schema_version: FORMAL_VECTORS_SCHEMA,
      entry_path: 'prompts/calc.prompt.md',
      default_op: 'eval',
      cases,
    };
    const res = exportFormalVectors(spec, {
      maxSteps,
      split,
      outputBasePath: 'tests/calc.formal.json',
    });

    if (caseCount > maxSteps && !split) {
      assert.equal(res.ok, false, `trial ${trial}: must refuse when caseCount > maxSteps without split`);
      assert.equal(res.refusal.code, 'max-steps-exceeded');
      continue;
    }

    assert.equal(res.ok, true, `trial ${trial}: unexpected refusal ${JSON.stringify(res.refusal)}`);
    const expectedChunks = Math.ceil(caseCount / maxSteps);
    assert.equal(res.files.length, expectedChunks);

    let totalSteps = 0;
    for (const file of res.files) {
      assert.ok(file.step_count >= 1 && file.step_count <= maxSteps, `chunk step_count ${file.step_count} > ${maxSteps}`);
      totalSteps += file.step_count;

      // Exact round-trip through parseExactScenarioJson + compileScenario (0 refusals, 0 patch-null warnings)
      const reparsed = parseExactScenarioJson(file.text);
      const compiled = compileScenario(reparsed, { path: file.path });
      assert.equal(compiled.refusal, null, `trial ${trial}: exported Short JSON failed compile: ${JSON.stringify(compiled.refusal)}`);
      assert.equal(
        (compiled.warnings ?? []).filter(w => w.code === 'patch-null-deletes-key').length,
        0,
      );
    }
    assert.equal(totalSteps, caseCount, `trial ${trial}: total steps must equal caseCount`);

    if (useBigInt) {
      const firstParsed = parseExactScenarioJson(res.files[0].text);
      assert.equal(firstParsed.steps[0].input.v, unsafeInt, `trial ${trial}: BigInt rounded`);
    }
  }
});

test('formal boundary grid: Quint ITF #bigint exactness and fail-closed invalid cases', () => {
  const bigStrs = ['-9007199254740995', '-9007199254740991', '0', '42', '9007199254740991', '9007199254740993', '123456789012345678901234567890'];
  for (const s of bigStrs) {
    const unwrapped = normalizeItfValue({ '#bigint': s });
    assert.equal(String(unwrapped), s, `exact integer preservation failed for ${s}`);
  }

  // Every zero-check or invalid-pointer case fails closed
  const invalidPointers = ['', 'foo', 'a/b', '/bad~2escape', '/trailing~'];
  for (const ptr of invalidPointers) {
    const res = exportFormalVectors({
      schema_version: FORMAL_VECTORS_SCHEMA,
      entry_path: 'prompts/calc.prompt.md',
      default_op: 'eval',
      cases: [{ id: 'c1', input: {}, expect: { [ptr]: 1 } }],
    });
    assert.equal(res.ok, false, `invalid pointer "${ptr}" must be refused`);
    assert.equal(res.refusal.code, 'invalid-pointer');
  }

  const zeroCheck = exportFormalVectors({
    schema_version: FORMAL_VECTORS_SCHEMA,
    entry_path: 'prompts/calc.prompt.md',
    default_op: 'eval',
    cases: [{ id: 'c1', input: { x: 1 } }],
  });
  assert.equal(zeroCheck.ok, false);
  assert.equal(zeroCheck.refusal.code, 'missing-checks');
});
