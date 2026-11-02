import test from 'node:test';
import assert from 'node:assert/strict';
import { checkInput, interfaceSchemaProblems } from '../src/runtime-preflight.mjs';

const text = { type: 'string' };
const object = properties => ({ type: 'object', properties, required: Object.keys(properties), additionalProperties: false });
const iface = proof => ({ status: 'draft', prose_sha256: '', calls: [], resources: [], limits: { max_steps: 4, max_model_calls: 4 },
  entries: [{ operation: 'sign_in', input_schema: object({ secret: text }), result_schema: object({ proof, status: text }), errors: [] }] });

// Wrong: pdd refused writeOnly before upload, so a schema could not hide a made-up secret in the report.
test('WRITE-ONLY1: a Boolean writeOnly annotation passes the local schema check', () => {
  assert.deepEqual(interfaceSchemaProblems(iface({ ...text, writeOnly: true })), []);
  assert.deepEqual(interfaceSchemaProblems(iface({ ...text, writeOnly: false })), []);
});

test('WRITE-ONLY2: a writeOnly that is not true or false is refused with its JSON pointer', () => {
  const problems = interfaceSchemaProblems(iface({ ...text, writeOnly: 'yes' }));
  assert.deepEqual(problems.map(item => [item.code, item.pointer]),
    [['graph-schema-invalid', '/entries/0/result_schema/properties/proof']]);
});

// Wrong: a field named "secret" with made-up data is ordinary test input; writeOnly changes nothing in the input check.
test('WRITE-ONLY3: test input under a writeOnly or secret-named field is still checked, with no warning', () => {
  const schema = object({ secret: { ...text, writeOnly: true }, claim_token: text });
  assert.deepEqual(checkInput({ secret: 'test-only-attempt-proof', claim_token: 'claim-1' }, schema, 0), { refusals: [], warnings: [] });
  assert.equal(checkInput({ secret: 7, claim_token: 'claim-1' }, schema, 0).refusals.length, 1);
});
