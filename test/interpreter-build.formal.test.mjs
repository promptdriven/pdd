import test from 'node:test';
import assert from 'node:assert/strict';
import { runDetailedVersion } from '../src/interpreter-version.mjs';

// Bounded semantic check of user_stories/interpreter-build.md, Rules to check,
// refined by prompts/cli/interpreter-version.prompt.md. These are decisions at
// the public operation with injected ports. Native process/fetch timing is not
// proved here. The oracle uses character sets, not the product's regular expressions.
const version = '9.8.7-fixture+local';
const origin = 'https://formal-metadata.invalid';
const token = 'FORMAL-PRIVATE-TOKEN';
const remote = 'FORMAL-PRIVATE-REMOTE\u001b[31m';
const hex = '0123456789abcdefABCDEF';
const alphanumeric = 'abcdefghijklmnopqrstuvwxyz0123456789';
const suffixCharacters = alphanumeric + '._-';
const sha = 'abcdef0123456789abcdef0123456789abcdef01';
assert.equal(sha.length, 40, 'the known metadata fixture must exercise a valid full build');
const keys = ['interface', 'test', 'app_map'];
const labels = ['Interface formats', 'Test formats', 'App-map formats'];
const throwReply = Symbol('callback throws');
const asciiAndUnicode = [...Array.from({ length: 128 }, (_, i) => String.fromCharCode(i)), '\u0085', 'é', '\u2028', '\u2029'];
const metadata = (engine_sha = sha, formats = {}) => ({ engine_sha, formats, message: remote, model: remote, api_version: remote });
const reply = value => ({ status: 200, body: JSON.stringify(value) });

function buildIsSafe(value) {
  return typeof value === 'string' && value.length === 40 && [...value].every(char => hex.includes(char));
}

function listDisplay(value) {
  if (!Array.isArray(value) || value.length > 32) return 'unknown';
  for (const id of value) {
    if (typeof id !== 'string' || !id.startsWith('prompt-runtime.')) return 'unknown';
    const tail = id.slice('prompt-runtime.'.length);
    if (tail.length < 1 || tail.length > 128 || !alphanumeric.includes(tail[0])) return 'unknown';
    if ([...tail].some(char => !suffixCharacters.includes(char))) return 'unknown';
  }
  return value.length === 0 ? 'none' : value.join(', ');
}

function expectedResult(answer) {
  const lines = [`PDD CLI: ${version}`];
  let value;
  try { if (answer?.status === 200 && typeof answer.body === 'string') value = JSON.parse(answer.body); }
  catch { /* Invalid JSON cannot report a known build. */ }
  if (value === null || typeof value !== 'object' || Array.isArray(value) || !buildIsSafe(value.engine_sha)) {
    lines.push('PDD interpreter: unknown');
  } else {
    lines.push(`PDD interpreter: ${value.engine_sha.toLowerCase()}`);
    for (let i = 0; i < keys.length; i++) lines.push(`${labels[i]}: ${listDisplay(value.formats?.[keys[i]])}`);
  }
  return { exit_code: 0, stdout: lines.join('\n') + '\n', stderr: '' };
}

async function check(options = {}) {
  // Preserve explicit undefined replies as part of the domain.
  const address = Object.hasOwn(options, 'address') ? options.address : { valid: true, origin };
  const credentials = Object.hasOwn(options, 'credentials') ? options.credentials : { token };
  const answer = Object.hasOwn(options, 'answer') ? options.answer : reply(metadata());
  const { env = {}, id = '' } = options;
  const calls = [];
  const respond = value => { if (value === throwReply) throw new Error(remote); return value; };
  const actual = await runDetailedVersion({ version, env }, {
    resolveOrigin: async args => { calls.push(['origin', args]); return respond(address); },
    readToken: async args => { calls.push(['token', args]); return respond(credentials); },
    getMetadata: async args => { calls.push(['metadata', args]); return respond(answer); },
    fetch: async () => { calls.push(['unexpected-fetch']); throw new Error(remote); },
  });
  const expectedCalls = [['origin', { env: Object.hasOwn(env, 'PDD_RUNTIME_URL') ? { PDD_RUNTIME_URL: env.PDD_RUNTIME_URL } : {} }]];
  const readableAddress = address !== throwReply && address?.valid;
  const readableToken = credentials !== throwReply && typeof credentials?.token === 'string' && credentials.token.trim() !== '';
  if (readableAddress) expectedCalls.push(['token', { timeoutMs: 2000 }]);
  if (readableAddress && readableToken) expectedCalls.push(['metadata', {
    origin: address.origin, path: '/v1/version', method: 'GET', token: credentials.token,
    timeoutMs: 10000, redirect: 'manual',
  }]);
  assert.deepEqual(calls, expectedCalls, `${id}: one ordered, bounded GET only after credentials`);
  const expected = expectedResult(readableAddress && readableToken && answer !== throwReply ? answer : undefined);
  assert.deepEqual(actual, expected, `${id}: Story output rule`);
  assert.ok(!actual.stdout.includes(token) && !actual.stdout.includes('FORMAL-PRIVATE-REMOTE'), `${id}: no credential or remote prose`);
  for (const char of actual.stdout) {
    const code = char.charCodeAt(0);
    assert.ok(char === '\n' || code >= 32 && code !== 127 && !(code >= 128 && code <= 159), `${id}: no terminal controls except line endings`);
  }
}

test('bounded build oracle: every single-position ASCII/Unicode replacement and lengths 0..42', async t => {
  const builds = new Set();
  const baseline = 'a'.repeat(40);
  for (let position = 0; position < 40; position++) for (const char of asciiAndUnicode) {
    builds.add(baseline.slice(0, position) + char + baseline.slice(position + 1));
  }
  for (let length = 0; length <= 42; length++) builds.add('a'.repeat(length));
  // Include nonuniform full lowercase/uppercase builds, not only repeated digits.
  builds.add(sha); builds.add(sha.toUpperCase());
  const nonStrings = [undefined, null, false, true, 40, {}, [], [sha]];
  for (const build of [...builds, ...nonStrings]) {
    await check({ answer: reply({ ...metadata(), engine_sha: build }), id: `build ${JSON.stringify(build)}` });
  }
  t.diagnostic(`Proved (bounded): ${builds.size + nonStrings.length} build cases; 40 positions × 132 replacement characters, lengths 0..42, 2 mixed builds, 8 nonstrings (deduplicated strings).`);
});

test('bounded format oracle: ID byte boundaries, every format slot, list sizes and independent fields', async t => {
  const ids = new Set(['wrong-prefix.a', 'PROMPT-RUNTIME.a', 'prompt-runtime.A', 'prompt-runtime.a, b']);
  for (const char of asciiAndUnicode) for (const tail of [char, char + 'a', 'a' + char]) ids.add('prompt-runtime.' + tail);
  for (let length = 0; length <= 129; length++) ids.add('prompt-runtime.' + 'a'.repeat(length));
  const values = [...ids].map(id => [id]);
  values.push(undefined, null, false, 1, 'prompt-runtime.a', {}, [null], [false], [1], [{}], [[]]);
  for (const count of [0, 1, 2, 32, 33]) {
    values.push(Array.from({ length: count }, (_, i) => `prompt-runtime.format-${count - i}`));
    for (let position = 0; position < count; position++) {
      const list = Array(count).fill('prompt-runtime.a'); list[position] = 'prompt-runtime.a\n'; values.push(list);
    }
  }
  let count = 0;
  for (const value of values) for (const key of keys) {
    const formats = { interface: ['prompt-runtime.z', 'prompt-runtime.a'], test: [], app_map: ['prompt-runtime.app-map.v1'] };
    formats[key] = value;
    await check({ answer: reply(metadata(sha, formats)), id: `formats ${key} ${JSON.stringify(value)}` }); count++;
  }
  const fieldStates = [undefined, [], ['prompt-runtime.z', 'prompt-runtime.a'], ['prompt-runtime.a\n']];
  for (const first of fieldStates) for (const second of fieldStates) for (const third of fieldStates) {
    await check({ answer: reply(metadata(sha, { interface: first, test: second, app_map: third })), id: `independent fields ${count}` }); count++;
  }
  for (const formats of [undefined, null, false, 3, 'remote prose', [], {}]) {
    await check({ answer: reply({ ...metadata(), formats }), id: `formats container ${JSON.stringify(formats)}` }); count++;
  }
  t.diagnostic(`Proved (bounded): ${count} format cases; ${ids.size} generated IDs in each of 3 slots, 11 malformed values, sizes 0/1/2/32/33 with every poisoned position, 4³ field states, 7 containers.`);
});

test('bounded access oracle: every selected origin/token/status combination, then HTTP statuses 100..599', async t => {
  const addresses = [{ valid: true, origin }, { valid: false, origin: '' }, null, undefined, throwReply];
  const credentials = [{ token }, { token: `  ${token}  ` }, { token: '' }, { token: ' \t\r\n' }, {}, { token: null }, { token: 7 }, null, undefined, throwReply];
  const statuses = [200, 201, 204, 301, 302, 307, 308, 400, 401, 403, 404, 429, 500, 503];
  const environments = [{}, { PDD_RUNTIME_URL: origin, HOME: '/private-home', PATH: '/private-path', UNRELATED: remote }];
  let count = 0;
  for (const address of addresses) for (const credential of credentials) for (const status of statuses) for (const env of environments) {
    await check({ address, credentials: credential, answer: { status, body: JSON.stringify(metadata()) }, env, id: `access ${count}` }); count++;
  }
  for (let status = 100; status <= 599; status++) {
    await check({ answer: { status, body: JSON.stringify(metadata()) }, id: `HTTP ${status}` }); count++;
  }
  for (const status of [undefined, null, '200', true, 0, 600]) {
    await check({ answer: { status, body: JSON.stringify(metadata()) }, id: `status type ${JSON.stringify(status)}` }); count++;
  }
  t.diagnostic(`Proved (bounded): ${count} access cases; 5 origins × 10 credential states × 14 statuses × 2 env states, all HTTP integers 100..599, 6 malformed/outside statuses.`);
});

test('bounded response oracle: malformed JSON, top-level types, missing build, response types and throws', async t => {
  const answers = [throwReply, undefined, null, false, {}, { status: 200 },
    ...[null, false, 1, {}, []].map(body => ({ status: 200, body })),
    ...['', '{', '{"engine_sha":', 'not-json ' + remote, '{} {}'].map(body => ({ status: 200, body })),
    ...[null, false, true, 0, 1, '', remote, [], [metadata()], {}, { engine_sha: null }].map(reply)];
  for (let i = 0; i < answers.length; i++) await check({ answer: answers[i], id: `malformed response ${i}` });
  t.diagnostic(`Proved (bounded): ${answers.length} malformed/throw response cases, with unknown output and exit 0.`);
});
