import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { runCheck, runTry, readTryOwner } from '../src/runtime-client.mjs';
import { createTryTools } from '../src/try-mcp.mjs';
import { fillHashes, interfaceBlocks, proseSha256 } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';

const spec = JSON.parse(readFileSync(new URL('./runtime/try-source-identity-cases.json', import.meta.url), 'utf8'));
const findCase = id => {
  const entry = spec.cases.find(item => item.id === id);
  assert.ok(entry, `missing case ${id}`);
  return entry;
};

function withEngine(job, rawEngine) {
  const copy = { ...job };
  if (rawEngine === undefined) return copy;
  if (rawEngine === null) delete copy.engine_sha;
  else copy.engine_sha = rawEngine;
  return copy;
}

function tryHandler({ engine, onModel, onState } = {}) {
  return (entry, f) => {
    if (entry.url.endsWith('/tests')) return { status: 404, json: { error: { code: 'not-found', message: 'The requested run or session was not found.' } } };
    if (entry.url.endsWith('/model') && onModel) return onModel(entry, f);
    if (entry.url.endsWith('/state') && onState) return onState(entry, f);
    if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId) };
    if (entry.command === 'try') return { status: 200, json: withEngine(f.tryJob(entry.request.requestId), engine) };
    return { status: 200, json: withEngine(f.tryJob(entry.url.split('/').at(-1)), engine) };
  };
}

test('try-source-identity case inventory matches Story criteria', () => {
  const story = readFileSync(new URL('../user_stories/try-source-identity.md', import.meta.url), 'utf8');
  for (const criterion of spec.criteria) assert.ok(story.includes(criterion.text), `criterion ${criterion.id} missing from Story`);
  assert.deepEqual(spec.cases.map(item => item.id), [
    'files-text-and-json-digest',
    'simulate-browser-and-reuse-identity',
    'simulate-door-stderr-lossless',
    'mcp-try-open-and-state-identity',
  ]);
});

test('case files-text-and-json-digest: pdd test --files text and --json match uploaded Try archive digest offline', async t => {
  const vector = findCase('files-text-and-json-digest');
  const setup = harbor(t, root => rmSync(join(root, 'tests/unknown-item.json')));
  let networkRequests = 0;
  const offlineExtra = {
    gh: () => { throw new Error('files must not call gh'); },
    fetch: async () => { networkRequests += 1; throw new Error('files must not make network calls'); },
  };
  const { ports: textPorts } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, offlineExtra);
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--files': true } }, textPorts), vector.expected.exit_code);
  const shaMatch = textPorts.stdout.text.match(/^Source SHA-256: ([0-9a-f]{64})$/m);
  assert.equal(Boolean(shaMatch), vector.expected.text_has_source_sha256_line);

  const { ports: jsonPorts } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, offlineExtra);
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--files': true, '--json': true } }, jsonPorts), vector.expected.exit_code);
  const parsed = JSON.parse(jsonPorts.stdout.text);
  assert.equal(parsed.source_sha256, shaMatch[1]);
  assert.equal(networkRequests, vector.expected.network_requests);

  const fake = await fakeRuntime(t, tryHandler());
  const { ports: tryPorts } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true } }, tryPorts), 0, tryPorts.stderr.text);
  const tryPost = fake.posts.find(post => post.command === 'try');
  assert.equal(parsed.source_sha256 === tryPost.request.source_sha256, vector.expected.json_source_sha256_matches_uploaded_try_request);
});

test('case simulate-browser-and-reuse-identity: engine_sha present, unknown/absent fallback, and legacy reuse safety', async t => {
  const vector = findCase('simulate-browser-and-reuse-identity');
  const setup = harbor(t, root => rmSync(join(root, 'tests/unknown-item.json')));
  const engine = 'eae2202a68d00ab762fcbbf1eba0d8607a132a15';
  const fake = await fakeRuntime(t, tryHandler({ engine }));
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };

  const { ports: first } = portsFor(env);
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true } }, first), vector.expected.exit_code, first.stderr.text);
  const uploadedSha = fake.posts.find(post => post.command === 'try').request.source_sha256;
  const expectedLine = vector.expected.stdout_contains.replace('<request.source_sha256>', uploadedSha);
  const firstLines = first.stdout.text.trim().split('\n');
  assert.equal(firstLines[firstLines.findIndex(line => line.startsWith('Try budget ')) + 1], expectedLine);

  const { ports: reused } = portsFor(env);
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true } }, reused), vector.expected.exit_code, reused.stderr.text);
  assert.ok(reused.stdout.text.includes(expectedLine));

  // Absent or "unknown" engine_sha prints Try source: sha256:<64-hex> without "; engine: ...".
  for (const rawEngine of ['unknown', null]) {
    const sub = harbor(t, root => rmSync(join(root, 'tests/unknown-item.json')));
    const subFake = await fakeRuntime(t, tryHandler({ engine: rawEngine }));
    const { ports } = portsFor({ HOME: sub.home, PDD_RUNTIME_URL: subFake.origin, PDD_STATE_DIR: sub.state });
    assert.equal(await runTry({ cwd: sub.repo, words: ['place-order'], options: { '--no-open': true } }, ports), 0, ports.stderr.text);
    const sha = subFake.posts.find(post => post.command === 'try').request.source_sha256;
    const lines = ports.stdout.text.trim().split('\n');
    assert.equal(lines[lines.findIndex(line => line.startsWith('Try budget ')) + 1], `Try source: sha256:${sha}`);
  }

  // Reused legacy record without saved or server source_sha256 must not claim edited local capture.sha256.
  const repoFiles = readdirSync(join(setup.state, 'repos')).map(name => join(setup.state, 'repos', name));
  for (const repoFile of repoFiles) {
    const saved = JSON.parse(readFileSync(repoFile, 'utf8'));
    if (saved.tries?.['tests/place-order.json']) {
      delete saved.tries['tests/place-order.json'].source_sha256;
      writeFileSync(repoFile, JSON.stringify(saved));
    }
  }
  const rawPrompt = readFileSync(join(setup.repo, PLACE), 'utf8').replace('Place an order', 'Place one order').replace('"status": "approved"', '"status": "draft"');
  writeFileSync(join(setup.repo, PLACE), rawPrompt);
  fillHashes({ root: setup.repo });
  const { ports: legacyReused } = portsFor(env);
  assert.equal(await runTry({ cwd: setup.repo, words: ['place-order'], options: { '--no-open': true } }, legacyReused), 0, legacyReused.stderr.text);
  assert.doesNotMatch(legacyReused.stdout.text, /Try source:/, 'legacy reuse must not print unuploaded local capture digest');
});

test('case simulate-door-stderr-lossless: --cli and --serve print Try source to stderr and keep stdout lossless', async t => {
  const vector = findCase('simulate-door-stderr-lossless');
  const cliEngine = '11223344556677889900aabbccddeeff00112233';

  // --cli door
  const cliSetup = harbor(t, root => {
    rmSync(join(root, 'tests/unknown-item.json'));
    const input = { type: 'object', properties: { argv: { type: 'array', items: { type: 'string' } } }, required: ['argv'], additionalProperties: false };
    const result = { type: 'object', properties: { stdout: { type: 'string' }, stderr: { type: 'string' }, exit_code: { type: 'integer' } }, required: ['stdout', 'stderr', 'exit_code'], additionalProperties: false };
    const iface = { status: 'draft', prose_sha256: '', entries: [{ operation: 'main', input_schema: input, result_schema: result, errors: [] }], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 }, conventions: ['input_schema', 'result_schema'].map(key => ({ path: `/entries/0/${key}`, convention: 'cli' })) };
    const content = () => `# paperclip\n\nPrint words.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\x60\x60\x60json\n${JSON.stringify(iface)}\n\x60\x60\x60\n</details>\n`;
    iface.prose_sha256 = proseSha256(content());
    writeFileSync(join(root, PLACE), content());
    writeFileSync(join(root, 'user_stories/place-order.md'), '# Arguments\n\nAs a person, I want words printed, so that I see them.\n\n## Acceptance criteria\n\n1. Words print.\n');
    writeFileSync(join(root, 'tests/place-order.json'), JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/place-order.md',
      criteria: [{ id: 'AC1', text: 'Words print.' }],
      initial_world: {}, simulation: {}, context: [],
      steps: [{ step_id: 's1', entry_path: PLACE, operation: 'main', input: { argv: ['hi'] }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'hi\n' }] }],
    }, null, 2) + '\n');
  });
  const cliFake = await fakeRuntime(t, tryHandler({
    engine: cliEngine,
    onModel: () => ({ status: 200, json: { calls: { cap: 400, remaining: 400 } } }),
  }));
  const cliPorts = portsFor(
    { HOME: cliSetup.home, PDD_RUNTIME_URL: cliFake.origin, PDD_STATE_DIR: cliSetup.state },
    { stdin: Readable.from([]), shell: async () => 0, openUrl: async () => assert.fail('door must not open browser') },
  ).ports;
  assert.equal(await runTry({ cwd: cliSetup.repo, words: ['place-order'], options: { '--cli': true } }, cliPorts), 0, cliPorts.stderr.text);
  const cliSha = cliFake.posts.find(post => post.command === 'try').request.source_sha256;
  assert.equal(cliPorts.stderr.text.includes(`Try source: sha256:${cliSha}; engine: ${cliEngine}`), vector.expected.stderr_contains_try_source);
  assert.equal(!cliPorts.stdout.text.includes('Try source:'), vector.expected.stdout_omits_try_source);

  // --serve door
  const serveSetup = harbor(t, root => {
    rmSync(join(root, 'tests/unknown-item.json'));
    const source = readFileSync(join(root, PLACE), 'utf8');
    const block = interfaceBlocks(source)[0];
    const iface = JSON.parse(block[1]);
    iface.status = 'draft';
    iface.entries[0].input_schema.title = 'HTTP POST /orders';
    const next = source.replace(block[1], JSON.stringify(iface));
    const updated = next.replace(iface.prose_sha256, proseSha256(next));
    writeFileSync(join(root, PLACE), updated);
  });
  const serveFake = await fakeRuntime(t, tryHandler({
    engine: cliEngine,
    onModel: () => ({
      status: 200,
      json: { entries: [{ entry_path: PLACE, operation: 'place_order', http: { method: 'POST', path: '/orders' }, input_schema: { type: 'object', properties: {}, required: [], additionalProperties: true } }], calls: { cap: 400, remaining: 400 } },
    }),
  }));
  const servePorts = portsFor(
    { HOME: serveSetup.home, PDD_RUNTIME_URL: serveFake.origin, PDD_STATE_DIR: serveSetup.state },
    { serve: async () => {}, openUrl: async () => assert.fail('door must not open browser') },
  ).ports;
  assert.equal(await runTry({ cwd: serveSetup.repo, words: ['place-order'], options: { '--serve': '0' } }, servePorts), 0, servePorts.stderr.text);
  const serveSha = serveFake.posts.find(post => post.command === 'try').request.source_sha256;
  assert.equal(servePorts.stderr.text.includes(`Try source: sha256:${serveSha}; engine: ${cliEngine}`), vector.expected.stderr_contains_try_source);
  assert.equal(!servePorts.stdout.text.includes('Try source:'), vector.expected.stdout_omits_try_source);
});

test('case mcp-try-open-and-state-identity: readTryOwner model-over-record precedence and try_open / try_state', async t => {
  const vector = findCase('mcp-try-open-and-state-identity');
  const setup = harbor(t, root => rmSync(join(root, 'tests/unknown-item.json')));
  const modelSha = 'f'.repeat(64);
  const modelEngine = 'eae2202a68d00ab762fcbbf1eba0d8607a132a15';
  const recordEngine = '0123456789abcdef0123456789abcdef01234567';
  let includeModelIdentity = true;

  const fake = await fakeRuntime(t, tryHandler({
    engine: recordEngine,
    onModel: () => ({
      status: 200,
      json: {
        entries: [{ entry_path: PLACE, operation: 'place_order', input_schema: { type: 'object' }, result_schema: { type: 'object' } }],
        calls: { cap: 400, remaining: 399 },
        ...(includeModelIdentity ? { source_sha256: modelSha.toUpperCase(), engine_sha: modelEngine.toUpperCase() } : { engine_sha: 'unknown' }),
      },
    }),
    onState: () => ({ status: 200, json: { world: { kv: { ready: true } }, actions: [] } }),
  }));
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state };
  const { ports } = portsFor(env);

  const tools = createTryTools({ cwd: setup.repo, env }, ports);
  const opened = await tools.call('try_open', {});
  const state = await tools.call('try_state', {});
  assert.equal(opened.source_sha256 === modelSha && state.source_sha256 === modelSha, vector.expected.source_sha256_returned);
  assert.equal(opened.engine_sha === modelEngine && state.engine_sha === modelEngine, vector.expected.engine_sha_returned);
  assert.deepEqual(opened.data_now, { kv: { ready: true } });
  assert.deepEqual(opened.calls, { cap: 400, remaining: 399 });

  // Fallback to saved record when /model omits source_sha256 or reports engine_sha: "unknown"
  includeModelIdentity = false;
  const uploadedSha = fake.posts.find(post => post.command === 'try').request.source_sha256;
  const fallbackOwner = await readTryOwner({ cwd: setup.repo }, ports);
  assert.equal(fallbackOwner.source_sha256, uploadedSha);
  assert.equal(fallbackOwner.engine_sha, recordEngine);
  const fallbackState = await tools.call('try_state', {});
  assert.equal(fallbackState.source_sha256, uploadedSha);
  assert.equal(fallbackState.engine_sha, recordEngine);
});
