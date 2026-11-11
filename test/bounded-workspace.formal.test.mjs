import './helpers/test-home.mjs';
// Independent finite checks derived from the six issue-2781 Stories' Rules to check.
// These domains are synthetic; enumeration establishes only the bounds stated below.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {join, dirname} from 'node:path';
import {tmpdir} from 'node:os';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {syncBuiltinESMExports} from 'node:module';
import {loadRuntimeWorkspace, allowsRuntimePath, requireRuntimePath} from '../src/runtime/runtime-workspace.mjs';
import {captureSource, fillHashes, createStrictSourceAccess} from '../src/runtime/runtime-preflight.mjs';
import {askAgent} from '../src/agent-adapters.mjs';
import {saveDoorCase, acquireCaseWriteOwnership, applyPendingCase, runTry} from '../src/runtime/runtime-client.mjs';
import {migrateRuntimeWorkspace} from '../src/runtime/runtime-workspace-migration.mjs';
import {associateEvidenceWorkspace, readEvidenceEligibility} from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';

const sha = bytes => createHash('sha256').update(bytes).digest('hex');
// This fixture has one known literal interface wrapper. Its independent oracle
// hashes the authored outside bytes, without calling the production hash/parser.
function authoredHash(text) {
  const start = text.indexOf('<details>'), end = text.indexOf('</details>') + '</details>'.length;
  assert.ok(start >= 0 && end > start);
  return sha(text.slice(0, start) + text.slice(end));
}
const read = (root, path) => fs.readFileSync(join(root, path), 'utf8');
function write(root, path, bytes) {
  fs.mkdirSync(dirname(join(root, path)), {recursive: true});
  fs.writeFileSync(join(root, path), bytes);
}
const json = (root, path, value) => write(root, path, JSON.stringify(value, null, 2) + '\n');
const closed = testPath => ({kind: 'closed-editor', testPath});
const stream = () => ({text: '', write(text) { this.text += text; }, isTTY: false});

function fixture(t) {
  const base = fs.mkdtempSync(join(tmpdir(), 'pdd-formal-2781-'));
  t.after(() => fs.rmSync(base, {recursive: true, force: true}));
  const root = join(base, 'repo'), home = join(base, 'home'), state = join(base, 'state');
  for (const dir of [root, home]) fs.mkdirSync(dir);
  const env = {...process.env, HOME: home, XDG_CONFIG_HOME: join(home, '.config'),
    PDD_STATE_DIR: state, GIT_CONFIG_NOSYSTEM: '1'};
  assert.equal(spawnSync('git', ['init', '-q'], {cwd: root, env}).status, 0);
  const story = 'simulation/user_stories/order.md', prompt = 'simulation/prompts/order.prompt.md';
  const tests = ['simulation/tests/order.json', 'simulation/tests/order.second.json'];
  write(root, story, '# Order\n\nI can keep a value.\n\n## Acceptance criteria\n\n1. Keep value.\n');
  const iface = {status: 'draft', prose_sha256: '', entries: [{operation: 'order',
    input_schema: {type: 'object', properties: {}, required: [], additionalProperties: false},
    result_schema: {type: 'integer'}, errors: []}], calls: [], resources: [],
  limits: {max_steps: 1, max_model_calls: 1}, conventions: []};
  let text = '# Order\n\nReturn a value.\n\n## Dependencies\n\n<details><summary>Runtime interface</summary>\n```json\n' +
    JSON.stringify(iface, null, 2) + '\n```\n</details>\n';
  text = text.replace('"prose_sha256": ""', '"prose_sha256": "' + authoredHash(text) + '"');
  write(root, prompt, text);
  const doc = {schema_version: 'prompt-runtime.program-scenario.v1', story_path: story,
    criteria: [{id: 'AC1', text: 'Keep value.'}], initial_world: {count: 0}, simulation: {}, context: [],
    steps: [{step_id: 'prior', entry_path: prompt, operation: 'order', input: {}, checks: [
      {criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 7},
      {criterion_id: 'AC1', target: 'world', path: '', op: 'equals', value: {count: 0}}
    ]}]};
  for (const path of tests) json(root, path, doc);
  write(root, 'private/ordinary.md', 'EXCLUDED-FORMAL-MARKER');
  json(root, 'pdd-workspace.json', {allowed_paths: ['simulation/']});
  const received = (target, world = 0, value = 9) => ({id: 'formal-case', name: 'formal-case',
    story_path: story, original_path: target, world_before: {count: world},
    test: {...doc, steps: [{step_id: 'formal-case', entry_path: prompt, operation: 'order', input: {},
      checks: [{criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value},
        {criterion_id: 'AC1', target: 'world', path: '', op: 'equals', value: {count: world}}]}]}});
  return {base, root, home, state, env, story, prompt, tests, doc, received};
}

// This observes actual native content reads, including the source reader's fd reads.
// It is deliberately independent of archive membership and returned read disclosures.
function observeReads(root, action) {
  const original = fs.readFileSync, open = fs.openSync, reads = [], opened = new Map();
  fs.openSync = function(path, ...args) {
    const descriptor = open.call(this, path, ...args);
    opened.set(descriptor, path);
    return descriptor;
  };
  fs.readFileSync = function(path, ...args) {
    const absolute = typeof path === 'number' ? opened.get(path) : path;
    if (typeof absolute === 'string' && absolute.startsWith(root + '/')) reads.push(absolute.slice(root.length + 1));
    return original.call(this, path, ...args);
  };
  syncBuiltinESMExports();
  try { return {value: action(), reads}; }
  finally { fs.readFileSync = original; fs.openSync = open; syncBuiltinESMExports(); }
}

test('FORMAL policy: all 8 entry subsets plus absence × 9 component-bound paths', t => {
  const entries = ['simulation/', 'contracts/shared.md', 'unused/'];
  const paths = ['simulation/a.md', 'simulation/sub/b.md', 'simulation', 'simulation/',
    'simulation-private/a.md', 'contracts/shared.md', 'contracts/shared.md/a', 'contracts/other.md', 'unused/x'];
  // Story oracle: exact file equality, or a strict descendant with equal complete components.
  const admits = (entry, path) => {
    if (!entry.endsWith('/')) return entry === path;
    const prefix = entry.slice(0, -1).split('/'), parts = path.split('/');
    return parts.length > prefix.length && parts[prefix.length] !== '' && prefix.every((p, i) => parts[i] === p);
  };
  const f = fixture(t);
  for (const mask of [-1, 0, 1, 2, 3, 4, 5, 6, 7]) {
    const allowed = entries.filter((_, i) => mask & (1 << i));
    if (mask === -1) fs.unlinkSync(join(f.root, 'pdd-workspace.json'));
    else json(f.root, 'pdd-workspace.json', {allowed_paths: allowed});
    const policy = loadRuntimeWorkspace({root: f.root});
    assert.equal(policy.configured, mask !== -1, 'absent policy cannot invent configured permission');
    assert.deepEqual(policy.allowed_paths, mask === -1 ? [] : allowed);
    for (const path of paths) {
      const expected = mask === -1 || allowed.some(entry => admits(entry, path));
      assert.equal(allowsRuntimePath(policy, path), expected, `${mask}: ${path}`);
      if (expected) assert.equal(requireRuntimePath(policy, {path}), path);
      else assert.throws(() => requireRuntimePath(policy, {path}), e => e.code === 'workspace-path-outside');
    }
  }
  t.diagnostic('81 path decisions; native policy load; directory components and no selection widening only.');
});

test('FORMAL capture: 2 permissions × 6 required-access routes, with independent actual-read observation', t => {
  for (const permitted of [false, true]) for (const route of ['dependency', 'context', 'include', 'prepare-read', 'prepare-stat', 'prepare-output']) {
    const f = fixture(t), target = 'private/ordinary.md';
    json(f.root, 'pdd-workspace.json', {allowed_paths: permitted ? ['simulation/', target] : ['simulation/']});
    const options = {tests: [f.tests[1]]};
    if (route === 'dependency') write(f.root, f.prompt, read(f.root, f.prompt).replace('## Dependencies', '## Dependencies\n\n- [required](../../private/ordinary.md)'));
    if (route === 'context') json(f.root, f.tests[1], {...f.doc, context: [{prompt_path: f.prompt, paths: [target]}]});
    if (route === 'include') json(f.root, 'pdd-source.json', {include: [target]});
    if (route.startsWith('prepare')) options.prepareSource = ports => {
      if (route === 'prepare-read') ports.readFile(target);
      if (route === 'prepare-stat') ports.statFile(target);
      return route === 'prepare-output' ? [{path: target, bytes: 'effective bytes'}] : [];
    };
    let capture, error;
    const observation = observeReads(f.root, () => { try { capture = captureSource(f.root, options); } catch (e) { error = e; } });
    if (!permitted) {
      assert.equal(error?.code, 'workspace-path-outside', route);
      assert.equal(capture, undefined);
      assert.equal(observation.reads.includes(target), false, `excluded read before ${route} refusal`);
    } else {
      assert.equal(error, undefined, error?.message);
      const uploaded = ['dependency', 'context', 'include', 'prepare-output'].includes(route);
      assert.equal(capture.files.some(file => file.path === target), uploaded, route);
      assert.equal(observation.reads.includes(target), route !== 'prepare-stat' && route !== 'prepare-output', route);
      assert.equal(capture.files.some(file => file.path === f.tests[0]), false, 'permission does not select a sibling');
    }
  }
  t.diagnostic('12 complete capture attempts; actual native content reads observed independently of files/tar.');
});

test('FORMAL source safety: all 2 policy modes × 3 strict-read targets preserve stronger safeguards', t => {
  for (const configured of [false, true]) for (const kind of ['regular', 'secret', 'symlink']) {
    const f = fixture(t), regular = 'simulation/rules.md';
    write(f.root, regular, 'SAFE-FORMAL-TEXT');
    write(f.root, 'simulation/.env', 'SECRET-FORMAL-TEXT');
    fs.symlinkSync('rules.md', join(f.root, 'simulation/link.md'));
    if (!configured) fs.unlinkSync(join(f.root, 'pdd-workspace.json'));
    const path = kind === 'regular' ? regular : kind === 'secret' ? 'simulation/.env' : 'simulation/link.md';
    let result, error;
    const observed = observeReads(f.root, () => {
      try { result = createStrictSourceAccess(f.root).sourceFilePort().read({path}); } catch (e) { error = e; }
    });
    if (kind === 'regular') { assert.equal(result.content, 'SAFE-FORMAL-TEXT'); assert.equal(error, undefined); }
    else {
      assert.equal(error?.exitCode, 4, `${configured}/${kind}`);
      assert.equal(observed.reads.includes(path), false, 'permission cannot weaken secret or strict no-link safety');
      assert.equal(observed.reads.includes(regular), false, 'strict link refusal cannot read its otherwise permitted target');
    }
  }
  t.diagnostic('6 actual strict native reads/refusals; source-safe linked upload and other safety classes are outside this domain.');
});

test('FORMAL simulator adapters: all 3 native kinds × default/custom definitions × 2 policy subsets refuse before process', async t => {
  for (const agent of ['codex', 'claude', 'gemini']) for (const custom of [false, true]) for (const allowed_paths of [[], ['simulation/']]) {
    const f = fixture(t); json(f.root, 'pdd-workspace.json', {allowed_paths});
    let processes = 0;
    const result = await askAgent({agent, cwd: f.root, env: f.env,
      definition: custom ? {id: agent, kind: agent, name: 'custom ' + agent, command: 'formal-custom', env: {}} : undefined,
      context: {question: 'explain'}, entries: [], run() { processes++; throw Error('forbidden process'); }});
    assert.match(result.error?.message ?? '', /Bounded agent connection/);
    assert.equal(processes, 0, `${agent}/${custom}/${allowed_paths}`);
  }
  t.diagnostic('12 actual adapter calls; unsupported bounded connection only; no successful native sandbox claimed.');
});

test('FORMAL authored source: all 2 statuses × 2 freshness states; all 2 policy widths × 4 independent edits', t => {
  for (const status of ['draft', 'approved']) for (const stale of [false, true]) {
    const f = fixture(t);
    let before = read(f.root, f.prompt).replace('"status": "draft"', `"status": "${status}"`);
    if (stale) before = before.replace('Return a value.', 'Return a different value.');
    write(f.root, f.prompt, before); write(f.root, 'private/excluded.prompt.md', before);
    const result = fillHashes({root: f.root});
    const shouldWrite = stale && status === 'draft';
    const expected = shouldWrite ? before.replace(/("prose_sha256": ")[a-f0-9]+(")/, `$1${authoredHash(before)}$2`) : before;
    assert.equal(read(f.root, f.prompt), expected, `${status}/${stale}: promised non-hash bytes`);
    assert.equal(result.filled.length, Number(shouldWrite));
    assert.equal(result.stale.length, Number(stale && status === 'approved'));
    assert.equal(read(f.root, 'private/excluded.prompt.md'), before);
  }
  for (const wider of [false, true]) for (const edit of ['private', 'selected-test', 'story', 'prompt']) {
    const f = fixture(t), before = captureSource(f.root, {tests: f.tests});
    if (wider) json(f.root, 'pdd-workspace.json', {allowed_paths: ['simulation/', 'unused/']});
    const path = edit === 'private' ? 'private/ordinary.md' : edit === 'selected-test' ? f.tests[1] : f[edit];
    write(f.root, path, read(f.root, path) + '\n');
    const after = captureSource(f.root, {tests: f.tests});
    assert.equal(after.sha256 === before.sha256, edit === 'private', `${wider}/${edit}`);
    assert.deepEqual(after.stories[0].tests.slice().sort(), f.tests.slice().sort());
  }
  t.diagnostic('4 hash classifications + 8 exact two-test source comparisons; used-reference and consumer reuse scopes remain separate.');
});

test('FORMAL case import: all 2 original targets × 2 worlds × 2 handoffs retain custody and never overwrite another test', async t => {
  for (const index of [0, 1]) for (const world of [0, 17]) for (const handoff of [false, true]) {
    const f = fixture(t), target = f.tests[index], other = f.tests[1 - index];
    const original = read(f.root, target), untouched = read(f.root, other), saved = f.received(target, world);
    const message = saveDoorCase(f.root, saved, {env: f.env});
    const id = message.match(/pending ([a-f0-9]{64}\.[a-f0-9]{64})/)?.[1];
    assert.ok(id, 'receipt without writer handoff is pending');
    assert.equal(read(f.root, target), original);
    const custody = join(f.state, 'case-import', ...id.split('.').map((part, i) => i ? part + '.received.json' : part));
    // The durable receipt must contain the entire received scenario, not merely a handled id.
    assert.ok(fs.existsSync(custody), 'complete durable receipt exists at the reported identity');
    const receipt = JSON.parse(fs.readFileSync(custody, 'utf8'));
    assert.deepEqual(receipt.saved, saved, 'full received payload including original association and expected values retained');
    if (handoff) {
      const ownership = await acquireCaseWriteOwnership({root: f.root, testPath: target, handoff: closed(target)}, {env: f.env});
      let result;
      try { result = await applyPendingCase({root: f.root, pendingId: id, writeOwnership: ownership}, {env: f.env}); }
      finally { ownership.release(); }
      const canAppend = world === 0;
      assert.equal(result.state, canAppend ? 'committed' : 'pending');
      const after = JSON.parse(read(f.root, target));
      if (canAppend) {
        assert.deepEqual({...after, steps: after.steps.slice(0, -1)}, JSON.parse(original));
        const once = read(f.root, target);
        const command = `import {saveDoorCase} from ${JSON.stringify(new URL('../src/runtime/runtime-client.mjs', import.meta.url).href)};` +
          `process.stdout.write(saveDoorCase(${JSON.stringify(f.root)},${JSON.stringify(saved)},{env:process.env}));`;
        const duplicate = spawnSync(process.execPath, ['--input-type=module', '-e', command], {cwd: f.root, env: f.env, encoding: 'utf8'});
        assert.equal(duplicate.status, 0, duplicate.stderr);
        assert.match(duplicate.stdout, /already saved/i);
        assert.equal(read(f.root, target), once, 'durable duplicate must not append again');
      } else assert.equal(read(f.root, target), original, 'incompatible world cannot invent setup/reset');
    }
    assert.equal(read(f.root, other), untouched, 'exact original association cannot choose the other variant');
  }
  t.diagnostic('8 target/world/handoff cases; 2 committed-duplicate replays in fresh Node processes; no arbitrary editor or crash-durability proof.');
});

for (const distinct of [false, true]) test(`FORMAL case custody MCP: supplied state ${distinct ? 'differs from' : 'equals'} process state`, t => {
  const f = fixture(t), processState = join(f.base, 'process-state'), requested = distinct ? join(f.base, 'requested-state') : processState;
  json(f.root, 'pdd-workspace.json', {allowed_paths: ['simulation/', 'tests/']});
  // The injected ports supply confirmed owner/action observations; the real MCP and save transaction run.
  const command = `import {createTryTools} from ${JSON.stringify(new URL('../src/runtime/try-mcp.mjs', import.meta.url).href)};` +
    `const f=${JSON.stringify({root: f.root, prompt: f.prompt, story: f.story, target: f.tests[1], doc: f.doc, requested})};` +
    `const owner={root:f.root,test:{path:f.target,storyPath:f.story,doc:f.doc},record:{id:'formal-session',origin:'https://interpreter.example.invalid',login:'owner'},model:{entries:[{entry_path:f.prompt,operation:'order'}]},data:{count:0}};` +
    `const tools=createTryTools({cwd:f.root,env:{...process.env,PDD_STATE_DIR:f.requested}},{readTryOwner:async()=>owner,runDoorCall:async()=>({id:'formal-action',result:9,inputWorld:{count:0},world:{count:0}})});` +
    `await tools.call('try_run',{entry:f.prompt+'#order',input:{}});try{await tools.call('try_save_case');}catch(e){process.stdout.write(e.message);}`;
  const result = spawnSync(process.execPath, ['--input-type=module', '-e', command], {
    cwd: f.root, env: {...f.env, PDD_STATE_DIR: processState}, encoding: 'utf8'});
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /not added:.*pending/);
  t.diagnostic(JSON.stringify({requestedCustody: fs.existsSync(join(requested, 'case-import')),
    processCustody: fs.existsSync(join(processState, 'case-import'))}));
  assert.equal(fs.existsSync(join(requested, 'case-import')), true, 'MCP pending custody must use the supplied environment');
  if (distinct) assert.equal(fs.existsSync(join(processState, 'case-import')), false, 'no fallback custody outside the requested state');
});

async function migrationFixture(t) {
  const f = fixture(t), old = fixture(t), workflowState = join(f.base, 'workflow-state');
  const run = {v: 1, number: 17, runId: 'formal-2781', repo: 'example/project', root: f.root, sourceRoot: f.root,
    commonDir: join(f.root, '.git'), runDir: join(f.root, '.git/pdd/runs/17'), state: 'running',
    areas: [{name: 'prompt-pr', steps: ['check'], optional: []}, {name: 'code', steps: ['build'], optional: []}],
    area: 0, done: {}, gate: null, pr: [], chats: [], startedAt: 0, workflow: 'feature', agent: 'codex'};
  writeRun(run, {stateDir: workflowState});
  return {...f, old, workflowState, mappings: [...f.tests, f.story, f.prompt].map(path => ({from: path, to: path}))};
}

test('FORMAL migration authority: all 3 registrations × 2 complete selections; preview is zero-write', async t => {
  for (const registration of ['none', 'first-only', 'complete']) for (const selection of [[0], [0, 1]]) {
    const f = await migrationFixture(t), selected = selection.map(i => f.tests[i]);
    if (registration !== 'none') {
      const result = await associateEvidenceWorkspace({ref: '17', workspace: f.old.root, stage: 'current',
        tests: registration === 'first-only' ? [f.tests[0]] : f.tests, cwd: f.root}, {stateDir: f.workflowState});
      assert.equal(result.exitCode, 0, result.message);
    }
    const source = captureSource(f.old.root, {tests: selected}).sha256;
    const eligibility = readEvidenceEligibility({root: f.root, producerRoot: f.old.root, tests: selected, source_sha256: source}, {stateDir: f.workflowState});
    const authorized = registration === 'first-only' && selection.length === 1 || registration === 'complete' && selection.length === 2;
    assert.equal(eligibility.state === 'eligible', authorized, `${registration}/${selection}`);
    const key = sha(f.old.root).slice(0, 16);
    const record = {root: f.old.root, last_batch: null, tries: {[selected[0]]: {id: 'formal-session', login: 'owner',
      origin: 'https://interpreter.example.invalid', tests: selected, source_sha256: source,
      state: 'unknown', readCommand: 'pdd test --read original'}}};
    json(f.state, 'repos/' + key + '.json', record);
    const before = fs.readFileSync(join(f.state, 'repos/' + key + '.json'));
    const preview = await migrateRuntimeWorkspace({root: f.root, projectionRoot: f.old.root, mappings: f.mappings},
      {env: f.env, evidencePorts: {stateDir: f.workflowState}});
    assert.ok(['preview', 'incomplete'].includes(preview.state));
    assert.equal(fs.existsSync(join(f.state, 'workspace-migrations')), false);
    assert.equal(fs.existsSync(join(f.state, 'repos/' + sha(f.root).slice(0, 16) + '.json')), false);
    assert.deepEqual(fs.readFileSync(join(f.state, 'repos/' + key + '.json')), before);
    assert.equal(fs.existsSync(f.old.root), true);
  }
  t.diagnostic('6 native association/read/preview combinations; equal bytes alone never authorize alternate-root evidence.');
});

for (const state of ['paused', 'unknown']) test(`FORMAL migration default descriptors: ${state} state retains usable exact-target recovery`, async t => {
  const f = await migrationFixture(t), id = '11111111-1111-4111-8111-111111111111', target = f.tests[1];
  assert.equal((await associateEvidenceWorkspace({ref: '17', workspace: f.old.root, stage: 'current', tests: [target], cwd: f.root}, {stateDir: f.workflowState})).exitCode, 0);
  const descriptor = join(f.state, 'tries', id + '.door.json'), last = join(f.state, 'tries', id + '.last.json');
  const oldRepo = join(f.state, 'repos', sha(f.old.root).slice(0, 16) + '.json');
  const promptHash = sha(read(f.old.root, f.prompt));
  json(f.state, 'tries/' + id + '.door.json', {version: 1, root: f.old.root, sessionId: id, origin: 'https://interpreter.example.invalid',
    login: 'owner', prompt: f.prompt, operation: 'order', originalPath: target, storyPath: f.story, criteria: f.doc.criteria,
    criterion: 'AC1', promptHash, promptHashes: {[f.prompt]: promptHash}, effectivePromptHashes: {[f.prompt]: promptHash},
    storyHash: sha(read(f.old.root, f.story)), stateDir: f.state, repoState: oldRepo, name: 'Order', inputSchema: {type: 'object'}});
  json(f.state, 'tries/' + id + '.last.json', {state: 'confirmed', id: 'formal-action', input: {}, result: 7,
    inputWorld: {count: 0}, world: {count: 0}});
  json(f.state, 'repos/' + sha(f.old.root).slice(0, 16) + '.json', {root: f.old.root, last_batch: null,
    last_door: {descriptor, last}, tries: {[target]: {id, state, login: 'owner', origin: 'https://interpreter.example.invalid',
      source_sha256: captureSource(f.old.root, {tests: [target]}).sha256, readCommand: 'pdd test --read original'}}});
  const originals = [oldRepo, descriptor, last].map(path => [path, fs.readFileSync(path)]);
  const result = await migrateRuntimeWorkspace({root: f.root, projectionRoot: f.old.root, mappings: f.mappings, write: true},
    {env: f.env, evidencePorts: {stateDir: f.workflowState}, handoff: async ({testPath}) => closed(testPath)});
  const stdout = stream(), stderr = stream(); let auth = 0, network = 0;
  const code = await runTry({cwd: f.root, options: {'--save-last': true}}, {env: f.env, stdout, stderr,
    gh(args) { auth++; return {status: 0, stdout: args[0] === 'auth' ? 'SYNTHETIC-NOT-A-CREDENTIAL' : 'owner 1'}; },
    fetch() { network++; throw Error('migration/save cannot dispatch'); }, caseHandoff: async ({testPath}) => closed(testPath)});
  for (const [path, bytes] of originals) assert.deepEqual(fs.readFileSync(path), bytes, 'original receipt/descriptor bytes');
  assert.equal(network, 0); assert.ok(auth <= 2);
  const destination = JSON.parse(read(f.state, 'repos/' + sha(f.root).slice(0, 16) + '.json'));
  const destinationDescriptor = JSON.parse(fs.readFileSync(destination.last_door.descriptor, 'utf8'));
  t.diagnostic(JSON.stringify({migration: result.state, items: result.items.map(item => ({kind: item.kind, state: item.state})),
    saveLastExit: code, descriptorStillNamesProjection: destinationDescriptor.root === f.old.root, network}));
  assert.equal(result.state, 'applied');
  assert.equal(code, 0, 'applied migration must retain usable exact-original saveLast: ' + stderr.text);
  assert.equal(JSON.parse(read(f.root, target)).steps.length, 2);
});
