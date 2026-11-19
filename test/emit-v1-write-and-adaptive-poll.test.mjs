import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { tmpdir } from 'node:os';
import { fakeRuntime } from './helpers/runtime-fake.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import * as seam from '../src/runtime-seam.mjs';

function makeRepo(t, entries) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-emit-write-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q'], { cwd: root });
  for (const [rel, body] of Object.entries(entries)) {
    const abs = join(root, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, typeof body === 'string' ? body : JSON.stringify(body, null, 2) + '\n');
  }
  execFileSync('git', ['add', '.'], { cwd: root });
  return root;
}

function captureStreams() {
  let out = '';
  let err = '';
  return {
    stdout: { write(chunk) { out += String(chunk); return true; } },
    stderr: { write(chunk) { err += String(chunk); return true; } },
    get out() { return out; },
    get err() { return err; },
  };
}

test('pdd lint --emit-v1 --write compiles Short JSON in place with concise output and stays idempotent', async t => {
  const root = makeRepo(t, {
    'prompts/greeter.prompt.md': '# greeter\n\nExpose `greet({ name })` returning `{ message }`.\n\n## Domain decisions\n\nReturn `"Hello, " + name + "!"`.\n',
    'user_stories/greet-user.md': [
      '# Greet a visitor',
      '',
      'As a visitor, I want a greeting with my name, so that I feel welcomed.',
      '',
      '## Acceptance criteria',
      '',
      '1. Greeting "Sam" returns "Hello, Sam!".',
      '',
    ].join('\n'),
    'tests/greet-user.json': {
      entry_path: 'prompts/greeter.prompt.md',
      steps: [
        {
          id: 'greet-sam',
          op: 'greet',
          input: { name: 'Sam' },
          checks: {
            '1': [['result', '/message', '=', 'Hello, Sam!']],
          },
        },
      ],
    },
  });

  // Reject --write without --emit-v1 cleanly (exit 2) before any network call.
  const badIo = captureStreams();
  const badCode = await runPdd(['lint', '--write', 'greet-user'], { cwd: root, ...badIo });
  assert.equal(badCode, 2);
  assert.match(badIo.err, /--write is only accepted with pdd lint --emit-v1/);

  // First --emit-v1 --write writes canonical v1 JSON directly to disk with concise stdout.
  const writeIo = captureStreams();
  const writeCode = await runPdd(['lint', '--emit-v1', '--write', 'greet-user'], { cwd: root, ...writeIo });
  assert.equal(writeCode, 0, writeIo.err);
  assert.match(writeIo.out, /Wrote tests\/greet-user\.json \(prompt-runtime\.program-scenario\.v1\)\./);
  assert.ok(writeIo.out.length < 200, `stdout should be concise, got ${writeIo.out.length} bytes`);

  const onDisk = JSON.parse(readFileSync(join(root, 'tests/greet-user.json'), 'utf8'));
  assert.equal(onDisk.schema_version, 'prompt-runtime.program-scenario.v1');
  assert.equal(onDisk.story_path, 'user_stories/greet-user.md');
  assert.equal(onDisk.criteria.length, 1);
  assert.match(onDisk.criteria[0].id, /^ac-sha256-/);
  assert.equal(onDisk.steps[0].step_id, 'greet-sam');
  assert.equal(onDisk.steps[0].operation, 'greet');

  // Second --emit-v1 --write --json is idempotent and reports unchanged without dumping full scenario JSON.
  const repeatIo = captureStreams();
  const repeatCode = await runPdd(['lint', '--emit-v1', '--write', '--json', 'greet-user'], { cwd: root, ...repeatIo });
  assert.equal(repeatCode, 0, repeatIo.err);
  const summary = JSON.parse(repeatIo.out);
  assert.equal(summary.ok, true);
  assert.equal(summary.wrote, true);
  assert.deepEqual(summary.updated, []);
  assert.deepEqual(summary.unchanged, ['tests/greet-user.json']);
  assert.equal(summary.files[0].written, false);
  assert.equal('scenario' in summary.files[0], false);
});

test('pdd lint --emit-v1 --write leaves all files untouched on compile refusal (exit 4)', async t => {
  const root = makeRepo(t, {
    'prompts/greeter.prompt.md': '# greeter\n\nExpose `greet({ name })` returning `{ message }`.\n',
    'user_stories/good.md': '# Good\n\nAs a visitor, I want a greeting, so that I see hello.\n\n## Acceptance criteria\n\n1. Greeting "Sam" returns "Hello, Sam!".\n',
    'tests/good.json': {
      entry_path: 'prompts/greeter.prompt.md',
      steps: [{ id: 's1', op: 'greet', input: { name: 'Sam' }, checks: { '1': [['result', '/message', '=', 'Hello, Sam!']] } }],
    },
    'user_stories/bad.md': '# Bad\n\nAs a visitor, I want a greeting, so that I see hello.\n\n## Acceptance criteria\n\n1. Greeting "Sam" returns "Hello, Sam!".\n',
    'tests/bad.json': {
      entry_path: 'prompts/greeter.prompt.md',
      steps: [{ id: 's1', op: 'greet', input: { name: 'Sam' }, checks: { '99': [['result', '/message', '=', 'Hello, Sam!']] } }],
    },
  });

  const beforeGood = readFileSync(join(root, 'tests/good.json'), 'utf8');
  const beforeBad = readFileSync(join(root, 'tests/bad.json'), 'utf8');

  const io = captureStreams();
  const code = await runPdd(['lint', '--emit-v1', '--write'], { cwd: root, ...io });
  assert.equal(code, 4);
  assert.equal(readFileSync(join(root, 'tests/good.json'), 'utf8'), beforeGood, 'valid sibling must not be written when another selected scenario fails');
  assert.equal(readFileSync(join(root, 'tests/bad.json'), 'utf8'), beforeBad);
});

test('seamRuntimePorts uses adaptive fast polling (250ms initial vs 2000ms legacy) while honoring explicit pollMs overrides', async t => {
  const root = makeRepo(t, {
    'prompts/greeter.prompt.md': '# greeter\n\nExpose `greet({ name })` returning `{ message }`.\n\n## Domain decisions\n\nReturn `"Hello, " + name + "!"`.\n',
    'user_stories/greet-user.md': [
      '# Greet a visitor',
      '',
      'As a visitor, I want a greeting with my name, so that I feel welcomed.',
      '',
      '## Acceptance criteria',
      '',
      '1. Greeting "Sam" returns "Hello, Sam!".',
      '',
    ].join('\n'),
    'tests/greet-user.json': {
      entry_path: 'prompts/greeter.prompt.md',
      steps: [{ id: 'greet-sam', op: 'greet', input: { name: 'Sam' }, checks: { '1': [['result', '/message', '=', 'Hello, Sam!']] } }],
    },
  });

  let postAt = 0;
  let getTimestamps = [];
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'lint') {
      postAt = Date.now();
      getTimestamps = [];
      return { status: 202, json: f.job(entry.request.requestId, 'lint', 'queued', null, 0) };
    }
    const id = entry.url.split('/').at(-1);
    getTimestamps.push(Date.now() - postAt);
    if (getTimestamps.length < 2) {
      return { status: 200, json: f.job(id, 'lint', 'running', null, 0) };
    }
    return {
      status: 200,
      json: f.lint(id, [{ path: 'prompts/greeter.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } }]),
    };
  });
  fake.capacity = () => ({ status: 200, json: { maintenance: false, available: true, remaining: 10, features: ['lint-tests', 'lazy-interfaces'] } });
  const env = { ...process.env, PDD_RUNTIME_URL: fake.origin };
  const fakeGh = args => {
    if (args[0] === 'auth' && args[1] === 'token') return { status: 0, stdout: 'gho_test_token\n', stderr: '' };
    if (args[0] === 'api' && (args[1] === 'user' || args[1] === '/user')) return { status: 0, stdout: 'tester 42\n', stderr: '' };
    return { status: 1, stdout: '', stderr: `unexpected gh call: ${args.join(' ')}` };
  };

  // 1. Default adaptive polling (no pollMs/sleep passed) finishes 2 poll cycles well under 1.5s (vs ~4.0s at 2000ms).
  const io1 = captureStreams();
  const t0 = Date.now();
  const code1 = await seam.lint({ cwd: root, words: ['greet-user'], options: { '--json': true } }, { env, gh: fakeGh, ...io1 });
  const elapsed1 = Date.now() - t0;
  assert.equal(code1, 0, io1.err + io1.out);
  assert.ok(getTimestamps.length >= 2, `expected at least 2 polls, got ${getTimestamps.length}`);
  assert.ok(elapsed1 < 1500, `adaptive polling should complete 2 fast polls well under 1500ms, took ${elapsed1}ms (polls at ${getTimestamps.join(',')}ms)`);

  // 2. Explicit ports.pollMs / ports.sleep override is preserved untouched.
  const recordedSleeps = [];
  const io2 = captureStreams();
  const code2 = await seam.lint(
    { cwd: root, words: ['greet-user'], options: { '--json': true } },
    {
      env,
      gh: fakeGh,
      pollMs: 77,
      sleep: async ms => { recordedSleeps.push(ms); },
      ...io2,
    },
  );
  assert.equal(code2, 0, io2.err + io2.out);
  assert.ok(recordedSleeps.includes(77), `expected explicit pollMs 77 to be preserved, saw ${JSON.stringify(recordedSleeps)}`);
});

test('pdd lint --emit-v1 --write binds matching legacy IDs and pdd lint --local flags stale/mismatched criteria offline', async t => {
  const criterionText = 'Greeting "Sam" returns "Hello, Sam!".';
  const root = makeRepo(t, {
    'prompts/greeter.prompt.md': '# greeter\n\nExpose `greet({ name })` returning `{ message }`.\n\n## Domain decisions\n\nReturn `"Hello, " + name + "!"`.\n',
    'user_stories/greet-user.md': [
      '# Greet a visitor',
      '',
      'As a visitor, I want a greeting with my name, so that I feel welcomed.',
      '',
      '## Acceptance criteria',
      '',
      `1. ${criterionText}`,
      '',
    ].join('\n'),
    'tests/greet-user.json': {
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/greet-user.md',
      criteria: [{ id: 'AC1', text: criterionText }],
      initial_world: {},
      simulation: {},
      steps: [
        {
          id: 'greet-sam',
          entry_path: 'prompts/greeter.prompt.md',
          operation: 'greet',
          input: { name: 'Sam' },
          checks: [{ criterion_id: 'AC1', target: 'result', path: '/message', op: 'equals', value: 'Hello, Sam!' }],
        },
      ],
    },
  });

  // 1. pdd lint --local keeps matching legacy v1 criteria free of false-positive warnings.
  const localBefore = captureStreams();
  const localCodeBefore = await runPdd(['lint', '--local', '--json'], { cwd: root, ...localBefore });
  assert.equal(localCodeBefore, 0, localBefore.err + localBefore.out);
  assert.deepEqual(JSON.parse(localBefore.out).warnings, []);

  // 2. pdd lint --emit-v1 --write binds legacy AC1 -> ac-sha256-... in place and stays idempotent.
  const writeIo = captureStreams();
  const writeCode = await runPdd(['lint', '--emit-v1', '--write', '--json'], { cwd: root, ...writeIo });
  assert.equal(writeCode, 0, writeIo.err + writeIo.out);
  const writeSummary = JSON.parse(writeIo.out);
  assert.deepEqual(writeSummary.updated, ['tests/greet-user.json']);
  const boundDoc = JSON.parse(readFileSync(join(root, 'tests/greet-user.json'), 'utf8'));
  assert.match(boundDoc.criteria[0].id, /^ac-sha256-/);
  assert.equal(boundDoc.steps[0].checks[0].criterion_id, boundDoc.criteria[0].id);

  const secondWriteIo = captureStreams();
  const secondWriteCode = await runPdd(['lint', '--emit-v1', '--write', '--json'], { cwd: root, ...secondWriteIo });
  assert.equal(secondWriteCode, 0, secondWriteIo.err + secondWriteIo.out);
  assert.deepEqual(JSON.parse(secondWriteIo.out).updated, []);

  // 3. pdd lint --local reports 0 warnings once bound.
  const localAfter = captureStreams();
  const localCodeAfter = await runPdd(['lint', '--local', '--json'], { cwd: root, ...localAfter });
  assert.equal(localCodeAfter, 0, localAfter.err + localAfter.out);
  const afterJson = JSON.parse(localAfter.out);
  assert.deepEqual(afterJson.warnings, []);

  // 4. Stale ac-sha256-... after Story edit is warned locally WITHOUT suggesting --bind-criteria and refused (exit 4) by --emit-v1 --write.
  const boundRaw = readFileSync(join(root, 'tests/greet-user.json'), 'utf8');
  writeFileSync(
    join(root, 'user_stories/greet-user.md'),
    '# Greet a visitor\n\nAs a visitor, I want a greeting, so that I feel welcomed.\n\n## Acceptance criteria\n\n1. Greeting "Sam" returns "Hi, Sam!".\n',
  );
  const staleLocal = captureStreams();
  await runPdd(['lint', '--local', '--json'], { cwd: root, ...staleLocal });
  const staleJson = JSON.parse(staleLocal.out);
  assert.ok(
    staleJson.warnings.some(w => /story-criterion-mismatch/.test(w) && /stale content-bound ID/.test(w)),
    `expected stale local warning, got ${JSON.stringify(staleJson.warnings)}`,
  );
  assert.equal(
    staleJson.warnings.some(w => /--bind-criteria/.test(w)),
    false,
    `stale content-bound warning must not suggest --bind-criteria: ${JSON.stringify(staleJson.warnings)}`,
  );
  const staleWrite = captureStreams();
  const staleWriteCode = await runPdd(['lint', '--emit-v1', '--write'], { cwd: root, ...staleWrite });
  assert.equal(staleWriteCode, 4);
  assert.equal(readFileSync(join(root, 'tests/greet-user.json'), 'utf8'), boundRaw, 'refused --emit-v1 --write must leave file untouched');

  // 5. Explicit legacy AC1 with mismatched text is also caught offline by pdd lint --local.
  writeFileSync(
    join(root, 'tests/greet-user.json'),
    JSON.stringify({ ...boundDoc, criteria: [{ id: 'AC1', text: criterionText }], steps: [{ ...boundDoc.steps[0], checks: [{ ...boundDoc.steps[0].checks[0], criterion_id: 'AC1' }] }] }, null, 2) + '\n',
  );
  const mismatchLocal = captureStreams();
  await runPdd(['lint', '--local', '--json'], { cwd: root, ...mismatchLocal });
  const mismatchJson = JSON.parse(mismatchLocal.out);
  assert.ok(
    mismatchJson.warnings.some(w => /story-criterion-mismatch/.test(w)),
    `expected text-mismatch local warning, got ${JSON.stringify(mismatchJson.warnings)}`,
  );
});
