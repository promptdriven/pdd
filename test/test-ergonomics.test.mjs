import './helpers/test-home.mjs';
import './helpers/test-net-guard.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { chmodSync, existsSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as seam from '../src/runtime-seam.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { TOKEN, fakeRuntime, portsFor, temp } from './helpers/runtime-fake.mjs';

const repoRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const BIN_PDD = join(repoRoot, 'bin/pdd.mjs');

function git(cwd, ...args) {
  const res = spawnSync('git', args, { cwd, encoding: 'utf8' });
  assert.equal(res.status, 0, res.stderr);
  return res.stdout;
}

function captureStream() {
  return {
    text: '',
    write(chunk) {
      this.text += String(chunk);
      return true;
    },
  };
}

function fakeGhBin(sandbox, { fail = false } = {}) {
  const binDir = join(sandbox, fail ? 'fake-gh-fail' : 'fake-gh-bin');
  mkdirSync(binDir, { recursive: true });
  const ghPath = join(binDir, 'gh');
  writeFileSync(
    ghPath,
    fail
      ? '#!/bin/sh\necho "unexpected gh call" >&2\nexit 99\n'
      : `#!/bin/sh\nif [ "$1" = "auth" ]; then printf '%s\\n' ${JSON.stringify(TOKEN)}; exit 0; fi\nprintf 'octo 4242\\n'\n`,
  );
  chmodSync(ghPath, 0o755);
  return `${binDir}${delimiter}${process.env.PATH ?? ''}`;
}

function makeCliPrompt(title, description, command) {
  const inputSchema = {
    type: 'object',
    properties: { argv: { type: 'array', items: { type: 'string' } } },
    required: ['argv'],
    additionalProperties: false,
  };
  const resultSchema = {
    type: 'object',
    properties: {
      stdout: { type: 'string' },
      stderr: { type: 'string' },
      exit_code: { type: 'integer' },
    },
    required: ['stdout', 'stderr', 'exit_code'],
    additionalProperties: false,
  };
  const iface = {
    status: 'draft',
    prose_sha256: '',
    entries: [
      {
        operation: 'main',
        input_schema: inputSchema,
        result_schema: resultSchema,
        errors: [],
        implementation: { kind: 'cli', command },
      },
    ],
    calls: [],
    resources: [],
    limits: { max_steps: 4, max_model_calls: 2 },
    conventions: [
      { path: '/entries/0/input_schema', convention: 'cli' },
      { path: '/entries/0/result_schema', convention: 'cli' },
    ],
  };
  const render = () =>
    `# ${title}\n\n${description}\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface, null, 2)}\n\`\`\`\n</details>\n`;
  iface.prose_sha256 = seam.proseSha256(render());
  return render();
}

function makeSplitStoryRepo(t) {
  const sandbox = temp(t);
  const repo = join(sandbox, 'repo');
  const home = join(sandbox, 'home');
  const state = join(sandbox, 'state');
  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  mkdirSync(join(repo, 'tests'), { recursive: true });
  mkdirSync(join(repo, 'bin'), { recursive: true });
  mkdirSync(join(repo, 'sub'), { recursive: true });
  mkdirSync(home, { recursive: true });

  writeFileSync(
    join(repo, 'bin/calc.mjs'),
    `const [op, a, b] = process.argv.slice(2);\nconst x = Number(a), y = Number(b);\nif (op === 'add') { console.log(String(x + y)); process.exit(0); }\nif (op === 'sub') { console.log(String(x - y)); process.exit(0); }\nconsole.error('unknown op'); process.exit(2);\n`,
  );
  writeFileSync(
    join(repo, 'bin/other.mjs'),
    `console.log('pong');\nprocess.exit(0);\n`,
  );

  writeFileSync(
    join(repo, 'prompts/calc.prompt.md'),
    makeCliPrompt('Calculator CLI', 'Compute add and sub operations on two integers.', 'node bin/calc.mjs'),
  );
  writeFileSync(
    join(repo, 'prompts/other.prompt.md'),
    makeCliPrompt('Other CLI', 'Print pong and exit 0.', 'node bin/other.mjs'),
  );

  writeFileSync(
    join(repo, 'user_stories/split.md'),
    [
      '# Split arithmetic',
      '',
      'As a user, I can add and subtract integers.',
      '',
      '## Acceptance criteria',
      '',
      '1. Adding two integers prints their sum and exits 0.',
      '2. Subtracting two integers prints their difference and exits 0.',
      '',
    ].join('\n'),
  );
  writeFileSync(
    join(repo, 'user_stories/other.md'),
    [
      '# Ping responder',
      '',
      'As a user, I can receive pong.',
      '',
      '## Acceptance criteria',
      '',
      '1. Running other prints pong and exits 0.',
      '',
    ].join('\n'),
  );

  const splitCriteria = [
    { id: 'AC1', text: 'Adding two integers prints their sum and exits 0.' },
    { id: 'AC2', text: 'Subtracting two integers prints their difference and exits 0.' },
  ];
  writeFileSync(
    join(repo, 'tests/split.a.json'),
    `${JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/split.md',
      criteria: splitCriteria,
      initial_world: {},
      simulation: {},
      context: [],
      steps: [
        {
          step_id: 'add-step',
          entry_path: 'prompts/calc.prompt.md',
          operation: 'main',
          input: { argv: ['add', '2', '3'] },
          checks: [
            { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: '5\n' },
            { criterion_id: 'AC1', target: 'result', path: '/exit_code', op: 'equals', value: 0 },
          ],
        },
      ],
    }, null, 2)}\n`,
  );
  writeFileSync(
    join(repo, 'tests/split.b.json'),
    `${JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/split.md',
      criteria: splitCriteria,
      initial_world: {},
      simulation: {},
      context: [],
      steps: [
        {
          step_id: 'sub-step',
          entry_path: 'prompts/calc.prompt.md',
          operation: 'main',
          input: { argv: ['sub', '9', '4'] },
          checks: [
            { criterion_id: 'AC2', target: 'result', path: '/stdout', op: 'equals', value: '5\n' },
            { criterion_id: 'AC2', target: 'result', path: '/exit_code', op: 'equals', value: 0 },
          ],
        },
      ],
    }, null, 2)}\n`,
  );
  writeFileSync(
    join(repo, 'tests/other.json'),
    `${JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/other.md',
      criteria: [{ id: 'AC1', text: 'Running other prints pong and exits 0.' }],
      initial_world: {},
      simulation: {},
      context: [],
      steps: [
        {
          step_id: 'ping-step',
          entry_path: 'prompts/other.prompt.md',
          operation: 'main',
          input: { argv: [] },
          checks: [
            { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'pong\n' },
            { criterion_id: 'AC1', target: 'result', path: '/exit_code', op: 'equals', value: 0 },
          ],
        },
      ],
    }, null, 2)}\n`,
  );

  git(repo, 'init', '-q');
  git(repo, 'add', '-A');
  git(repo, '-c', 'user.email=test@example.com', '-c', 'user.name=Test', 'commit', '-qm', 'init');

  return { sandbox, repo: realpathSync(repo), home: realpathSync(home), state };
}

function fakeSplitServer(t, { failTests = new Set(), reconcileHandler = null } = {}) {
  return fakeRuntime(t, (entry, fake) => {
    if (entry.method === 'GET' && entry.url.includes('/reconciliation')) {
      if (reconcileHandler) return reconcileHandler(entry, fake);
      return { status: 404, json: { error: { code: 'not-found' } } };
    }
    if (entry.method === 'POST' && entry.command === 'lint') {
      return {
        status: 200,
        json: fake.lint(entry.request.requestId, [
          { path: 'prompts/calc.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
          { path: 'prompts/other.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } },
        ]),
      };
    }
    if (entry.method === 'POST' && entry.command === 'check') {
      const testPath = entry.request.scenario;
      fake.jobs.set(entry.request.requestId, testPath);
      return { status: 202, json: fake.check(entry.request.requestId, 'queued') };
    }
    const id = entry.url.split('/').at(-1);
    if (!fake.jobs.has(id)) {
      return { status: 404, json: { error: { code: 'not-found' } } };
    }
    const testPath = fake.jobs.get(id) ?? '';
    if (failTests.has(testPath)) {
      return {
        status: 200,
        json: fake.check(id, 'failed', [
          { criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', expected: '5\n', actual: 'wrong\n', passed: false },
        ]),
      };
    }
    const criterionId = testPath.endsWith('split.b.json') ? 'AC2' : 'AC1';
    return {
      status: 200,
      json: fake.check(id, 'passed', [
        { criterion_id: criterionId, target: 'result', path: '/stdout', op: 'equals', expected: '5\n', actual: '5\n', passed: true },
        { criterion_id: criterionId, target: 'result', path: '/exit_code', op: 'equals', expected: 0, actual: 0, passed: true },
      ]),
    };
  });
}

test('#3703 AC2: single-scenario targeting runs only the targeted file across --files, pdd test, and --target code, stays fail-closed, and never poisons Story cache', async t => {
  const setup = makeSplitStoryRepo(t);
  const envBase = { ...process.env, HOME: setup.home, PDD_STATE_DIR: setup.state };

  // 1. pdd test --files tests/split.a.json (root and subdirectory) uploads only split.a.json + owning Story + prompt closure.
  for (const [cwd, arg] of [[setup.repo, 'tests/split.a.json'], [setup.repo, './tests/split.a.json'], [join(setup.repo, 'sub'), '../tests/split.a.json']]) {
    const out = captureStream();
    const err = captureStream();
    const code = await runPdd(['test', '--files', arg, '--json'], { cwd, env: envBase, stdout: out, stderr: err });
    assert.equal(code, 0, err.text);
    const json = JSON.parse(out.text);
    const paths = json.files.map(f => f.path).sort();
    assert.deepEqual(paths, ['prompts/calc.prompt.md', 'tests/split.a.json', 'user_stories/split.md']);
  }

  // 2. pdd test tests/split.a.json sends ONLY split.a.json, exits 0, promotes targeted slice, and does NOT write full-Story cache.
  const fake = await fakeSplitServer(t);
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const checkCode = await seam.check({ words: ['tests/split.a.json'], options: { '--json': true }, cwd: setup.repo }, ports);
  assert.equal(checkCode, 0, ports.stderr.text);
  const checkPosts = fake.posts.filter(p => p.command === 'check');
  assert.deepEqual(checkPosts.map(p => p.request.scenario), ['tests/split.a.json']);
  const checkJson = JSON.parse(ports.stdout.text);
  assert.equal(checkJson.exit_code, 0);
  assert.equal(checkJson.rows.length, 1);
  assert.equal(checkJson.rows[0].test, 'tests/split.a.json');
  assert.equal(checkJson.rows[0].state, 'passed');
  assert.equal(checkJson.rows[0].targeted_scenario, true);
  assert.deepEqual(checkJson.rows[0].sibling_covered_criteria.map(c => c.criterion_id), ['AC2']);
  assert.deepEqual(checkJson.rows[0].criteria, { passed: 1, total: 1 });
  assert.match(ports.stderr.text, /targeted scenario tests\/split\.a\.json passed own checks/);
  // Verify saved summary.json and batch.json on disk both reflect the promoted pass,
  // so --retry-unresolved on that targeted-slice batch sees 0 unresolved tests and makes 0 AI calls.
  const savedSummary = JSON.parse(readFileSync(join(setup.state, 'batches', checkJson.batch, 'summary.json'), 'utf8'));
  assert.equal(savedSummary.exit_code, 0);
  assert.equal(savedSummary.rows[0].state, 'passed');
  const savedBatch = JSON.parse(readFileSync(join(setup.state, 'batches', checkJson.batch, 'batch.json'), 'utf8'));
  assert.equal(savedBatch.rows[0].state, 'passed');
  assert.equal(savedBatch.rows[0].targeted_scenario, true);
  const retryTargetedPostsBefore = fake.posts.length;
  const retryTargetedPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(
    await seam.check({ words: [], options: { '--retry-unresolved': checkJson.batch, '--json': true }, cwd: setup.repo }, retryTargetedPorts.ports),
    0,
    retryTargetedPorts.ports.stderr.text,
  );
  assert.equal(fake.posts.length, retryTargetedPostsBefore, 'promoted targeted-slice batch must not be re-run by --retry-unresolved');
  assert.equal(JSON.parse(retryTargetedPorts.ports.stdout.text).ai_calls, 0);
  // Rule check: must NOT write a full-Story pass entry into .pdd/cache/test/stories.json.
  const cachePath = join(setup.repo, '.pdd/cache/test/stories.json');
  if (existsSync(cachePath)) {
    const cacheDoc = JSON.parse(readFileSync(cachePath, 'utf8'));
    assert.notEqual(cacheDoc?.stories?.['tests/split.a.json']?.outcome, 'passed', 'targeted slice must never write full-Story pass to cache');
    assert.notEqual(cacheDoc?.stories?.['user_stories/split.md']?.outcome, 'passed', 'targeted slice must never write full-Story pass to cache');
  }

  // Also test plain text output mode (with --details) and subdirectory invocation for single-scenario targeting.
  const textPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const textCode = await seam.check({ words: ['tests/split.a.json'], options: { '--details': true }, cwd: setup.repo }, textPorts.ports);
  assert.equal(textCode, 0, textPorts.ports.stderr.text);
  assert.match(textPorts.ports.stdout.text, /tests\/split\.a\.json\s+passed/);
  assert.match(textPorts.ports.stdout.text, /1 of 1 criterion/);
  assert.match(textPorts.ports.stdout.text, /Reports \(anyone with a link can open it\):/);

  // Subdirectory invocation with repo-root-relative path tests/split.a.json must also promote cleanly!
  const subPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const subCode = await seam.check({ words: ['tests/split.a.json'], options: { '--json': true }, cwd: join(setup.repo, 'sub') }, subPorts.ports);
  assert.equal(subCode, 0, subPorts.ports.stderr.text);
  assert.equal(JSON.parse(subPorts.ports.stdout.text).rows[0].state, 'passed');

  // Mixed batch in text mode with --details: split.a.json passes while other.json fails — failure diff & report URL must be preserved!
  const mixedFailFake = await fakeSplitServer(t, { failTests: new Set(['tests/other.json']) });
  const mixedPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: mixedFailFake.origin });
  const mixedCode = await seam.check(
    { words: ['tests/split.a.json', 'tests/other.json'], options: { '--details': true }, cwd: setup.repo },
    mixedPorts.ports,
  );
  assert.equal(mixedCode, 1);
  assert.match(mixedPorts.ports.stdout.text, /tests\/split\.a\.json\s+passed/);
  assert.match(mixedPorts.ports.stdout.text, /FAILED\s+.*tests\/other\.json/);
  assert.match(mixedPorts.ports.stdout.text, /expected "5\\n", got "wrong\\n"/);
  assert.match(mixedPorts.ports.stdout.text, /Report:\s+http:\/\/127\.0\.0\.1:/);

  // 3. Own check failure on targeted slice still exits 1 (never promoted).
  const failFake = await fakeSplitServer(t, { failTests: new Set(['tests/split.a.json']) });
  const failPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: failFake.origin });
  const failCode = await seam.check({ words: ['tests/split.a.json'], options: { '--json': true }, cwd: setup.repo }, failPorts.ports);
  assert.equal(failCode, 1);
  assert.equal(JSON.parse(failPorts.ports.stdout.text).rows[0].state, 'failed');

  // 4. pdd test --target code tests/split.a.json executes ONLY split.a.json and exits 0.
  const codeOut = captureStream();
  const codeErr = captureStream();
  const compiledSliceExit = await runPdd(['test', '--target', 'code', 'tests/split.a.json', '--json'], {
    cwd: setup.repo,
    env: envBase,
    stdout: codeOut,
    stderr: codeErr,
  });
  assert.equal(compiledSliceExit, 0, codeErr.text);
  const compiledSliceJson = JSON.parse(codeOut.text);
  assert.equal(compiledSliceJson.ai_calls, 0);
  assert.equal(compiledSliceJson.stories.length, 1);
  assert.equal(compiledSliceJson.stories[0].status, 'passed');
  assert.deepEqual(compiledSliceJson.stories[0].steps.map(s => s.step_id), ['add-step']);

  // Full split Story under --target code executes both siblings and passes.
  const fullOut = captureStream();
  const fullErr = captureStream();
  const compiledFullExit = await runPdd(['test', '--target', 'code', 'user_stories/split.md', '--json'], {
    cwd: setup.repo,
    env: envBase,
    stdout: fullOut,
    stderr: fullErr,
  });
  assert.equal(compiledFullExit, 0, fullErr.text);
  const compiledFullJson = JSON.parse(fullOut.text);
  assert.equal(compiledFullJson.stories[0].status, 'passed');
  assert.deepEqual(compiledFullJson.stories[0].steps.map(s => s.step_id).sort(), ['add-step', 'sub-step']);

  // Failing code implementation makes targeted --target code fail with exit 1.
  const origCalc = readFileSync(join(setup.repo, 'bin/calc.mjs'), 'utf8');
  writeFileSync(join(setup.repo, 'bin/calc.mjs'), origCalc.replace('x + y', 'x + y + 1'));
  const badCodeOut = captureStream();
  const badCodeErr = captureStream();
  const badCodeExit = await runPdd(['test', '--target', 'code', 'tests/split.a.json', '--json'], {
    cwd: setup.repo,
    env: envBase,
    stdout: badCodeOut,
    stderr: badCodeErr,
  });
  assert.equal(badCodeExit, 1);
  assert.equal(JSON.parse(badCodeOut.text).stories[0].status, 'failed');
  writeFileSync(join(setup.repo, 'bin/calc.mjs'), origCalc);

  // 5. Fail-closed negative check: adding an uncovered 3rd criterion fails BOTH pdd test and pdd test --target code!
  writeFileSync(
    join(setup.repo, 'user_stories/split.md'),
    `${readFileSync(join(setup.repo, 'user_stories/split.md'), 'utf8')}3. Multiplying two integers prints their product and exits 0.\n`,
  );
  for (const file of ['tests/split.a.json', 'tests/split.b.json']) {
    const doc = JSON.parse(readFileSync(join(setup.repo, file), 'utf8'));
    doc.criteria.push({ id: 'AC3', text: 'Multiplying two integers prints their product and exits 0.' });
    writeFileSync(join(setup.repo, file), `${JSON.stringify(doc, null, 2)}\n`);
  }

  const uncoveredOut = captureStream();
  const uncoveredErr = captureStream();
  const uncoveredCodeExit = await runPdd(['test', '--target', 'code', 'tests/split.a.json', '--json'], {
    cwd: setup.repo,
    env: envBase,
    stdout: uncoveredOut,
    stderr: uncoveredErr,
  });
  assert.equal(uncoveredCodeExit, 1);
  assert.equal(JSON.parse(uncoveredOut.text).stories[0].status, 'not run');

  const uncoveredPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const uncoveredCheckExit = await seam.check({ words: ['tests/split.a.json'], options: { '--json': true }, cwd: setup.repo }, uncoveredPorts.ports);
  assert.equal(uncoveredCheckExit, 5);
  const uncoveredCheckJson = JSON.parse(uncoveredPorts.ports.stdout.text);
  assert.equal(uncoveredCheckJson.rows[0].state, 'not run');
  assert.equal(uncoveredCheckJson.rows[0].reason.code, 'criteria-not-checked');
});

test('#3703 AC3: --retry-unresolved reconciles batch, skips passed scenarios, re-runs partial/unknown/not_run/failed, and exits 0 with 0 AI calls when all passed', async t => {
  const setup = makeSplitStoryRepo(t);

  // Create 5 standalone single-criterion scenarios so each can be verified cleanly in one batch.
  const names = ['s-pass', 's-part', 's-unk', 's-notrun', 's-fail'];
  for (const name of names) {
    writeFileSync(
      join(setup.repo, `user_stories/${name}.md`),
      `# Story ${name}\n\nAs a user, I run ${name}.\n\n## Acceptance criteria\n\n1. Running other prints pong and exits 0.\n`,
    );
    writeFileSync(
      join(setup.repo, `tests/${name}.json`),
      `${JSON.stringify({
        schema_version: 'prompt-runtime.program-scenario.v1',
        story_path: `user_stories/${name}.md`,
        criteria: [{ id: 'AC1', text: 'Running other prints pong and exits 0.' }],
        initial_world: {},
        simulation: {},
        context: [],
        steps: [
          {
            step_id: `${name}-step`,
            entry_path: 'prompts/other.prompt.md',
            operation: 'main',
            input: { argv: [] },
            checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'pong\n' }],
          },
        ],
      }, null, 2)}\n`,
    );
  }
  git(setup.repo, 'add', '-A');
  git(setup.repo, '-c', 'user.email=test@example.com', '-c', 'user.name=Test', 'commit', '-qm', 'add batch scenarios');

  const mixedBatch = '20261125-100000-ab12';
  const reqPart = '11111111-1111-4111-8111-111111111111';
  const reqUnk = '22222222-2222-4222-8222-222222222222';
  const batchDir = join(setup.state, 'batches', mixedBatch);
  mkdirSync(batchDir, { recursive: true });
  const nowMs = Date.parse('2026-10-27T16:27:47Z');
  writeFileSync(
    join(batchDir, 'batch.json'),
    JSON.stringify({
      version: 1,
      batch: mixedBatch,
      root: setup.repo,
      intent: 'check',
      login: 'octo',
      created_at: new Date(nowMs - 60_000).toISOString(),
      rows: [
        { test: 'tests/s-pass.json', state: 'passed', recovery_state: 'passed', request_ids: ['33333333-3333-4333-8333-333333333333'], calls: 1, accounting_complete: true },
        { test: 'tests/s-part.json', state: 'partial', recovery_state: 'unknown', note: { code: 'no-server-verdict', message: 'Timed out.' }, request_ids: [reqPart], sent_at: nowMs - 60_000, calls: 'unknown', accounting_complete: false },
        { test: 'tests/s-unk.json', state: 'unknown', recovery_state: 'unknown', request_ids: [reqUnk], sent_at: nowMs - 48 * 3_600_000, calls: 'unknown', accounting_complete: false },
        { test: 'tests/s-notrun.json', state: 'not_run', recovery_state: 'not_run', note: { code: 'server-busy', message: 'Busy.' }, request_ids: [], calls: 0, accounting_complete: true },
        { test: 'tests/s-fail.json', state: 'failed', recovery_state: 'failed', failed_checks: [{ criterion_id: 'AC1' }], request_ids: ['44444444-4444-4444-8444-444444444444'], calls: 1, accounting_complete: true },
      ],
    }, null, 2),
  );

  const reconcileUrls = [];
  const fake = await fakeSplitServer(t, {
    reconcileHandler(entry) {
      reconcileUrls.push(entry.url);
      return { status: 404, json: { error: { code: 'not-found' } } };
    },
  });

  // Patch batch.json origin so reconciliation talks to fake.origin.
  const bDoc = JSON.parse(readFileSync(join(batchDir, 'batch.json'), 'utf8'));
  bDoc.origin = fake.origin;
  writeFileSync(join(batchDir, 'batch.json'), JSON.stringify(bDoc, null, 2));

  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const exitCode = await seam.check(
    { words: [], options: { '--retry-unresolved': mixedBatch, '--json': true }, cwd: setup.repo },
    ports,
  );
  assert.equal(exitCode, 0, ports.stderr.text);
  assert.ok(reconcileUrls.some(u => u.includes(reqPart)), 'expected batch reconciliation query before retry');
  const checkPosts = fake.posts.filter(p => p.command === 'check').map(p => p.request.scenario).sort();
  assert.deepEqual(checkPosts, ['tests/s-fail.json', 'tests/s-notrun.json', 'tests/s-part.json', 'tests/s-unk.json']);
  assert.ok(!checkPosts.includes('tests/s-pass.json'), 'already-passed scenario must be skipped');

  const outJson = JSON.parse(ports.stdout.text);
  assert.equal(outJson.retried_from, mixedBatch);
  assert.deepEqual(outJson.skipped_passed_tests, ['tests/s-pass.json']);
  assert.equal(outJson.exit_code, 0);

  // Saved batch.json should have expired reservations cleared after reconciliation.
  const updatedBatch = JSON.parse(readFileSync(join(batchDir, 'batch.json'), 'utf8'));
  assert.equal(updatedBatch.rows.find(r => r.test === 'tests/s-part.json').reservation_reconciled?.cleared, true);
  assert.equal(updatedBatch.rows.find(r => r.test === 'tests/s-unk.json').reservation_reconciled?.cleared, true);

  // All-passed batch exits 0 with 0 AI calls and 0 gh/HTTP calls.
  const passedBatch = '20261125-100500-cd34';
  const passedDir = join(setup.state, 'batches', passedBatch);
  mkdirSync(passedDir, { recursive: true });
  writeFileSync(
    join(passedDir, 'batch.json'),
    JSON.stringify({
      version: 1,
      batch: passedBatch,
      root: setup.repo,
      intent: 'check',
      origin: fake.origin,
      rows: [{ test: 'tests/s-pass.json', state: 'passed', recovery_state: 'passed', request_ids: ['55555555-5555-4555-8555-555555555555'], calls: 1, accounting_complete: true }],
    }, null, 2),
  );
  const postsBefore = fake.posts.length;
  const { ports: pAll, clock: cAll } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const allExit = await seam.check({ words: [], options: { '--retry-unresolved': passedBatch, '--json': true }, cwd: setup.repo }, pAll);
  assert.equal(allExit, 0, pAll.stderr.text);
  assert.equal(fake.posts.length, postsBefore, 'all-passed batch must send 0 runtime POSTs');
  assert.equal(cAll.gh.length, 0, 'all-passed batch must make 0 gh calls');
  const allJson = JSON.parse(pAll.stdout.text);
  assert.equal(allJson.ai_calls, 0);
  assert.deepEqual(allJson.retry_tests, []);
  assert.deepEqual(allJson.skipped_passed_tests, ['tests/s-pass.json']);

  // Batch where an unresolved row settles to passed via server reconciliation triggers 0 AI retries.
  const settledBatch = '20261125-100600-ef56';
  const reqSettled = '66666666-6666-4666-8666-666666666666';
  const settledDir = join(setup.state, 'batches', settledBatch);
  mkdirSync(settledDir, { recursive: true });
  const settleFake = await fakeSplitServer(t, {
    reconcileHandler() {
      return {
        status: 200,
        json: {
          schema_version: 'pdd-runtime.check-reconciliation.v1',
          read_only: true,
          request_id: reqSettled,
          job_id: reqSettled,
          command: 'check',
          disposition: {
            state: 'passed',
            verdict: 'passed',
            terminal: true,
            refusal_code: null,
            created_at: '2026-10-27T16:26:00Z',
            finished_at: '2026-10-27T16:26:30Z',
            expired: false,
            purged: false,
          },
          dispatch: { status: 'dispatched', proven: true },
          accounting: { status: 'complete_dispatched', accounting_complete: true, calls: 2, known_calls: 2, unknown_calls: 0, cap: 20 },
          retry: { blocked: true, safe_next_action: 'Completed.' },
          evidence: {
            proof_basis: ['server_receipt_terminal'],
            contradictions: [],
            ledger_row_present: true,
            report_status: 'present',
            report_dispatch: 'completed',
            report_accounting_complete: true,
            prepared_receipt_status: 'valid',
            provision_phase: 'dispatched',
            accounting_custody: 'protected',
            call_records_count: 2,
            call_ledger_status: 'trusted',
            call_ledger_started: true,
            call_ledger_counts: { known: 2, unknown: 0, unused: 0 },
          },
          provenance: {
            source_sha256: 'a'.repeat(64),
            engine_sha: 'b'.repeat(40),
            server_commit: 'c'.repeat(40),
            sources_consulted: ['receipt_store'],
          },
        },
      };
    },
  });
  writeFileSync(
    join(settledDir, 'batch.json'),
    JSON.stringify({
      version: 1,
      batch: settledBatch,
      root: setup.repo,
      intent: 'check',
      login: 'octo',
      origin: settleFake.origin,
      created_at: new Date(nowMs - 60_000).toISOString(),
      rows: [{ test: 'tests/s-part.json', state: 'partial', recovery_state: 'unknown', request_ids: [reqSettled], sent_at: nowMs - 60_000, calls: 'unknown', accounting_complete: false }],
    }, null, 2),
  );
  const { ports: pSettled } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: settleFake.origin });
  const settledExit = await seam.check({ words: [], options: { '--retry-unresolved': settledBatch, '--json': true }, cwd: setup.repo }, pSettled);
  assert.equal(settledExit, 0, pSettled.stderr.text);
  assert.equal(settleFake.posts.filter(p => p.command === 'check').length, 0, 'settled pass must not be re-run');
  assert.equal(JSON.parse(pSettled.stdout.text).ai_calls, 0);

  // Fail-open when batch reconciliation hangs past timeout: warns and still retries non-passed scenario.
  const hangPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PDD_AUTO_RECONCILE_TIMEOUT_MS: '120' },
    {
      reconcileCheckBatch: (_input, p) => new Promise((_resolve, reject) => {
        p.signal?.addEventListener('abort', () => reject(p.signal.reason ?? new Error('aborted')), { once: true });
      }),
    },
  );
  const hangBatch = '20261125-100700-aa99';
  mkdirSync(join(setup.state, 'batches', hangBatch), { recursive: true });
  writeFileSync(
    join(setup.state, 'batches', hangBatch, 'batch.json'),
    JSON.stringify({
      version: 1,
      batch: hangBatch,
      root: setup.repo,
      intent: 'check',
      origin: fake.origin,
      rows: [{ test: 'tests/s-fail.json', state: 'failed', recovery_state: 'failed', request_ids: [], calls: 1, accounting_complete: true }],
    }, null, 2),
  );
  const hangExit = await seam.check({ words: [], options: { '--retry-unresolved': hangBatch, '--json': true }, cwd: setup.repo }, hangPorts.ports);
  assert.equal(hangExit, 0, hangPorts.ports.stderr.text);
  assert.match(hangPorts.ports.stderr.text, /Warning: reconciliation for batch 20261125-100700-aa99 skipped \(timed out after 120ms\)/);

  // Error validation: missing batch, wrong-repo batch, non-check batch, unsafe path in batch.
  const missingPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.check({ words: [], options: { '--retry-unresolved': '20261125-111111-zzzz' }, cwd: setup.repo }, missingPorts.ports), 2);
  assert.match(missingPorts.ports.stderr.text, /No saved batch/);

  const wrongRepoBatch = '20261125-100800-bb11';
  mkdirSync(join(setup.state, 'batches', wrongRepoBatch), { recursive: true });
  writeFileSync(
    join(setup.state, 'batches', wrongRepoBatch, 'batch.json'),
    JSON.stringify({ version: 1, batch: wrongRepoBatch, root: '/tmp/other-repo-nowhere', intent: 'check', rows: [] }),
  );
  const wrongPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.check({ words: [], options: { '--retry-unresolved': wrongRepoBatch }, cwd: setup.repo }, wrongPorts.ports), 2);
  assert.match(wrongPorts.ports.stderr.text, /different repository/);

  // Non-check batch (intent: 'lint-only') exits 2.
  const lintOnlyBatch = '20261125-100850-dd33';
  mkdirSync(join(setup.state, 'batches', lintOnlyBatch), { recursive: true });
  writeFileSync(
    join(setup.state, 'batches', lintOnlyBatch, 'batch.json'),
    JSON.stringify({ version: 1, batch: lintOnlyBatch, root: setup.repo, intent: 'lint-only', rows: [] }),
  );
  const lintOnlyPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.check({ words: [], options: { '--retry-unresolved': lintOnlyBatch }, cwd: setup.repo }, lintOnlyPorts.ports), 2);
  assert.match(lintOnlyPorts.ports.stderr.text, /no Check intent/);

  // Plain-text --retry-unresolved from subdirectory on a split-Story scenario must succeed and promote!
  const subRetryBatch = '20261125-100950-ee44';
  mkdirSync(join(setup.state, 'batches', subRetryBatch), { recursive: true });
  writeFileSync(
    join(setup.state, 'batches', subRetryBatch, 'batch.json'),
    JSON.stringify({
      version: 1,
      batch: subRetryBatch,
      root: setup.repo,
      intent: 'check',
      origin: fake.origin,
      rows: [{ test: 'tests/split.a.json', state: 'failed', recovery_state: 'failed', request_ids: [], calls: 1, accounting_complete: true }],
    }, null, 2),
  );
  const subRetryPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(
    await seam.check({ words: [], options: { '--retry-unresolved': subRetryBatch }, cwd: join(setup.repo, 'sub') }, subRetryPorts.ports),
    0,
    subRetryPorts.ports.stderr.text,
  );
  assert.match(subRetryPorts.ports.stdout.text, /tests\/split\.a\.json\s+passed/);

  const unsafeBatch = '20261125-100900-cc22';
  mkdirSync(join(setup.state, 'batches', unsafeBatch), { recursive: true });
  writeFileSync(
    join(setup.state, 'batches', unsafeBatch, 'batch.json'),
    JSON.stringify({ version: 1, batch: unsafeBatch, root: setup.repo, intent: 'check', rows: [{ test: '../escape.json', state: 'failed' }] }),
  );
  const unsafePorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state });
  assert.equal(await seam.check({ words: [], options: { '--retry-unresolved': unsafeBatch }, cwd: setup.repo }, unsafePorts.ports), 2);
  assert.match(unsafePorts.ports.stderr.text, /unsafe scenario path/);
});

test('#3703 AC4: auto-reconcile performs 0 calls on clean repos, clears stale prior reservations before dispatch, and fails open on timeout/error', async t => {
  const setup = makeSplitStoryRepo(t);
  const reconcileCalls = [];
  const fake = await fakeSplitServer(t, {
    reconcileHandler(entry) {
      reconcileCalls.push(entry.url);
      return { status: 404, json: { error: { code: 'not-found' } } };
    },
  });

  // 1. Clean repo (no stale reservations): 0 auto-reconcile calls and 0 /reconciliation HTTP calls.
  let spyInvocations = 0;
  const cleanPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin },
    {
      reconcileStaleReservations: async () => {
        spyInvocations += 1;
        return { batches_inspected: 0, cleared_count: 0, remaining_unresolved_count: 0 };
      },
    },
  );
  const cleanExit = await seam.check({ words: ['other'], options: { '--json': true, '--fresh': true }, cwd: setup.repo }, cleanPorts.ports);
  assert.equal(cleanExit, 0, cleanPorts.ports.stderr.text);
  assert.equal(spyInvocations, 0, 'clean repo must perform 0 auto-reconciliation calls');
  assert.equal(reconcileCalls.length, 0);

  // 2. Seed two stale prior batches (1 within-TTL 404 + 1 past-TTL 48h old).
  const nowMs = Date.parse('2026-10-27T16:27:47Z');
  const staleRecent = '20261027-160000-st01';
  const staleOld = '20261024-100000-st02';
  const reqRecent = '77777777-7777-4777-8777-777777777777';
  const reqOld = '88888888-8888-4888-8888-888888888888';
  for (const [id, reqId, ts] of [[staleRecent, reqRecent, nowMs - 30 * 60_000], [staleOld, reqOld, nowMs - 48 * 3_600_000]]) {
    const dir = join(setup.state, 'batches', id);
    mkdirSync(dir, { recursive: true });
    writeFileSync(
      join(dir, 'batch.json'),
      JSON.stringify({
        version: 1,
        batch: id,
        root: setup.repo,
        intent: 'check',
        login: 'octo',
        origin: fake.origin,
        created_at: new Date(ts).toISOString(),
        rows: [
          {
            test: 'tests/other.json',
            state: 'unknown',
            recovery_state: 'unknown',
            request_ids: [reqId],
            sent_at: ts,
            max_calls: 25,
            calls: 'unknown',
            accounting_complete: false,
          },
        ],
      }, null, 2),
    );
  }

  // Non-dispatch modes (--files) must NOT auto-reconcile even when stale reservations exist.
  const filesPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await seam.local({ what: 'files', words: ['other'], options: { '--json': true }, cwd: setup.repo }, filesPorts.ports), 0);
  assert.equal(reconcileCalls.length, 0, '--files must not trigger auto-reconcile');

  // Dispatch mode automatically reconciles BOTH stale batches before dispatching the new batch!
  const dispatchPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const dispatchExit = await seam.check(
    { words: ['other'], options: { '--fresh': true, '--max-total-calls': 20, '--json': true }, cwd: setup.repo },
    dispatchPorts.ports,
  );
  assert.equal(dispatchExit, 0, dispatchPorts.ports.stderr.text);
  assert.ok(reconcileCalls.some(u => u.includes(reqRecent)), 'expected within-TTL stale reservation to be reconciled');
  assert.match(dispatchPorts.ports.stderr.text, /Auto-reconciled 2 stale prior reservations across 2 batches \(0 remaining\)\./);
  assert.doesNotMatch(dispatchPorts.ports.stderr.text, /pdd test --reconcile-stale/);
  assert.equal(JSON.parse(readFileSync(join(setup.state, 'batches', staleRecent, 'batch.json'), 'utf8')).rows[0].reservation_reconciled?.cleared, true);
  assert.equal(JSON.parse(readFileSync(join(setup.state, 'batches', staleOld, 'batch.json'), 'utf8')).rows[0].reservation_reconciled?.cleared, true);

  // 3. Fail-open on bounded timeout AND on error when a new stale batch exists.
  const staleHung = '20261027-161000-st03';
  mkdirSync(join(setup.state, 'batches', staleHung), { recursive: true });
  writeFileSync(
    join(setup.state, 'batches', staleHung, 'batch.json'),
    JSON.stringify({
      version: 1,
      batch: staleHung,
      root: setup.repo,
      intent: 'check',
      login: 'octo',
      origin: fake.origin,
      created_at: new Date(nowMs - 10_000).toISOString(),
      rows: [{ test: 'tests/other.json', state: 'unknown', recovery_state: 'unknown', request_ids: ['99999999-9999-4999-8999-999999999999'], sent_at: nowMs - 10_000, calls: 'unknown', accounting_complete: false }],
    }, null, 2),
  );

  let aborted = false;
  const timeoutPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin, PDD_AUTO_RECONCILE_TIMEOUT_MS: '120' },
    {
      reconcileStaleReservations: (_input, p) => new Promise((_resolve, reject) => {
        p.signal?.addEventListener('abort', () => {
          aborted = true;
          reject(p.signal.reason ?? new Error('aborted'));
        }, { once: true });
      }),
    },
  );
  const startMs = Date.now();
  const timeoutExit = await seam.check({ words: ['other'], options: { '--fresh': true, '--json': true }, cwd: setup.repo }, timeoutPorts.ports);
  const elapsedMs = Date.now() - startMs;
  assert.equal(timeoutExit, 0, timeoutPorts.ports.stderr.text);
  assert.equal(aborted, true, 'bounded timeout must abort hung reconciliation');
  assert.ok(elapsedMs < 5000, `bounded timeout took too long (${elapsedMs}ms)`);
  assert.match(timeoutPorts.ports.stderr.text, /Warning: auto-reconciliation of stale prior reservations skipped \(timed out after 120ms\); continuing check run\./);

  const errPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin },
    {
      reconcileStaleReservations: async () => {
        throw new Error('simulated network outage');
      },
    },
  );
  const errExit = await seam.check({ words: ['other'], options: { '--fresh': true, '--json': true }, cwd: setup.repo }, errPorts.ports);
  assert.equal(errExit, 0, errPorts.ports.stderr.text);
  assert.match(errPorts.ports.stderr.text, /Warning: auto-reconciliation of stale prior reservations skipped \(simulated network outage\); continuing check run\./);

  // 4. Invalid option mixes against a state dir WITH stale reservations perform 0 auto-reconcile calls.
  let invalidSpy = 0;
  for (const invalidOpts of [
    { '--affected': true, '--files': true, '--lf': true },
    { '--retry-unresolved': 'not-a-batch' },
    { '--app-map': 'app-map.json' },
  ]) {
    const p = portsFor(
      { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin },
      { reconcileStaleReservations: async () => { invalidSpy += 1; return { batches_inspected: 0, cleared_count: 0, remaining_unresolved_count: 0 }; } },
    );
    assert.equal(await seam.check({ words: [], options: invalidOpts, cwd: setup.repo }, p.ports), 2);
  }
  assert.equal(invalidSpy, 0, 'invalid option mixes must trigger 0 auto-reconciliation calls even when stale batches exist');

  // 5. Batch whose row is already settled by a local terminal receipt triggers 0 auto-reconcile calls.
  rmSync(join(setup.state, 'batches', staleHung), { recursive: true, force: true });
  const locallySettledBatch = '20261027-161500-ls04';
  const lsReq = 'aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa';
  const lsDir = join(setup.state, 'batches', locallySettledBatch);
  mkdirSync(lsDir, { recursive: true });
  writeFileSync(
    join(lsDir, 'batch.json'),
    JSON.stringify({
      version: 1, batch: locallySettledBatch, root: setup.repo, intent: 'check', login: 'octo', origin: fake.origin,
      rows: [{ test: 'tests/other.json', state: 'unknown', recovery_state: 'unknown', request_ids: [lsReq], calls: 'unknown', accounting_complete: false }],
    }, null, 2),
  );
  writeFileSync(
    join(lsDir, `${lsReq}.json`),
    JSON.stringify({ requestId: lsReq, id: lsReq, command: 'check', state: 'passed', usage: { calls: 1 } }),
  );
  let lsSpy = 0;
  const lsPorts = portsFor(
    { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin },
    { reconcileStaleReservations: async () => { lsSpy += 1; return { batches_inspected: 0, cleared_count: 0, remaining_unresolved_count: 0 }; } },
  );
  assert.equal(await seam.check({ words: ['other'], options: { '--fresh': true, '--json': true }, cwd: setup.repo }, lsPorts.ports), 0);
  assert.equal(lsSpy, 0, 'locally settled receipt row must not trigger repeated auto-reconciliation');
});

test('#3703 AC1 & AC5: pdd test --affected --files dry-run, invalid option errors, help, and completion via real bin/pdd.mjs subprocess', async t => {
  const setup = makeSplitStoryRepo(t);
  const untouchedState = join(setup.sandbox, 'never-created-state');
  const offlineEnv = {
    ...process.env,
    HOME: setup.home,
    PDD_STATE_DIR: untouchedState,
    PDD_RUNTIME_URL: 'http://127.0.0.1:1',
    PATH: fakeGhBin(setup.sandbox, { fail: true }),
  };

  // 1. Clean repo: conservatively previews all Stories/tests with 0 AI calls, 0 gh calls, 0 state writes.
  const cleanRes = spawnSync(process.execPath, [BIN_PDD, 'test', '--affected', '--files', '--json'], {
    cwd: setup.repo,
    env: offlineEnv,
    encoding: 'utf8',
  });
  assert.equal(cleanRes.status, 0, cleanRes.stderr);
  const cleanJson = JSON.parse(cleanRes.stdout);
  assert.equal(cleanJson.affected, true);
  assert.equal(cleanJson.ai_calls, 0);
  assert.deepEqual(cleanJson.check_selection.tests.sort(), ['tests/other.json', 'tests/split.a.json', 'tests/split.b.json']);
  assert.equal(existsSync(untouchedState), false, '--affected --files must write 0 state files');

  // 2. Dirty repo changing ONLY prompts/calc.prompt.md: selects only split Story & calc prompt closure, excludes other.
  writeFileSync(
    join(setup.repo, 'prompts/calc.prompt.md'),
    makeCliPrompt('Calculator CLI', 'Compute add and sub operations on two integers accurately.', 'node bin/calc.mjs'),
  );
  const dirtyJsonRes = spawnSync(process.execPath, [BIN_PDD, 'test', '--affected', '--files', '--json'], {
    cwd: setup.repo,
    env: offlineEnv,
    encoding: 'utf8',
  });
  assert.equal(dirtyJsonRes.status, 0, dirtyJsonRes.stderr);
  const dirtyJson = JSON.parse(dirtyJsonRes.stdout);
  assert.equal(dirtyJson.affected, true);
  assert.equal(dirtyJson.ai_calls, 0);
  assert.deepEqual(dirtyJson.affected_stories, ['user_stories/split.md']);
  assert.deepEqual(dirtyJson.omitted_stories, ['user_stories/other.md']);
  assert.deepEqual(dirtyJson.check_selection.tests.sort(), ['tests/split.a.json', 'tests/split.b.json']);
  assert.deepEqual(dirtyJson.check_selection.baseline_tests, ['tests/other.json']);
  const uploadedPaths = dirtyJson.files.map(f => f.path).sort();
  assert.deepEqual(uploadedPaths, ['prompts/calc.prompt.md', 'tests/split.a.json', 'tests/split.b.json', 'user_stories/split.md']);
  assert.equal(existsSync(untouchedState), false, '--affected --files must write 0 state files');

  // Plain-text output mode of --affected --files.
  const dirtyTextRes = spawnSync(process.execPath, [BIN_PDD, 'test', '--affected', '--files'], {
    cwd: setup.repo,
    env: offlineEnv,
    encoding: 'utf8',
  });
  assert.equal(dirtyTextRes.status, 0, dirtyTextRes.stderr);
  assert.match(dirtyTextRes.stdout, /Affected selection: 2 of 3 tests \(1 Story\) selected; 1 omitted baseline test\. 0 AI calls\./);
  assert.match(dirtyTextRes.stdout, /target: user_stories\/split\.md/);
  assert.match(dirtyTextRes.stdout, /prompts\/calc\.prompt\.md/);
  assert.doesNotMatch(dirtyTextRes.stdout, /prompts\/other\.prompt\.md/);

  // 3. Invalid option combinations exit 2 with usage error on stderr and 0 network/gh/state calls.
  const invalidCases = [
    ['test', '--affected', '--files', '--lf'],
    ['test', '--affected', '--files', 'split'],
    ['test', '--affected', '--files', '--fresh'],
    ['test', '--affected', '--files', '--retry', '20261125-100000-ab12'],
    ['test', '--retry-unresolved', 'not-a-batch'],
    ['test', '--retry-unresolved', '20261125-100000-ab12', 'split'],
    ['test', '--retry-unresolved', '20261125-100000-ab12', '--retry', '20261125-100000-ab12'],
    ['test', '--retry-unresolved', '20261125-100000-ab12', '--affected'],
    ['test', '--retry-unresolved', '20261125-100000-ab12', '--files'],
    ['lint', '--retry-unresolved', '20261125-100000-ab12'],
  ];
  for (const argv of invalidCases) {
    const res = spawnSync(process.execPath, [BIN_PDD, ...argv], { cwd: setup.repo, env: offlineEnv, encoding: 'utf8' });
    assert.equal(res.status, 2, `expected exit 2 for pdd ${argv.join(' ')}, got ${res.status} (stderr: ${res.stderr})`);
    assert.ok(res.stderr.trim().length > 0, `expected stderr message for pdd ${argv.join(' ')}`);
  }
  assert.equal(existsSync(untouchedState), false, 'invalid option checks must write 0 state files');

  // Plain-text TTY --affected --files and --files must skip releaseNotice (0 network / 0 state writes).
  let releaseNoticeCalls = 0;
  const ttyOut = captureStream();
  const ttyErr = { ...captureStream(), isTTY: true };
  const ttyCode = await runPdd(['test', '--affected', '--files'], {
    cwd: setup.repo,
    env: offlineEnv,
    stdout: ttyOut,
    stderr: ttyErr,
    releaseNotice: async () => {
      releaseNoticeCalls += 1;
      return 'should not run';
    },
  });
  assert.equal(ttyCode, 0, ttyErr.text);
  assert.equal(releaseNoticeCalls, 0, 'pdd test --affected --files in TTY must skip releaseNotice');
  assert.equal(existsSync(untouchedState), false, 'TTY --affected --files must write 0 state files');

  // Native-only sibling must NOT falsely satisfy sibling coverage for targeted slice (fail-closed exit 5).
  const nativeSetup = makeSplitStoryRepo(t);
  writeFileSync(
    join(nativeSetup.repo, 'prompts/native_sub.prompt.md'),
    '---\nkind: native-only\n---\n\n# Native subtraction helper\n\nSubtract integers using OS API.\n\n## Dependencies\n\nNone.\n',
  );
  const splitBDoc = JSON.parse(readFileSync(join(nativeSetup.repo, 'tests/split.b.json'), 'utf8'));
  splitBDoc.steps[0].entry_path = 'prompts/native_sub.prompt.md';
  writeFileSync(join(nativeSetup.repo, 'tests/split.b.json'), `${JSON.stringify(splitBDoc, null, 2)}\n`);
  const nativeFake = await fakeSplitServer(t);
  const nativePorts = portsFor({ HOME: nativeSetup.home, PDD_STATE_DIR: nativeSetup.state, PDD_RUNTIME_URL: nativeFake.origin });
  const nativeSliceExit = await seam.check({ words: ['tests/split.a.json'], options: { '--json': true }, cwd: nativeSetup.repo }, nativePorts.ports);
  assert.equal(nativeSliceExit, 5, 'native-only sibling must not satisfy targeted-slice coverage');
  assert.equal(JSON.parse(nativePorts.ports.stdout.text).rows[0].reason.code, 'criteria-not-checked');

  // 4. Help and shell completions expose --retry-unresolved and --affected --files.
  const helpRes = spawnSync(process.execPath, [BIN_PDD, 'test', '--help'], { cwd: setup.repo, env: offlineEnv, encoding: 'utf8' });
  assert.equal(helpRes.status, 0, helpRes.stderr);
  assert.match(helpRes.stdout, /pdd test --affected --files \[--app-map PATH\] \[--json\]/);
  assert.match(helpRes.stdout, /pdd test --retry-unresolved BATCH/);

  for (const shell of ['bash', 'zsh']) {
    const comp = spawnSync(process.execPath, [BIN_PDD, 'completion', shell], {
      cwd: setup.repo,
      env: offlineEnv,
      encoding: 'utf8',
    });
    assert.equal(comp.status, 0, comp.stderr);
    assert.match(comp.stdout, /--retry-unresolved/);
  }
});
