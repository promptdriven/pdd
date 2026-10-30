import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { readProduct, productStatus, productNext, productStart, runProduct } from '../src/product.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { readWorkflowAreas } from '../src/workflow-areas.mjs';
import { storyEvidence } from '../src/workflow-runner.mjs';
import { sourceFingerprint } from '../src/workflow-replay.mjs';
import { resolveWorkflowRepository } from '../src/workflow-github.mjs';

const root = new URL('../', import.meta.url).pathname;
const stream = () => ({ text: '', write(value) { this.text += value; } });
const pr = (number, state = 'OPEN', extra = {}) => ({ number, url: `https://github.com/example/coffee/pull/${number}`, isCrossRepository: false, headRepository: {name:'coffee'}, headRepositoryOwner:{login:'example'}, headRefName: `branch-${number}`, state, body: `PR 2 of this run: the code.\n<!-- pdd-workflow:run-${number}:code -->`, isDraft: true, updatedAt: `2026-10-${number}`, ...extra });
function fixture(t) {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-product-'));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  cpSync(new URL('../examples/coffee-pickup/', import.meta.url), cwd, { recursive: true });
  const state = { issues: [], runs: [], prs: [], events: [], base: true, starts: [], commands: [] };
  const ports = {
    readProductState: async () => ({ json: state.productState ?? null }),
    writeProductState: async ({ json }) => { state.productState = json; return {}; },
    now: async () => ({ milliseconds: (state.clock = (state.clock ?? 0) + 60000) }),
    issueByNumber: async ({ number }) => {
      if (state.fail) throw Error('GitHub unavailable');
      const row = (state.pages?.flat() ?? state.issues).find(item => item.number === number);
      return row && { author_association: 'MEMBER', user: { login: 'member' }, created_at: '2026-10-01T00:00:00Z', ...row };
    },
    listRuns: async () => state.runs,
    openBaseSource: async () => ({root:cwd,handle:null}),
    resolveRepository: async () => ({ repository: 'example/coffee', defaultBranch: 'alpha' }),
    planOnBase: async args => { state.baseArgs = args; return state.base; },
    storyEvidence: async run => run.rows ?? [],
    startRun: async args => { state.starts.push(args); return { exitCode: 0, message: `Started feature #${args.issue}.` }; },
    execFile: async (file, args) => {
      state.commands.push({ file, args });
      if (state.fail) throw Error('GitHub unavailable');
      assert.equal(file, 'gh');
      if (args[0] === 'api') {
        if (args[1].includes('/timeline?')) return {stdout:JSON.stringify(state.events.map(event => ({event:'cross-referenced',...event})))};
        const all = (state.pages?.flat() ?? state.issues).map(item => ({author_association:'MEMBER',user:{login:'member'},created_at:'2026-10-01T00:00:00Z',...item}));
        const query = new URL('https://api.github.com/'+args[1]).searchParams, page=Number(query.get('page')), size=Number(query.get('per_page'));
        return {stdout:JSON.stringify({items:all.slice((page-1)*size,page*size),total_count:all.length,incomplete_results:false})};
      }
      if (args[0] === 'issue' && args[1] === 'create') {
        const issue = { number: 81 + state.issues.length, state: 'OPEN', body: args[args.indexOf('--body') + 1] };
        state.issues.push(issue); return { stdout: `https://github.com/example/coffee/issues/${issue.number}\n` };
      }
      if (args[0] === 'pr' && args[1] === 'view') return {stdout:JSON.stringify(state.prs.find(pr => pr.number === Number(args[2])))};
      assert.fail(`${file} ${args.join(' ')}`);
    },
  };
  return { cwd, state, ports };
}
const issue = (run, number = 81) => ({ number, state: 'OPEN', body: `<!-- pdd-product: run=${run} -->` });

test('product workflow parses without changing runner phases; catalog exposes commands and options', () => {
  const areas = readWorkflowAreas({ packageRoot: root, cwd: root, home: '/missing', name: 'product' }).areas;
  assert.deepEqual(areas.map(area => [area.name, area.gate]), [['map', 'approve'], ['plan', 'pr']]);
  assert.equal(parseArgv(['product', 'status', '--json']).local, 'product-status');
  assert.equal(parseArgv(['product', 'start', 'phone-1', '--no-run', '--agent', 'claude']).options['--no-run'], true);
  assert.throws(() => parseArgv(['product', 'start', 'phone-1', '--agent', 'other']));
});

test('coffee example provides three parts, twelve core Stories and four planned runs', async t => {
  const f = fixture(t), product = await readProduct({ cwd: f.cwd }, f.ports);
  assert.equal(product.name, 'Coffee pickup'); assert.equal(product.size, 'medium');
  assert.equal(product.stories.filter(story => story.tag === 'CORE').length, 12);
  assert.deepEqual(product.runs.map(run => run.run), ['server-1', 'phone-1', 'barista-1', 'journeys']);
  assert.deepEqual((await productNext({ cwd: f.cwd }, f.ports)).ready, ['server-1', 'phone-1', 'barista-1']);
});

test('start creates exactly once, preserves body/contracts and safely passes multiline text', async t => {
  const f = fixture(t), input = { cwd: f.cwd, run: 'phone-1', noRun: true };
  const first = await productStart(input, f.ports), second = await productStart(input, f.ports);
  assert.equal(first.created, true); assert.equal(second.created, false); assert.equal(first.issue, second.issue);
  assert.equal(f.state.commands.filter(call => call.args[0] === 'issue').length, 1);
  assert.match(f.state.issues[0].body, /contracts\/phone-server\.md/);
  assert.match(f.state.issues[0].body, /P01: I see the menu with prices\./);
  assert.equal((f.state.issues[0].body.match(/pdd-product:/g) ?? []).length, 1);
  assert.equal(f.state.starts.length, 0);
});

test('exact marker on a later closed page is reused; lookup failures and unknown runs never create', async t => {
  const f = fixture(t); f.state.pages = [[issue('phone-10')], [{ ...issue('phone-1', 92), state: 'CLOSED' }]];
  assert.equal((await productStart({ cwd: f.cwd, run: 'phone-1', agent: 'claude' }, f.ports)).issue, 92);
  assert.equal(f.state.starts[0].agent, 'claude');
  f.state.fail = true;
  assert.equal((await productStart({ cwd: f.cwd, run: 'phone-1' }, f.ports)).exitCode, 1);
  const before = f.state.commands.length;
  assert.equal((await productStart({ cwd: f.cwd, run: 'missing' }, f.ports)).exitCode, 1);
  assert.equal(f.state.commands.length, before);
  assert.equal(f.state.commands.some(call => call.args[0] === 'issue'), false);
});

test('only a merged implementation PR satisfies needs, not stopped prompt-only workflows', async t => {
  const f = fixture(t);
  f.state.issues = ['server-1', 'phone-1', 'barista-1'].map((name, i) => issue(name, 81 + i));
  f.state.runs = f.state.issues.map((item, i) => ({ number: item.number, state: 'completed', doneAt: 'PR 1', pr: [{ number: 20 + i, stage: 'prompt-pr', branch: `branch-${20+i}` }], rows: [] }));
  f.state.prs = [20, 21, 22].map(number => pr(number, 'MERGED', { body: 'PR 1 of this run: the prompt, Story and test cases.' }));
  assert.deepEqual((await productNext({ cwd: f.cwd }, f.ports)).ready, []);
  f.state.runs.forEach((run, i) => run.pr.push({ number: 30 + i, stage: 'code', branch: `branch-${30+i}` }));
  f.state.prs.push(...[30, 31, 32].map(number => pr(number, 'MERGED')));
  assert.deepEqual((await productNext({ cwd: f.cwd }, f.ports)).ready, ['journeys']);
});

test('base-plan lookup uses saved product base; missing plan advises explicit start without blocking', async t => {
  const f = fixture(t); f.state.base = false; f.state.runs.push({ workflow: 'product', number: 50, baseBranch: 'review-base' });
  assert.deepEqual((await productNext({ cwd: f.cwd }, f.ports)).ready, []);
  assert.equal(f.state.baseArgs.baseBranch, 'review-base');
  const started = await productStart({ cwd: f.cwd, run: 'phone-1' }, f.ports);
  assert.equal(started.exitCode, 0); assert.match(started.message, /Advice: phone-1 still needs plan PR/); assert.equal(f.state.starts.length, 1);
});

test('remote PR evidence is labelled and counts only exact leading Story ids', async t => {
  const f = fixture(t); f.state.issues = [issue('phone-1')];
  f.state.events = [{ source: { issue: { pull_request: { html_url: 'https://github.com/example/coffee/pull/61' } } } }];
  f.state.prs = [pr(61, 'OPEN', { body: '<!-- pdd-product: run=phone-1 -->\nRuntime check (user_stories/P01-menu.md): ✓ 1 of 1 criteria\nRuntime check (P010-wrong): ✓ 1 of 1 criteria' })];
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.equal(status.parts[0].pass, 1); assert.equal(status.runs[1].fromPr, 61);
  assert.match((await runProduct({ cwd: f.cwd, command: 'status' }, f.ports)).message, /from PR #61/);
});

test('shared evidence preserves partial compatible Stories and reports stale evidence separately', t => {
  const f = fixture(t); execFileSync('git', ['init', '-q'], { cwd: f.cwd }); execFileSync('git', ['add', '.'], { cwd: f.cwd });
  const sha256 = sourceFingerprint(f.cwd), source = { kind: 'git-content-v1', sha256 };
  const run = { root: f.cwd, runtimeHistory: [
    { at: 1, source, summary: 'Runtime check (P01-menu): ✓\nRuntime check (P02-order): ✓' },
    { at: 2, source: { ...source, sha256: '0'.repeat(64) }, summary: 'Runtime check (P01-menu): ✗\nRuntime check (P03-ready): ✓' },
    { at: 3, source, summary: 'Runtime check (P02-order): ✗' },
  ] };
  const rows = storyEvidence(run);
  assert.deepEqual(rows.find(row => row.story === 'P01-menu'), { story: 'P01-menu', current: true, pass: true, result: '✓', at: 1 });
  assert.equal(rows.find(row => row.story === 'P02-order').pass, false);
  assert.equal(rows.find(row => row.story === 'P03-ready').current, false);
});

test('CLI resolves subdirectory and delegates parsed values once; malformed replies remain finite', async () => {
  const stdout = stream(), stderr = stream(), calls = [];
  const deps = { stdout, stderr, cwd: '/repo/sub', packageRoot: '/bundle', gitContext: async cwd => { assert.equal(cwd, '/repo/sub'); return { toplevel: '/repo' }; },
    product: { runProduct: async args => { calls.push(args); return { exitCode: 0, message: 'Ready.' }; } } };
  assert.equal(await runPdd(['product', 'start', 'phone-1', '--no-run', '--agent', 'claude'], deps), 0);
  assert.deepEqual(calls, [{ command: 'start', run: 'phone-1', noRun: true, agent: 'claude', json: false, cwd: '/repo', packageRoot: '/bundle' }]);
  assert.equal(stdout.text, 'Ready.\n'); assert.equal(stderr.text, '');
  deps.product.runProduct = async () => null;
  assert.equal(await runPdd(['product', 'next'], deps), 1);
  assert.match(stderr.text, /product command failed/);
});

test('default plan lookup honors existing origin ref absence without falling back to local plan', async t => {
  const f = fixture(t); execFileSync('git', ['init', '-q', '-b', 'alpha'], { cwd: f.cwd });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: f.cwd }); execFileSync('git', ['config', 'user.email', 'test@example.invalid'], { cwd: f.cwd });
  writeFileSync(join(f.cwd, 'baseline.txt'), 'base'); execFileSync('git', ['add', 'baseline.txt'], { cwd: f.cwd }); execFileSync('git', ['commit', '-qm', 'base'], { cwd: f.cwd });
  execFileSync('git', ['update-ref', 'refs/remotes/origin/alpha', 'HEAD'], { cwd: f.cwd });
  execFileSync('git', ['add', '.'], { cwd: f.cwd }); execFileSync('git', ['commit', '-qm', 'plan local only'], { cwd: f.cwd });
  delete f.ports.planOnBase;
  const gh = f.ports.execFile; f.ports.execFile = async (file, args, options) => file === 'git' ? { stdout: execFileSync(file, args, { ...options, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }) } : gh(file, args, options);
  // execFileSync errors are native process errors with numeric status rather than code; adapt at the port boundary.
  const exec = f.ports.execFile; f.ports.execFile = async (...args) => { try { return await exec(...args); } catch (error) { if (Number.isInteger(error.status)) return { stdout: '', stderr: error.stderr?.toString(), code: error.status }; throw error; } };
  assert.deepEqual((await productNext({ cwd: f.cwd }, f.ports)).ready, []);
  execFileSync('git', ['update-ref', '-d', 'refs/remotes/origin/alpha'], { cwd: f.cwd });
  assert.deepEqual((await productNext({ cwd: f.cwd }, f.ports)).ready, ['server-1', 'phone-1', 'barista-1']);
});

test('shared repository identity export uses verified GitHub origin metadata', async () => {
  const calls = [];
  const result = await resolveWorkflowRepository({ cwd: '/repo' }, { execFile: async (file, args) => {
    calls.push([file, ...args]); return { stdout: file === 'git' ? 'git@github.com:example/coffee.git\n' : JSON.stringify({ nameWithOwner: 'example/coffee', url: 'https://github.com/example/coffee', defaultBranchRef: { name: 'alpha' } }) };
  } });
  assert.deepEqual(result, { repository: 'example/coffee', defaultBranch: 'alpha' }); assert.equal(calls.length, 2);
});

test('a near-prefix pass and a stale pass never become a local current pass', async t => {
  const f = fixture(t); f.state.issues = [issue('phone-1')];
  f.state.runs = [{ number: 81, state: 'running', rows: [
    { story: 'P010-unrelated', pass: true, current: true },
    { story: 'P02-order', pass: true, current: false },
    { story: 'P03-ready', pass: false, current: true },
  ] }];
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.deepEqual(status.parts[0], { part: 'phone', total: 4, pass: 0, stale: 1, notRun: 3 });
});

test('an oversized planned run warns without preventing explicit issue preparation', async t => {
  const f = fixture(t), map = join(f.cwd, 'product/map.md'), plan = join(f.cwd, 'product/plan.md');
  const ids = Array.from({ length: 13 }, (_, i) => `P${i + 10}`);
  writeFileSync(map, readFileSync(map, 'utf8').replace('## Journeys', ids.map(id => `| ${id} | phone | I use ${id}. | CORE |`).join('\n') + '\n\n## Journeys'));
  writeFileSync(plan, readFileSync(plan, 'utf8').replace('P01, P02, P03, P04 | plan PR', `${ids.join(', ')} | plan PR`));
  const result = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(result.exitCode, 0); assert.match(result.message, /Warning: phone-1 has 13 Stories/);
  assert.equal(f.state.issues.length, 1);
});

test('real CLI process resolves nested repo cwd with a fake gh executable and no runtime', t => {
  const f = fixture(t); execFileSync('git', ['init', '-q', '-b', 'alpha'], { cwd: f.cwd });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: f.cwd }); execFileSync('git', ['config', 'user.email', 'test@example.invalid'], { cwd: f.cwd });
  execFileSync('git', ['remote', 'add', 'origin', 'https://github.com/example/coffee.git'], { cwd: f.cwd });
  execFileSync('git', ['add', '.'], { cwd: f.cwd }); execFileSync('git', ['commit', '-qm', 'reviewed plan'], { cwd: f.cwd });
  const bin = join(f.cwd, 'fake-bin'); mkdirSync(bin); mkdirSync(join(f.cwd, 'nested'));
  writeFileSync(join(bin, 'gh'), '#!/usr/bin/env node\nconst args=process.argv.slice(2);process.stdout.write(JSON.stringify(args[0]==="repo"?{nameWithOwner:"example/coffee",defaultBranchRef:{name:"alpha"},url:"https://github.com/example/coffee"}:{items:[],total_count:0,incomplete_results:false}));\n', { mode: 0o755 });
  const output = execFileSync(process.execPath, [join(root, 'bin/pdd.mjs'), 'product', 'next'], { cwd: join(f.cwd, 'nested'), encoding: 'utf8', env: { ...process.env, HOME: f.cwd, PATH: `${bin}:${process.env.PATH}` } });
  assert.match(output, /server-1, phone-1, barista-1/); assert.match(output, /pdd product start phone-1/);
});

const tipsMap = () => JSON.parse(readFileSync(new URL('./runtime/product-map.json', import.meta.url))).initial_world.files['/project/product/map.md'].content;
test('small map-only start hands off its map and folder without absent contract dependencies', async t => {
  const f = fixture(t);
  writeFileSync(join(f.cwd, 'product/map.md'), tipsMap());
  rmSync(join(f.cwd, 'product/plan.md')); rmSync(join(f.cwd, 'contracts'), { recursive: true });
  const result = await productStart({ cwd: f.cwd, run: 'tips', noRun: true }, f.ports);
  assert.equal(result.exitCode, 0); assert.equal(f.state.issues.length, 1);
  const body = f.state.issues[0].body;
  assert.match(body, /product\/map\.md/); assert.match(body, /prompts\/tips/);
  assert.deepEqual(body.match(/contracts\/[A-Za-z0-9_./-]+/g) ?? [], []);
  assert.equal(f.state.starts.length, 0);
});

test('missing required table columns fail before returning incomplete structures or creating an issue', async t => {
  for (const [file, section, column] of [
    ['map', 'Parts', 'Folder'], ['map', 'Stories', 'Story'], ['map', 'Stories', 'Tag'],
    ['map', 'Journeys', 'Journey'], ['map', 'Questions', 'Answer'],
    ['plan', 'Runs', 'Needs'], ['plan', 'Boundaries', 'Contract'],
  ]) {
    const f = fixture(t), path = join(f.cwd, `product/${file}.md`);
    const text = readFileSync(path, 'utf8').replace(new RegExp(`(## ${section}\\n)([\\s\\S]*?)(?=\\n## |$)`), (whole, heading, table) => {
      const lines = table.split('\n'), index = lines.find(line => line.startsWith('|')).split('|').findIndex(cell => cell.trim() === column);
      return heading + lines.map(line => line.startsWith('|') ? line.split('|').filter((cell, i) => i !== index).join('|') : line).join('\n');
    });
    writeFileSync(path, text);
    await assert.rejects(readProduct({ cwd: f.cwd }, f.ports), error => error.code === 'invalid-product' && error.message.includes(`product/${file}.md`) && error.message.includes(column), `${section}/${column}`);
    const result = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
    assert.notEqual(result.exitCode, 0); assert.equal(f.state.issues.length, 0); assert.equal(f.state.commands.length, 0);
  }
});

test('escaped pipes stay in Story cells and preserve the CORE Story in the small run and issue', async t => {
  for (const [cell, story] of [
    [String.raw`I run x \| y.`, 'I run x | y.'], [String.raw`I see \|`, 'I see |'],
    [String.raw`I compare x \| y \| z.`, 'I compare x | y | z.'],
    [String.raw`I keep C:\tmp and x \| y.`, String.raw`I keep C:\tmp and x | y.`],
  ]) {
    const f = fixture(t);
    writeFileSync(join(f.cwd, 'product/map.md'), tipsMap().replace('I enter a bill.', cell));
    rmSync(join(f.cwd, 'product/plan.md'));
    const product = await readProduct({ cwd: f.cwd }, f.ports);
    assert.equal(product.stories[0].story, story); assert.equal(product.stories[0].tag, 'CORE');
    assert.deepEqual(product.runs[0].stories, ['T01', 'T02', 'T03', 'T04']);
    const result = await productStart({ cwd: f.cwd, run: 'tips', noRun: true }, f.ports);
    assert.equal(result.exitCode, 0); assert.ok(f.state.issues[0].body.includes(`T01: ${story}`));
  }
});

test('issue creation port receives the planned handoff and starts the returned issue once', async t => {
  const f = fixture(t), creates = [];
  f.state.runs.push({ workflow: 'product', number: 50, baseBranch: 'alpha' });
  f.ports.createIssue = async payload => { creates.push(payload); return { url: 'https://github.com/example/coffee/issues/82' }; };
  const result = await productStart({ cwd: f.cwd, run: 'barista-1', agent: 'claude' }, f.ports);
  assert.equal(result.exitCode, 0); assert.equal(result.issue, 82); assert.equal(result.created, true); assert.equal(result.started, true);
  assert.equal(creates.length, 1); assert.equal(creates[0].repository, 'example/coffee');
  for (const id of ['barista-1', 'B01', 'B02', 'B03', 'B04']) assert.ok(creates[0].title.includes(id));
  for (const value of ['Part of #50', 'prompts/barista', 'contracts/server-barista.md', 'contracts/world.md', '<!-- pdd-product: run=barista-1 -->']) assert.ok(creates[0].body.includes(value));
  assert.deepEqual(f.state.starts, [{ name: 'feature', issue: 82, agent: 'claude', cwd: f.cwd }]);
  assert.equal(f.state.commands.some(call => call.args[0] === 'issue'), false);
});

test('unconfirmed creation-port replies never start a workflow or retry the mutation', async t => {
  for (const response of [null, { url: 'https://github.com/other/coffee/issues/82' }, { url: 'not-an-issue' }]) {
    const f = fixture(t); let creates = 0;
    f.ports.createIssue = async () => { creates++; return response; };
    const result = await productStart({ cwd: f.cwd, run: 'barista-1' }, f.ports);
    assert.notEqual(result.exitCode, 0); assert.equal(result.started, false); assert.equal(creates, 1);
    assert.equal(f.state.starts.length, 0); assert.equal(f.state.commands.some(call => call.args[0] === 'issue'), false);
  }
});

test('ready-run guidance offers parallel or in-order work while retaining the small path', async t => {
  const f = fixture(t), guidance = 'These can run in parallel, or one person can start them in order.';
  assert.equal((await productNext({ cwd: f.cwd }, f.ports)).guidance, guidance);
  assert.ok((await runProduct({ cwd: f.cwd, command: 'next' }, f.ports)).message.includes(guidance));
  f.state.issues = [issue('server-1'), issue('phone-1', 82)];
  assert.equal((await productNext({ cwd: f.cwd }, f.ports)).guidance, '');
  writeFileSync(join(f.cwd, 'product/map.md'), tipsMap()); rmSync(join(f.cwd, 'product/plan.md'));
  f.state.issues = [];
  assert.equal((await productNext({ cwd: f.cwd }, f.ports)).guidance, 'run one feature run');
});

for (const latestPass of [true, false]) {
  test(`newest source-compatible receipt wins across runs when latest pass is ${latestPass}`, async t => {
    const f = fixture(t), other = fixture(t);
    for (const cwd of [f.cwd, other.cwd]) {
      execFileSync('git', ['init', '-q'], { cwd });
      execFileSync('git', ['add', '.'], { cwd });
    }
    const receipt = (cwd, at, pass) => ({ root: cwd, state: 'running', pr: [], runtimeHistory: [{
      at, source: { kind: 'git-content-v1', sha256: sourceFingerprint(cwd) },
      summary: `Runtime check (P01-menu): ${pass ? '✓' : '✗'}`,
    }] });
    f.state.issues = [issue('phone-1', 81), issue('barista-1', 82)];
    f.state.runs = [
      { number: 81, ...receipt(f.cwd, 20, latestPass) },
      { number: 82, ...receipt(other.cwd, 10, !latestPass) },
    ];
    delete f.ports.storyEvidence;
    const status = await productStatus({ cwd: f.cwd }, f.ports);
    assert.deepEqual(status.parts[0], { part: 'phone', total: 4, pass: latestPass ? 1 : 0, stale: 0, notRun: latestPass ? 3 : 4 });
    const planPath = join(f.cwd, 'product/plan.md');
    const plan = readFileSync(planPath, 'utf8');
    const phone = plan.split('\n').find(line => line.startsWith('| phone-1 |'));
    const barista = plan.split('\n').find(line => line.startsWith('| barista-1 |'));
    writeFileSync(planPath, plan.replace(phone, '__swap__').replace(barista, phone).replace('__swap__', barista));
    f.state.runs[0].runtimeHistory[0].source.sha256 = sourceFingerprint(f.cwd);
    assert.deepEqual((await productStatus({ cwd: f.cwd }, f.ports)).parts[0], status.parts[0]);
  });
}

test('remote progress uses PR receipt time across runs and keeps each PR source label', async t => {
  const f = fixture(t); f.state.issues = [issue('phone-1', 81), issue('barista-1', 82)];
  f.state.prs = [
    pr(61, 'OPEN', { updatedAt: '2026-10-30T00:00:20Z', body: '<!-- pdd-product: run=phone-1 -->\nRuntime check (P01-menu): ✓ 1 of 1 criteria' }),
    pr(62, 'OPEN', { updatedAt: '2026-10-30T00:00:10Z', body: '<!-- pdd-product: run=barista-1 -->\nRuntime check (P01-menu): ✗ 0 of 1 criteria' }),
  ];
  const gh = f.ports.execFile;
  f.ports.execFile = async (file, args) => {
    const number = /\/issues\/(81|82)\/timeline\?/.exec(args[1])?.[1];
    return number ? { stdout: JSON.stringify([{ event: 'cross-referenced', source: { issue: { pull_request: {
      html_url: `https://github.com/example/coffee/pull/${number === '81' ? 61 : 62}`,
    } } } }]) } : gh(file, args);
  };
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.deepEqual(status.parts[0], { part: 'phone', total: 4, pass: 1, stale: 0, notRun: 3 });
  assert.equal(status.runs.find(row => row.run === 'phone-1').fromPr, 61);
  assert.equal(status.runs.find(row => row.run === 'barista-1').fromPr, 62);
});
