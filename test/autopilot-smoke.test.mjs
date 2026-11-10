import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { loadSmokeFixture, readSmokeResults, runSmoke } from '../scripts/autopilot-smoke.mjs';

const fixtureRoot = resolve('fixtures/autopilot-smoke');
const createdAt = '2026-11-10T10:00:00Z';
const repo = 'example/smoke';
const iso = text => new Date(text).toISOString();
const noPrograms = () => { throw Error('No program may run'); };
function scratch(t) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-smoke-test-'));
  t.after(() => fs.rmSync(root, {recursive: true, force: true}));
  return root;
}
function world() {
  const fixture = loadSmokeFixture({root: fixtureRoot});
  const issues = fixture.issues.map((issue, index) => ({number: index + 1,
    title: issue.title, body: issue.body, state: 'open', created_at: createdAt,
    closed_at: null, html_url: `https://github.com/${repo}/issues/${index + 1}`}));
  const comments = new Map();
  const prs = [];
  const calls = [];
  const ports = {now: () => Date.parse('2026-11-10T10:10:00Z'),
    run(program, args) {
      calls.push([program, args]);
      assert.equal(program, 'gh');
      const endpoint = args.find(arg => arg.startsWith('repos/'));
      if (endpoint === `repos/${repo}/issues?state=all&per_page=100`) {
        assert.ok(args.includes('--paginate'));
        assert.ok(args.includes('--slurp'));
        assert.ok(args.includes('GET'));
        return {code: 0, stdout: JSON.stringify([[issues[0]], issues.slice(1)])};
      }
      if (endpoint?.includes('/comments?')) {
        return {code: 0, stdout: JSON.stringify(comments.get(Number(endpoint.split('/')[4])) ?? [[]])};
      }
      assert.deepEqual(args, ['pr', 'list', '--repo', repo, '--state', 'merged', '--limit', '1000',
        '--json', 'number,url,mergedAt,closingIssuesReferences']);
      return {code: 0, stdout: JSON.stringify(prs)};
    }};
  return {fixture, issues, comments, prs, ports, calls};
}

test('fixture loader loads sorted fixed issues, exact base bytes and a passing Node package', t => {
  const fixture = loadSmokeFixture({root: fixtureRoot});
  assert.deepEqual(fixture.issues.map(issue => issue.id), ['01-doc', '02-bug', '03-feature']);
  assert.match(fixture.issues[0].body, /<!-- pdd:autopilot-smoke:01-doc -->$/);
  assert.equal(fixture.files.find(file => file.path === 'README.md').content,
    fs.readFileSync(join(fixtureRoot, 'base/README.md'), 'utf8'));
  const destination = scratch(t);
  fs.cpSync(join(fixtureRoot, 'base'), destination, {recursive: true});
  const env = {...process.env};
  delete env.NODE_TEST_CONTEXT;
  const base = spawnSync(process.execPath, ['--test', '--test-reporter=tap', 'test/helpers.test.mjs'],
    {cwd: destination, encoding: 'utf8', env});
  assert.equal(base.status, 0, base.stdout + base.stderr);
  assert.match(base.stdout, /# tests 3/);
});

test('vendored base reproduces the bug and does not yet provide the requested feature', async () => {
  const {clamp, sum} = await import('../fixtures/autopilot-smoke/base/src/helpers.mjs');
  assert.equal(clamp(7, -10, 0), 7, 'seed bug is observable');
  assert.equal(clamp(-3, -10, 0), -3);
  assert.equal(sum([1, 2], 10), 3, 'optional starting total is not implemented');
});

test('loader rejects missing bodies, too few issues and a base symlink', t => {
  const root = scratch(t);
  fs.cpSync(fixtureRoot, root, {recursive: true});
  fs.writeFileSync(join(root, 'issues/01-doc.md'), '# Missing body\n');
  assert.throws(() => loadSmokeFixture({root}), /body/i);
  fs.rmSync(join(root, 'issues/01-doc.md'));
  assert.throws(() => loadSmokeFixture({root}), /3.*5/);
  fs.cpSync(fixtureRoot, root, {recursive: true});
  fs.symlinkSync('/etc/passwd', join(root, 'base/outside'));
  assert.throws(() => loadSmokeFixture({root}), /regular|symlink/i);
});

test('loader rejects marker injection, malformed names and missing native test command', t => {
  const root = scratch(t);
  fs.cpSync(fixtureRoot, root, {recursive: true});
  fs.appendFileSync(join(root, 'issues/01-doc.md'), '\n<!-- pdd:autopilot-smoke:other -->');
  assert.throws(() => loadSmokeFixture({root}), /marker/i);
  fs.cpSync(fixtureRoot, root, {recursive: true});
  fs.renameSync(join(root, 'issues/01-doc.md'), join(root, 'issues/unsafe name.md'));
  assert.throws(() => loadSmokeFixture({root}), /name/i);
  fs.rmSync(join(root, 'issues/unsafe name.md'));
  fs.cpSync(fixtureRoot, root, {recursive: true});
  fs.writeFileSync(join(root, 'base/package.json'), '{}');
  assert.throws(() => loadSmokeFixture({root}), /test/i);
});

test('dry run creates no files or subprocesses and prints the full opt-in plan', () => {
  const lines = [];
  const fixture = loadSmokeFixture({root: fixtureRoot});
  const result = runSmoke(['--owner', 'example'], {fixture, fs: {}, run: noPrograms,
    now: () => Date.parse(createdAt), id: () => 'abc123', log: line => lines.push(line)});
  assert.equal(result.exitCode, 0, result.message);
  const output = lines.join('\n');
  assert.match(output, /Dry run/);
  assert.match(output, /example\/autopilot-smoke-20261110T100000Z-abc123/);
  assert.match(output, /private/);
  for (const issue of fixture.issues) assert.ok(output.includes(issue.title));
  assert.match(output, /pdd:autopilot/);
  assert.match(output, /gh repo delete example\//);
});

test('argument rejection and help cannot spawn programs', () => {
  for (const args of [[], ['--owner'], ['--owner', '-bad'], ['--owner', 'a/b'],
    ['--owner', 'a;echo'], ['--owner', 'a', '--owner', 'b'], ['--apply'], ['--unknown'],
    ['--check', 'a/b', '--apply'], ['--check', '../bad'], ['--check', 'a/..'],
    ['--check', 'a/b', '--owner', 'a']]) {
    assert.equal(runSmoke(args, {run: noPrograms}).exitCode, 1, JSON.stringify(args));
  }
  assert.equal(runSmoke(['--help'], {run: noPrograms}).exitCode, 0);
});

test('apply uses a private fresh repo, exact fixture, labelled issues and always cleans local staging', t => {
  const root = scratch(t), lines = [], calls = [];
  let staging;
  const result = runSmoke(['--owner', 'example', '--apply'], {now: () => Date.parse(createdAt),
    id: () => 'abc123', log: line => lines.push(line),
    fs: {...fs, mkdtempSync: () => (staging = fs.mkdtempSync(join(root, 'stage-')))},
    run(program, args, options) {
      calls.push([program, args, options]);
      if (program === 'gh' && args[0] === 'repo') {
        assert.equal(args[1], 'create');
        assert.ok(args.includes('--private'));
        assert.ok(args.includes('--push'));
        assert.ok(lines.some(line => line.startsWith('Delete manually:')));
        assert.equal(fs.readFileSync(join(staging, 'README.md'), 'utf8'),
          fs.readFileSync(join(fixtureRoot, 'base/README.md'), 'utf8'));
      }
      const number = calls.filter(call => call[0] === 'gh' && call[1][0] === 'issue').length;
      return {code: 0, stdout: args[0] === 'issue' ? `https://github.com/example/smoke/issues/${number}\n` : ''};
    }});
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(fs.existsSync(staging), false);
  const issues = calls.filter(([program, args]) => program === 'gh' && args[0] === 'issue');
  assert.equal(issues.length, 3);
  assert.ok(issues.every(([, args]) => args.includes('pdd:autopilot')));
  assert.ok(issues.every(([, args, options]) => args.includes('--body-file') && args.includes('-') &&
    options.input.includes('<!-- pdd:autopilot-smoke:')));
  assert.ok(calls.some(([program, args]) => program === 'git' && args.includes('core.hooksPath=/dev/null')));
});

test('failed apply stops without retry or deletion and retains recovery identity without leaking stderr', t => {
  const root = scratch(t), lines = [], calls = [];
  let staging;
  const result = runSmoke(['--owner', 'example', '--apply'], {log: line => lines.push(line),
    fs: {...fs, mkdtempSync: () => (staging = fs.mkdtempSync(join(root, 'stage-')))},
    run(program, args) {
      calls.push([program, args]);
      return {code: args[0] === 'label' ? 1 : 0, stdout: '', stderr: 'SECRET_SENTINEL'};
    }});
  assert.equal(result.exitCode, 1);
  assert.equal(fs.existsSync(staging), false);
  assert.ok(lines.join('\n').includes('Delete manually: gh repo delete example/'));
  assert.ok(!JSON.stringify([result, lines]).includes('SECRET_SENTINEL'));
  assert.ok(!calls.some(([, args]) => args.includes('delete') || args[0] === 'issue'));
});

test('result reader reports merged, ended and open with timestamps from fake gh', () => {
  const w = world();
  w.issues[0].state = 'closed';
  w.issues[0].closed_at = '2026-11-10T10:03:00Z';
  w.prs.push({number: 8, url: `https://github.com/${repo}/pull/8`, mergedAt: '2026-11-10T10:02:00Z',
    closingIssuesReferences: [{number: 1, url: w.issues[0].html_url}]});
  w.comments.set(2, [[{body: '<!-- pdd:autopilot-core:end:2:run-a -->', created_at: '2026-11-10T10:04:00Z'}],
    [{body: '<!-- pdd:autopilot-core:end:2:run-b -->', created_at: '2026-11-10T10:05:00Z'}]]);
  const result = readSmokeResults({repo, fixture: w.fixture}, w.ports);
  assert.equal(result.repo, repo);
  assert.equal(result.checkedAt, iso('2026-11-10T10:10:00Z'));
  assert.deepEqual(result.issues, [
    {id: '01-doc', number: 1, title: w.issues[0].title, url: w.issues[0].html_url,
      state: 'merged', createdAt: iso(createdAt), finishedAt: iso('2026-11-10T10:02:00Z'), elapsedSeconds: 120},
    {id: '02-bug', number: 2, title: w.issues[1].title, url: w.issues[1].html_url,
      state: 'ended', createdAt: iso(createdAt), finishedAt: iso('2026-11-10T10:05:00Z'), elapsedSeconds: 300},
    {id: '03-feature', number: 3, title: w.issues[2].title, url: w.issues[2].html_url,
      state: 'open', createdAt: iso(createdAt), finishedAt: null, elapsedSeconds: 600}]);
});

test('closed without merge is ended, unrelated references and wrong issue end markers do not prove merge/end', () => {
  const w = world();
  w.issues[0].state = 'closed';
  w.issues[0].closed_at = '2026-11-10T10:01:00Z';
  w.prs.push({number: 9, mergedAt: createdAt, closingIssuesReferences: [{number: 1, url: 'https://github.com/other/repo/issues/1'}]});
  w.comments.set(2, [[{body: '<!-- pdd:autopilot-core:end:3:other -->', created_at: createdAt}]]);
  const result = readSmokeResults({repo, fixture: w.fixture}, w.ports);
  assert.deepEqual(result.issues.map(issue => issue.state), ['ended', 'open', 'open']);
  assert.equal(result.issues[0].elapsedSeconds, 60);
});

test('merged evidence wins over an old end marker but an open issue is not merged', () => {
  const w = world();
  w.issues[0].state = 'closed'; w.issues[0].closed_at = createdAt;
  w.comments.set(1, [[{body: '<!-- pdd:autopilot-core:end:1:old -->', created_at: createdAt}]]);
  for (const issue of w.issues.slice(0, 2)) {
    w.prs.push({number: issue.number + 10, mergedAt: '2026-11-10T10:06:00Z',
      closingIssuesReferences: [{url: issue.html_url}]});
  }
  assert.deepEqual(readSmokeResults({repo, fixture: w.fixture}, w.ports).issues.map(issue => issue.state),
    ['merged', 'open', 'open']);
});

test('reader refuses missing/duplicate smoke issues, invalid dates and failed or malformed gh', () => {
  let w = world(); w.issues.pop();
  assert.throws(() => readSmokeResults({repo, fixture: w.fixture}, w.ports), /missing|exactly one/i);
  w = world(); w.issues.push({...w.issues[0], number: 99});
  assert.throws(() => readSmokeResults({repo, fixture: w.fixture}, w.ports), /duplicate|exactly one/i);
  w = world(); w.issues[0].created_at = 'not a date';
  assert.throws(() => readSmokeResults({repo, fixture: w.fixture}, w.ports), /date|time/i);
  for (const reply of [{code: 1, stderr: 'SECRET_SENTINEL'}, {code: 0, stdout: 'not json'},
    {code: 0, stdout: '{}'}]) {
    assert.throws(() => readSmokeResults({repo}, {run: () => reply}), error => !error.message.includes('SECRET_SENTINEL'));
  }
});

test('check command emits times and cleanup instructions through read-only gh calls', () => {
  const w = world(), lines = [];
  const result = runSmoke(['--check', repo], {...w.ports, log: line => lines.push(line)});
  assert.equal(result.exitCode, 0, result.message);
  assert.match(lines.join('\n'), /#1 open.*created=.*finished=.*elapsed=600s/);
  assert.match(lines.join('\n'), /Delete manually: gh repo delete example\/smoke --yes/);
  assert.ok(w.calls.every(([, args]) => args[0] === 'pr' || (args[0] === 'api' && args.includes('GET'))));
});

test('result reader refuses truncated merged PR inventory', () => {
  const w = world();
  for (let i = 0; i < 1000; i++) w.prs.push({number: i + 1, mergedAt: createdAt, closingIssuesReferences: []});
  assert.throws(() => readSmokeResults({repo, fixture: w.fixture}, w.ports), /1000|saturat|truncat/i);
});

test('shell entrypoint works outside the checkout without gh for a default dry run', t => {
  const result = spawnSync(resolve('scripts/autopilot-smoke.sh'), ['--owner', 'example'],
    {cwd: scratch(t), encoding: 'utf8'});
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /Dry run/);
});

test('native apply uses real isolated Git and a fake gh executable despite inherited Git overrides', t => {
  const root = scratch(t), bin = join(root, 'bin'), transcript = join(root, 'gh-calls.jsonl');
  fs.mkdirSync(bin);
  fs.writeFileSync(join(bin, 'gh'), `#!/usr/bin/env node
const fs = require('node:fs');
const cp = require('node:child_process');
const args = process.argv.slice(2);
const row = {args};
if (args[0] === 'repo') {
  const source = args[args.indexOf('--source') + 1];
  row.branch = cp.execFileSync('git', ['-C', source, 'branch', '--show-current'], {encoding: 'utf8'}).trim();
  row.author = cp.execFileSync('git', ['-C', source, 'log', '-1', '--format=%an <%ae>'], {encoding: 'utf8'}).trim();
  row.hooks = cp.execFileSync('git', ['-C', source, 'config', 'core.hooksPath'], {encoding: 'utf8'}).trim();
}
fs.appendFileSync(${JSON.stringify(transcript)}, JSON.stringify(row) + '\\n');
if (args[0] === 'issue') {
  const repo = args[args.indexOf('--repo') + 1];
  console.log('https://github.com/' + repo + '/issues/' + fs.readFileSync(${JSON.stringify(transcript)}, 'utf8').trim().split('\\n').length);
}
`, {mode: 0o755});
  const redirected = join(root, 'must-not-exist');
  const result = spawnSync(resolve('scripts/autopilot-smoke.sh'), ['--owner', 'example', '--apply'],
    {cwd: root, encoding: 'utf8', env: {...process.env, PATH: `${bin}:${process.env.PATH}`,
      GIT_DIR: redirected, GIT_WORK_TREE: redirected, GIT_INDEX_FILE: redirected,
      GIT_AUTHOR_NAME: 'Inherited author', GIT_AUTHOR_EMAIL: 'inherited@example.invalid'}});
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.equal(fs.existsSync(redirected), false);
  const rows = fs.readFileSync(transcript, 'utf8').trim().split('\n').map(line => JSON.parse(line));
  assert.equal(rows.length, 5);
  assert.equal(rows[0].branch, 'main');
  assert.equal(rows[0].author, 'Smoke sandbox <smoke@example.invalid>');
  assert.equal(rows[0].hooks, '/dev/null');
});
