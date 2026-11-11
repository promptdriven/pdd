import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, rmSync, writeFileSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const bin = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
const version = JSON.parse(readFileSync(new URL('../package.json', import.meta.url))).version;
const notice = `pdd 999.0.0 is available (installed ${version}). Update: npm install -g github:promptdriven/pdd#alpha-v999.0.0\n`;
const indicators = ['CI', 'GITHUB_ACTIONS', 'GITLAB_CI', 'CIRCLECI', 'TRAVIS', 'BUILDKITE', 'TF_BUILD', 'JENKINS_URL', 'PDD_PATH_PROBE'];
function fixture(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-release-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const preload = join(dir, 'transport.mjs'), request = join(dir, 'request.json'), aborted = join(dir, 'aborted');
  writeFileSync(preload, `import {writeFileSync} from 'node:fs';
globalThis.fetch = async (url, options) => {
  writeFileSync(${JSON.stringify(request)}, JSON.stringify({url, options}));
  const mode = process.env.PDD_TEST_MODE;
  options.signal.addEventListener('abort', () => writeFileSync(${JSON.stringify(aborted)}, 'aborted'));
  if (mode === 'reject') throw Error('offline secret');
  if (mode === 'hang') return new Promise(() => {});
  if (mode === 'body-hang') return new Response(new ReadableStream({start() {}}));
  if (mode === 'oversize' || mode === 'at-limit') {
    const json = JSON.stringify({tag_name:'alpha-v999.0.0',draft:false,prerelease:false});
    return new Response(json.padEnd(mode === 'oversize' ? 65537 : 65536, ' '));
  }
  if (mode === 'bad-json') return new Response('not json');
  if (mode === 'http') return new Response('{}', {status:429});
  return new Response(process.env.PDD_TEST_RELEASE || JSON.stringify({tag_name:'alpha-v999.0.0',draft:false,prerelease:false}));
};\n`);
  const env = { ...process.env, HOME: join(dir, 'home'), PATH: '', CLAUDE_CONFIG_DIR: '' };
  for (const key of indicators) delete env[key];
  const run = (args = ['--version'], extra = {}) => spawnSync(process.execPath, ['--import', preload, bin, ...args], {cwd:dir,env:{...env,...extra},encoding:'utf8',timeout:8000});
  return {run, request, aborted};
}

test('next executable command prints the exact pinned GitHub update command on stderr', t => {
  const {run, request} = fixture(t);
  const result = run();
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout, `${version}\n`);
  assert.equal(result.stderr, notice);
  const call = JSON.parse(readFileSync(request));
  assert.equal(call.url, 'https://api.github.com/repos/promptdriven/pdd/releases/latest');
  assert.equal(call.options.redirect, 'error');
  assert.equal(call.options.credentials, 'omit');
  assert.equal(call.options.headers.Authorization, undefined);
});

test('workflow list keeps its stdout and exit status while reporting a release', t => {
  const {run} = fixture(t);
  const normal = run(['workflow','list'], {CI:'1'}), checked = run(['workflow','list']);
  assert.equal(checked.status, normal.status);
  assert.equal(checked.stdout, normal.stdout);
  assert.equal(checked.stderr, normal.stderr + notice);
});

test('bad command keeps its failure exit status and diagnostic', t => {
  const {run} = fixture(t);
  const normal = run(['does-not-exist'], {CI:'1'}), checked = run(['does-not-exist']);
  assert.equal(checked.status, 2);
  assert.equal(checked.stdout, normal.stdout);
  assert.equal(checked.stderr, notice + normal.stderr);
});

for (const indicator of indicators) test(`${indicator} skips lookup and notice`, t => {
  const {run, request} = fixture(t);
  const result = run(['--version'], {[indicator]:'1'});
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout, `${version}\n`);
  assert.equal(result.stderr, '');
  assert.equal(existsSync(request), false);
});

for (const mode of ['reject','hang','body-hang','oversize','bad-json','http']) test(`${mode} lookup cannot block the command or leak a diagnostic`, t => {
  const {run, request, aborted} = fixture(t);
  const started = performance.now();
  const result = run(['--version'], {PDD_TEST_MODE:mode});
  assert.ok(performance.now() - started < 3000, 'lookup must finish near its one-second deadline');
  if (['hang','body-hang','oversize'].includes(mode)) assert.ok(existsSync(aborted), 'transport was aborted');
  assert.equal(result.error, undefined);
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout, `${version}\n`);
  assert.equal(result.stderr, '');
  assert.ok(existsSync(request));
});

for (const release of [
  {tag_name:'alpha-v0.0.0',draft:false,prerelease:false},
  {tag_name:`alpha-v${version}`,draft:false,prerelease:false},
  {tag_name:'alpha-v999.0.0',draft:true,prerelease:false},
  {tag_name:'alpha-v999.0.0',draft:false,prerelease:true},
  {tag_name:'alpha-v999.0.0; touch /tmp/pwned',draft:false,prerelease:false},
  {tag_name:'alpha-v999.0.0\nmalicious',draft:false,prerelease:false},
  {tag_name:'v999.0.0'}, null,
]) test(`unusable release ${JSON.stringify(release)} stays silent`, t => {
  const {run} = fixture(t);
  const result = run(['--version'], {PDD_TEST_RELEASE:JSON.stringify(release)});
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stdout, `${version}\n`);
  assert.equal(result.stderr, '');
});

test('native test isolation marks subprocesses as CI for offline release checking', () => {
  assert.equal(process.env.GITHUB_ACTIONS, '1');
});

test('a valid JSON response at the exact byte limit can produce a reminder', t => {
  const {run} = fixture(t);
  const result = run(['--version'], {PDD_TEST_MODE:'at-limit'});
  assert.equal(result.status, 0);
  assert.equal(result.stdout, `${version}\n`);
  assert.equal(result.stderr, notice);
});
