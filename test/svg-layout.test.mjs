import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { fakeRuntime, harbor, portsFor, sink, temp, PLACE } from './runtime-fake.mjs';

const fixtures = join(import.meta.dirname, 'fixtures/svg-layout');
function drawing(t, prose = readFileSync(join(fixtures, 'game.prompt.md'), 'utf8'), svg) {
  const root = temp(t); cpSync(fixtures, root, { recursive: true });
  writeFileSync(join(root, 'game.prompt.md'), prose);
  if (svg !== undefined) writeFileSync(join(root, 'game.ui.svg'), svg);
  return { root, files: ['game.prompt.md', 'game.ui.svg'] };
}

test('2048-like data prose does not specify score/seed boxes, READY or absent directions', t => {
  const result = lintSvgLayouts(drawing(t));
  for (const part of ['move-left', 'move-right', 'move-up', 'move-down', 'label "READY"', 'region #score', 'region #seed']) assert.ok(result.some(warning => warning.includes(part)), part);
  assert.ok(result.every(warning => warning.startsWith('Warning: SVG layout game.prompt.md -> game.ui.svg:')));
  assert.ok(!result.some(warning => /label "(?:SCORE|SEED)"|HIDDEN|CONTEXT|Metadata/.test(warning)));
});

test('explicit layout declarations match decoded whole labels, ids and named controls', t => {
  const prose = '# UI\n\n## Appearance\n\nregion score, seed box, status bar, `go`. SCORE SEED READY. Button "Go & win" with id="go".\n![drawing](game.ui.svg)';
  const svg = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 200 100"><g id="score"><text>SCORE</text></g><g id="seed"><text>SEED</text></g><g id="status"><text>READY</text></g><g id="go"><text>Go &amp; win</text></g></svg>';
  assert.deepEqual(lintSvgLayouts(drawing(t, prose, svg)), []);
  const incomplete = lintSvgLayouts(drawing(t, prose.replace('READY', 'ALREADY'), svg));
  assert.ok(incomplete.some(warning => warning.includes('label "READY"')));
});

test('reference links deduplicate, prompt selection scopes, metadata/hidden/context stay excluded', t => {
  const prose = '# Appearance\n\n![layout][start]\n[Same](game.ui.svg#screen)\n[start]: game.ui.svg\n[External](https://example.test/no.ui.svg)';
  const setup = drawing(t, prose);
  const once = lintSvgLayouts(setup);
  assert.equal(new Set(once).size, once.length);
  assert.deepEqual(lintSvgLayouts({ ...setup, promptPaths: [] }), []);
  assert.deepEqual(lintSvgLayouts({ ...setup, files: ['game.prompt.md', 'game.prompt.md'] }), once);
});

test('missing, escaping, symlink and malformed/unsafe drawings produce warnings', t => {
  for (const svg of ['<svg><text>broken</svg>', '<svg><text>&unknown;</text></svg>', '<svg><script>alert(1)</script></svg>']) {
    const result = lintSvgLayouts(drawing(t, '![drawing](game.ui.svg)', svg));
    assert.equal(result.length, 1); assert.match(result[0], /drawing:/);
  }
  const setup = drawing(t, '![drawing](game.ui.svg)');
  rmSync(join(setup.root, 'game.ui.svg'));
  assert.match(lintSvgLayouts(setup)[0], /game.ui.svg: drawing:/);
  symlinkSync(join(fixtures, 'game.ui.svg'), join(setup.root, 'game.ui.svg'));
  assert.match(lintSvgLayouts(setup)[0], /symlink/);
  writeFileSync(join(setup.root, 'game.prompt.md'), '![drawing](../escape.ui.svg)');
  assert.match(lintSvgLayouts(setup)[0], /escapes repository/);
});

test('static CSS hiding and shortcut reference links do not require hidden labels', t => {
  const setup = drawing(t, '![view]\n[view]: game.ui.svg\nVisible', '<svg><style>.hidden { display:none }</style><text class="hidden">SECRET</text><text>Visible</text></svg>');
  assert.deepEqual(lintSvgLayouts(setup), []);
  writeFileSync(join(setup.root, 'game.ui.svg'), '<svg><style>g .hidden { display:none }</style><text>Visible</text></svg>');
  assert.match(lintSvgLayouts(setup)[0], /unsupported SVG stylesheet selector/);
});

test('public local lint includes no-interface/no-test Git-visible prompts, no auth/network/state', async t => {
  const setup = harbor(t, repo => { mkdirSync(join(repo, 'views')); cpSync(join(fixtures, 'game.ui.svg'), join(repo, 'views/game.ui.svg')); writeFileSync(join(repo, 'views/game.prompt.md'), '![Layout](game.ui.svg)'); });
  const stdout = sink(), stderr = sink();
  const env = { HOME: setup.home, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: setup.repo };
  assert.equal(await runPdd(['check', '--lint', '--local', '--json'], { cwd: setup.repo, env, stdout, stderr }), 0, stderr.text);
  const result = JSON.parse(stdout.text);
  assert.equal(result.exit_code, 0); assert.ok(result.warnings.some(warning => warning.includes('views/game.prompt.md'))); assert.match(result.summary_line, /0 AI calls/);
  const p = portsFor(env, { gh: () => assert.fail('No auth'), fetch: () => assert.fail('No network') }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, words: ['no-such-story'], options: { '--lint': true, '--local': true } }, p), 2);
  assert.match(p.stderr.text, /Unknown story/);
});

test('Story local lint follows selected dependency closure and omits unrelated prompts', async t => {
  const setup = harbor(t, repo => {
    cpSync(join(fixtures, 'game.ui.svg'), join(repo, 'prompts/game.ui.svg'));
    const original = readFileSync(join(repo, PLACE), 'utf8');
    writeFileSync(join(repo, PLACE), `${original}\n![Layout](game.ui.svg)`);
    writeFileSync(join(repo, 'prompts/unrelated.prompt.md'), '![Layout](missing.ui.svg)');
  });
  const p = portsFor({ PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: setup.repo }, { gh: () => assert.fail('No auth'), fetch: () => assert.fail('No network') }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--local': true, '--json': true } }, p), 0, p.stderr.text);
  const result = JSON.parse(p.stdout.text);
  assert.ok(result.warnings.some(warning => warning.includes(PLACE)));
  assert.ok(!result.warnings.some(warning => warning.includes('unrelated')));
});

test('hosted lint merges advisory warnings before authentication and preserves one complete-lint request', async t => {
  const setup = harbor(t, repo => {
    cpSync(join(fixtures, 'game.ui.svg'), join(repo, 'prompts/game.ui.svg'));
    writeFileSync(join(repo, PLACE), `${readFileSync(join(repo, PLACE), 'utf8')}\n![Layout](game.ui.svg)`);
  });
  const fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.lint(entry.request.requestId) }));
  const p = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }).ports;
  const auth = p.gh; p.gh = args => { if (args[0] === 'auth') assert.match(p.stderr.text, /Warning: SVG layout/); return auth(args); };
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true } }, p), 0, p.stderr.text);
  assert.equal(fake.posts.length, 1); assert.equal(fake.posts[0].command, 'lint'); assert.equal(fake.posts[0].request.complete, true);
  const jsonPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, jsonPorts), 0);
  assert.ok(JSON.parse(jsonPorts.stdout.text).warnings.some(warning => warning.includes('region #score')));
});

test('CLI rejects local/screen combinations before auth, browser and runtime effects', async t => {
  const cwd = temp(t);
  for (const argv of [ ['check','--local'], ['check','--lint','--local','--details'], ['check','--drawing','a.ui.svg'], ['check','--screen','http://example.test'], ['check','--screen','http://example.test','--drawing','a.ui.svg','story'], ['check','--screen','http://example.test','--drawing','a.ui.svg','--lint'] ]) {
    const plan = parseArgv(argv), p = portsFor({ PDD_RUNTIME_URL: 'invalid' }, { gh: () => assert.fail('No auth'), fetch: () => assert.fail('No network'), screenBrowser: () => assert.fail('No browser') }).ports;
    assert.equal(await runCheck({ cwd, words: [...plan.operands], options: { ...plan.options } }, p), 2, JSON.stringify(argv));
    assert.equal(p.stdout.text, '');
  }
});
