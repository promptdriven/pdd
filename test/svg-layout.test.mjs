import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { discoverTestAndAppMaps } from '../src/core/ui/app-map-lint.mjs';
import { workspace } from '../src/shared/workspace-policy.mjs';
import { format, proseSha256, runCheck } from '../src/runtime-seam.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { fakeRuntime, harbor, portsFor, sink, temp, PLACE } from './helpers/runtime-fake.mjs';

const fixtures = join(import.meta.dirname, 'fixtures/svg-layout');
function drawing(t, prose = readFileSync(join(fixtures, 'game.prompt.md'), 'utf8'), svg) {
  const root = temp(t); cpSync(fixtures, root, { recursive: true });
  writeFileSync(join(root, 'game.prompt.md'), prose);
  if (svg !== undefined) writeFileSync(join(root, 'game.ui.svg'), svg);
  return { root, files: ['game.prompt.md', 'game.ui.svg'] };
}

test('valid linked .ui.svg drawing passes cleanly without prose control/label/region false positives', t => {
  assert.deepEqual(lintSvgLayouts(drawing(t)), []);
  const prose = '# UI\n\n## Appearance\n\n![drawing](game.ui.svg)\n';
  const svg = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 200 100"><g id="score"><text>SCORE</text></g></svg>';
  assert.deepEqual(lintSvgLayouts(drawing(t, prose, svg)), []);
});

test('reference links deduplicate and prompt selection scopes cleanly', t => {
  const prose = '# Appearance\n\n![layout][start]\n[Same](game.ui.svg#screen)\n[start]: game.ui.svg\n[External](https://example.test/no.ui.svg)';
  const setup = drawing(t, prose, '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 0 100"></svg>');
  const once = lintSvgLayouts(setup);
  assert.equal(once.length, 1);
  assert.equal(new Set(once).size, once.length);
  assert.deepEqual(lintSvgLayouts({ ...setup, promptPaths: [] }), []);
  assert.deepEqual(lintSvgLayouts({ ...setup, files: ['game.prompt.md', 'game.prompt.md'] }), once);
});

test('missing, escaping, symlink, bad viewBox, and malformed/unsafe drawings produce warnings', t => {
  for (const svg of [
    '<svg><text>broken</svg>',
    '<svg><text>&unknown;</text></svg>',
    '<svg><script>alert(1)</script></svg>',
    '<svg viewBox="0 0 0 100"><text>zero</text></svg>',
    '<svg viewBox="0 0 3 55000000000"><text>extreme</text></svg>',
  ]) {
    const result = lintSvgLayouts(drawing(t, '![drawing](game.ui.svg)', svg));
    assert.equal(result.length, 1, svg);
    assert.match(result[0], /(?:drawing|viewBox):/);
  }
  const setup = drawing(t, '![drawing](game.ui.svg)');
  rmSync(join(setup.root, 'game.ui.svg'));
  assert.match(lintSvgLayouts(setup)[0], /game.ui.svg: drawing:/);
  symlinkSync(join(fixtures, 'game.ui.svg'), join(setup.root, 'game.ui.svg'));
  assert.match(lintSvgLayouts(setup)[0], /symlink/);
  writeFileSync(join(setup.root, 'game.prompt.md'), '![drawing](../escape.ui.svg)');
  assert.match(lintSvgLayouts(setup)[0], /escapes repository/);
});

test('SVG stylesheets with complex CSS selectors and shortcut reference links pass without false positives', t => {
  const setup = drawing(t, '![view]\n[view]: game.ui.svg\nVisible', '<svg viewBox="0 0 200 100"><style>.hidden { display:none } g .card > rect { fill: #fff }</style><text class="hidden">SECRET</text><text>Visible</text></svg>');
  assert.deepEqual(lintSvgLayouts(setup), []);
});

test('local fragment paint resources accept CSS quotes while external resources warn', t => {
  for (const resource of ['url(#paint)', "url('#paint')", 'url(&quot;#paint&quot;)']) {
    const source = `<svg viewBox="0 0 200 100"><defs><linearGradient id="paint"><stop stop-color="red"/></linearGradient></defs><rect fill="${resource}"/></svg>`;
    const setup = drawing(t, '![drawing](game.ui.svg)', source);
    assert.deepEqual(lintSvgLayouts(setup), [], resource);
    writeFileSync(join(setup.root, 'game.ui.svg'), source.replace('#paint', 'https://example.test/paint.svg#paint'));
    assert.match(lintSvgLayouts(setup)[0], /external SVG resources/);
  }
});

test('public local lint includes no-interface/no-test Git-visible prompts with zero interface-missing problems, no auth/network', async t => {
  const setup = harbor(t, repo => {
    mkdirSync(join(repo, 'views'));
    writeFileSync(join(repo, 'views/game.ui.svg'), '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 0 100"></svg>');
    writeFileSync(join(repo, 'views/game.prompt.md'), '![Layout](game.ui.svg)');
  });
  const stdout = sink(), stderr = sink();
  const env = { HOME: setup.home, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: setup.state };
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: setup.repo, env, stdout, stderr }), 0, stderr.text);
  const result = JSON.parse(stdout.text);
  assert.equal(result.exit_code, 0);
  assert.deepEqual(result.problems, []);
  assert.ok(result.warnings.some(warning => warning.includes('views/game.prompt.md') && warning.includes('viewBox')));
  assert.match(result.summary_line, /0 AI calls/);
  const p = portsFor(env, { gh: () => assert.fail('No auth'), fetch: () => assert.fail('No network') }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, words: ['no-such-story'], options: { '--lint': true, '--local': true } }, p), 2);
  assert.match(p.stderr.text, /Unknown story/);
});

test('Story local lint follows selected dependency closure and omits unrelated prompts', async t => {
  const setup = harbor(t, repo => {
    writeFileSync(join(repo, 'prompts/game.ui.svg'), '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 -10 100"></svg>');
    const updated = `${readFileSync(join(repo, PLACE), 'utf8')}\n![Layout](game.ui.svg)`;
    writeFileSync(join(repo, PLACE), format.setInterfaceStatus(updated, { status: 'approved', prose_sha256: proseSha256(updated) }));
    writeFileSync(join(repo, 'prompts/unrelated.prompt.md'), '![Layout](missing.ui.svg)');
  });
  const p = portsFor({ PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: setup.state }, { gh: () => assert.fail('No auth'), fetch: () => assert.fail('No network') }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--lint': true, '--local': true, '--json': true } }, p), 0, p.stderr.text);
  const result = JSON.parse(p.stdout.text);
  assert.ok(result.warnings.some(warning => warning.includes(PLACE)));
  assert.ok(!result.warnings.some(warning => warning.includes('unrelated')));
});

test('hosted lint merges advisory warnings before authentication and preserves one complete-lint request', async t => {
  const setup = harbor(t, repo => {
    writeFileSync(join(repo, 'prompts/game.ui.svg'), '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 0 100"></svg>');
    writeFileSync(join(repo, PLACE), `${readFileSync(join(repo, PLACE), 'utf8')}\n![Layout](game.ui.svg)`);
  });
  const fake = await fakeRuntime(t, (entry, f) => ({ status: 200, json: f.lint(entry.request.requestId) }));
  const p = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }).ports;
  const auth = p.gh; p.gh = args => { if (args[0] === 'auth') assert.match(p.stderr.text, /Warning: SVG layout/); return auth(args); };
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true } }, p), 0, p.stderr.text);
  assert.equal(fake.posts.length, 1); assert.equal(fake.posts[0].command, 'lint'); assert.equal(fake.posts[0].request.complete, true);
  const jsonPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, jsonPorts), 0);
  assert.ok(JSON.parse(jsonPorts.stdout.text).warnings.some(warning => warning.includes('viewBox')));
});

test('CLI rejects local/screen combinations before auth, browser and runtime effects', async t => {
  const cwd = temp(t);
  for (const argv of [ ['test','--local'], ['test','--lint','--local','--details'], ['test','--drawing','a.ui.svg'], ['test','--screen','http://example.test'], ['test','--look'], ['test','--journeys','--look'], ['test','--screen','http://example.test','--look'], ['test','--drawing','a.ui.svg','--look'], ['test','--screen','http://example.test','--drawing','a.ui.svg','story'], ['test','--screen','http://example.test','--drawing','a.ui.svg','--lint'], ['test','--screen','http://example.test','--drawing','a.ui.svg','--look','story'], ['test','--screen','http://example.test','--drawing','a.ui.svg','--look','--lint'] ]) {
    const plan = parseArgv(argv), p = portsFor({ PDD_RUNTIME_URL: 'invalid' }, { gh: () => assert.fail('No auth'), fetch: () => assert.fail('No network'), screenBrowser: () => assert.fail('No browser') }).ports;
    assert.equal(await runCheck({ cwd, words: [...plan.operands], options: { ...plan.options } }, p), 2, JSON.stringify(argv));
    assert.equal(p.stdout.text, '');
  }
});

test('app-map stylesheet file existence check catches missing stylesheet files cleanly', t => {
  const ledgerSvg = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 420 220"><rect width="420" height="220" fill="#0f172a"/></svg>';
  const setup = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/views'), { recursive: true });
    mkdirSync(join(repo, 'styles'), { recursive: true });
    writeFileSync(join(repo, 'prompts/views/ledger__stacked.ui.svg'), ledgerSvg);
    writeFileSync(join(repo, 'prompts/ledger_screen.prompt.md'), '# Ledger\n\n![Ledger](views/ledger__stacked.ui.svg)\n\n## Dependencies\n\nNone.\n');
    writeFileSync(join(repo, 'styles/pocket.css'), '.ledger-card { background-color: #1e293b; }\n');
    writeFileSync(join(repo, 'app-map.json'), JSON.stringify({
      schema_version: 'prompt-runtime.app-map.v1',
      name: 'Pocket Ledger',
      default_screen: 'ledger',
      stylesheets: ['styles/pocket.css'],
      screens: [
        { id: 'ledger', title: 'Ledger', source: 'operation', prompt_path: 'prompts/ledger_screen.prompt.md', operation: 'renderLedger', format: 'html', stylesheets: [] },
      ],
    }, null, 2));
  });
  const files = ['app-map.json', 'styles/pocket.css', 'prompts/ledger_screen.prompt.md', 'prompts/views/ledger__stacked.ui.svg'];
  assert.deepEqual(lintSvgLayouts({ root: setup.repo, files }), []);

  rmSync(join(setup.repo, 'styles/pocket.css'));
  const missingFile = lintSvgLayouts({ root: setup.repo, files: files.filter(f => f !== 'styles/pocket.css') });
  assert.equal(missingFile.length, 1);
  assert.match(missingFile[0], /app-map\.json -> styles\/pocket\.css: stylesheet:/);
});

test('lint ignores valid comments without reconstructing markup and warns on malformed comments', t => {
  const prose = '![drawing](game.ui.svg)\nVisible\n<!-- Missing -->';
  assert.deepEqual(lintSvgLayouts(drawing(t, prose, '<svg viewBox="0 0 100 50"><!-- <script>unsafe only as active markup</script> --><text>Visible</text></svg>')), []);
  assert.deepEqual(lintSvgLayouts(drawing(t, '<!-- ![ignored](missing.ui.svg) -->\n' + prose, '<svg viewBox="0 0 100 50"><text>Visible</text></svg>')), []);
  const boundary = lintSvgLayouts(drawing(t, prose, '<svg><scr<!-- harmless -->ipt/></svg>'));
  assert.match(boundary[0], /malformed|unsafe/);
  for (const comment of ['<!--outer<!-- nested -->', '<!-- unterminated', '<!-- bad -- content -->', '<!-- trailing --->']) {
    const badDrawing = lintSvgLayouts(drawing(t, prose, `<svg>${comment}<text>Visible</text></svg>`));
    assert.equal(badDrawing.length, 1); assert.match(badDrawing[0], /drawing:.*comment|drawing:.*malformed/i);
    const badPrompt = lintSvgLayouts(drawing(t, `${prose}\n${comment}`, '<svg viewBox="0 0 100 50"><text>Visible</text></svg>'));
    assert.equal(badPrompt.length, 1); assert.match(badPrompt[0], /source:.*comment/i);
  }
  const literal = lintSvgLayouts(drawing(t, '![drawing](game.ui.svg)\n<script>', '<svg viewBox="0 0 100 50"><text><![CDATA[<script>]]></text></svg>'));
  assert.deepEqual(literal, []);
  const active = lintSvgLayouts(drawing(t, prose, '<svg><!-- harmless --><script>alert(1)</script></svg>'));
  assert.match(active[0], /unsafe/);
});

test('discoverTestAndAppMaps finds default app-map.json and scenario-declared app_maps respecting workspace policy', t => {
  const root = temp(t);
  mkdirSync(join(root, 'tests'), { recursive: true });
  mkdirSync(join(root, 'custom'), { recursive: true });
  writeFileSync(join(root, 'app-map.json'), '{}');
  writeFileSync(join(root, 'custom/map.json'), '{}');
  writeFileSync(join(root, 'tests/s.json'), JSON.stringify({ app_maps: ['custom/map.json'] }));
  const { testJsonPaths, mapPaths } = discoverTestAndAppMaps({
    root,
    files: ['app-map.json', 'tests/s.json', 'custom/map.json'],
    policy: workspace.policy({ root }),
    safeRead: (r, rel) => readFileSync(join(r, rel), 'utf8'),
  });
  assert.deepEqual(testJsonPaths, ['tests/s.json']);
  assert.deepEqual([...mapPaths].sort(), ['app-map.json', 'custom/map.json']);
});
