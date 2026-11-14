import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { runCheck } from '../src/runtime-seam.mjs';
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

test('hidden descendants never contribute to visible lint labels', t => {
  for (const content of ['Visible<tspan style="display:none">SECRET</tspan>', 'Vis<tspan visibility="hidden">SECRET</tspan>ible', 'Vis<tspan opacity="0"><tspan>SECRET</tspan></tspan>ible']) {
    assert.deepEqual(lintSvgLayouts(drawing(t, '![drawing](game.ui.svg)\nVisible', `<svg><text>${content}</text></svg>`)), [], content);
  }
});

test('local fragment paint resources accept CSS quotes while external resources warn', t => {
  for (const resource of ['url(#paint)', "url('#paint')", 'url(&quot;#paint&quot;)']) {
    const source = `<svg><defs><linearGradient id="paint"><stop stop-color="red"/></linearGradient></defs><rect fill="${resource}"/></svg>`;
    const setup = drawing(t, '![drawing](game.ui.svg)', source);
    assert.deepEqual(lintSvgLayouts(setup), [], resource);
    writeFileSync(join(setup.root, 'game.ui.svg'), source.replace('#paint', 'https://example.test/paint.svg#paint'));
    assert.match(lintSvgLayouts(setup)[0], /external SVG resources/);
  }
});

test('public local lint includes no-interface/no-test Git-visible prompts, no auth/network', async t => {
  const setup = harbor(t, repo => { mkdirSync(join(repo, 'views')); cpSync(join(fixtures, 'game.ui.svg'), join(repo, 'views/game.ui.svg')); writeFileSync(join(repo, 'views/game.prompt.md'), '![Layout](game.ui.svg)'); });
  const stdout = sink(), stderr = sink();
  const env = { HOME: setup.home, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: setup.state };
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: setup.repo, env, stdout, stderr }), 4, stderr.text);
  const result = JSON.parse(stdout.text);
  assert.equal(result.exit_code, 4);
  assert.ok(result.problems.some(problem => problem.code === 'interface-missing' && problem.path === 'views/game.prompt.md')); assert.ok(result.warnings.some(warning => warning.includes('views/game.prompt.md'))); assert.match(result.summary_line, /0 AI calls/);
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
  const p = portsFor({ PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: setup.state }, { gh: () => assert.fail('No auth'), fetch: () => assert.fail('No network') }).ports;
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
  for (const argv of [ ['test','--local'], ['test','--lint','--local','--details'], ['test','--drawing','a.ui.svg'], ['test','--screen','http://example.test'], ['test','--look'], ['test','--journeys','--look'], ['test','--screen','http://example.test','--look'], ['test','--drawing','a.ui.svg','--look'], ['test','--screen','http://example.test','--drawing','a.ui.svg','story'], ['test','--screen','http://example.test','--drawing','a.ui.svg','--lint'], ['test','--screen','http://example.test','--drawing','a.ui.svg','--look','story'], ['test','--screen','http://example.test','--drawing','a.ui.svg','--look','--lint'] ]) {
    const plan = parseArgv(argv), p = portsFor({ PDD_RUNTIME_URL: 'invalid' }, { gh: () => assert.fail('No auth'), fetch: () => assert.fail('No network'), screenBrowser: () => assert.fail('No browser') }).ports;
    assert.equal(await runCheck({ cwd, words: [...plan.operands], options: { ...plan.options } }, p), 2, JSON.stringify(argv));
    assert.equal(p.stdout.text, '');
  }
});

test('HTML screen with .ui.svg warns on missing stylesheet or missing CSS classes in local lint, hosted lint and pdd test', async t => {
  const ledgerSvg = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 420 220"><rect width="420" height="220" fill="#0f172a"/><g id="balance-card"><rect x="16" y="48" width="388" height="68" fill="#1e293b"/><text x="32" y="88" fill="#f8fafc">BALANCE</text></g><g id="add-expense"><rect x="16" y="132" width="160" height="44" fill="#0284c7"/><text x="36" y="160" fill="#ffffff">Add Expense</text></g></svg>';
  const draftInterface = name => `<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify({
    status: 'draft',
    prose_sha256: '',
    entries: [{
      operation: name,
      input_schema: { type: 'object', properties: {}, required: [], additionalProperties: false },
      result_schema: { type: 'object', properties: { html: { type: 'string' } }, required: ['html'], additionalProperties: false },
      errors: [],
    }],
    calls: [],
    resources: [],
    limits: { max_steps: 4, max_model_calls: 2 },
    conventions: [],
  }, null, 2)}\n\`\`\`\n</details>\n`;
  const baseProse = `# Ledger Screen\n\n## Appearance\n\n![Ledger](views/ledger__stacked.ui.svg)\n\nRender \`balance-card\` with BALANCE and Button "Add Expense" with id="add-expense".\n\n## Dependencies\n\nNone.\n\n${draftInterface('renderLedger')}`;
  const notesProse = `# Notes Screen\n\nRender notes HTML without any drawing.\n\n## Dependencies\n\nNone.\n\n${draftInterface('renderNotes')}`;
  const makeMap = stylesheets => JSON.stringify({
    schema_version: 'prompt-runtime.app-map.v1',
    name: 'Pocket Ledger',
    default_screen: 'ledger',
    stylesheets,
    screens: [
      { id: 'ledger', title: 'Ledger', source: 'operation', prompt_path: 'prompts/ledger_screen.prompt.md', operation: 'renderLedger', format: 'html', stylesheets: [] },
      { id: 'notes', title: 'Notes', source: 'operation', prompt_path: 'prompts/notes_screen.prompt.md', operation: 'renderNotes', format: 'html', stylesheets: [] },
      { id: 'menu', title: 'Menu', source: 'mockup', prompt_path: 'prompts/place_order.prompt.md', format: 'svg', svg_path: 'prompts/views/ledger__stacked.ui.svg', stylesheets: [] },
    ],
  }, null, 2);

  const setup = harbor(t, repo => {
    mkdirSync(join(repo, 'prompts/views'), { recursive: true });
    mkdirSync(join(repo, 'styles'), { recursive: true });
    writeFileSync(join(repo, 'prompts/views/ledger__stacked.ui.svg'), ledgerSvg);
    writeFileSync(join(repo, 'prompts/ledger_screen.prompt.md'), baseProse);
    writeFileSync(join(repo, 'prompts/notes_screen.prompt.md'), notesProse);
    writeFileSync(join(repo, 'app-map.json'), makeMap([]));
    const scenario = JSON.parse(readFileSync(join(repo, 'tests/place-order.json'), 'utf8'));
    writeFileSync(join(repo, 'tests/place-order.json'), JSON.stringify({ ...scenario, app_maps: ['app-map.json'], context: [...(scenario.context ?? []), 'prompts/ledger_screen.prompt.md', 'prompts/notes_screen.prompt.md'] }, null, 2));
  });
  const fillStdout = sink(), fillStderr = sink();
  assert.equal(await runPdd(['test', '--fill-hash'], { cwd: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state }, stdout: fillStdout, stderr: fillStderr }), 0, fillStderr.text || fillStdout.text);

  const expectedMissingSheet = 'Warning: SVG layout app-map.json -> prompts/ledger_screen.prompt.md: stylesheets: HTML screen "ledger" links prompts/views/ledger__stacked.ui.svg with no stylesheet in "stylesheets".';
  const localPorts = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: setup.state }, { gh: () => assert.fail('No auth'), fetch: () => assert.fail('No network') }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--local': true, '--json': true } }, localPorts), 0, localPorts.stderr.text);
  assert.deepEqual(JSON.parse(localPorts.stdout.text).warnings, [expectedMissingSheet]);

  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const lintPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--lint': true, '--json': true } }, lintPorts), 0, lintPorts.stderr.text);
  assert.deepEqual(JSON.parse(lintPorts.stdout.text).warnings, [expectedMissingSheet]);

  const testPorts = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }).ports;
  assert.equal(await runCheck({ cwd: setup.repo, options: { '--json': true } }, testPorts), 0, testPorts.stderr.text);
  assert.ok(JSON.parse(testPorts.stdout.text).warnings.includes(expectedMissingSheet), testPorts.stdout.text);

  writeFileSync(join(setup.repo, 'styles/pocket.css'), '.ledger-card { background-color: #1e293b; }\n.btn-primary { background-color: #0284c7; }\n');
  writeFileSync(join(setup.repo, 'app-map.json'), makeMap(['styles/pocket.css']));
  const missingClass = lintSvgLayouts({ root: setup.repo, files: ['app-map.json', 'styles/pocket.css', 'prompts/ledger_screen.prompt.md', 'prompts/notes_screen.prompt.md', 'prompts/place_order.prompt.md', 'prompts/views/ledger__stacked.ui.svg'] });
  assert.deepEqual(missingClass, [
    'Warning: SVG layout prompts/ledger_screen.prompt.md -> styles/pocket.css: stylesheet classes: HTML screen "ledger" links prompts/views/ledger__stacked.ui.svg and names no CSS class from its stylesheet (for example .btn-primary).',
  ]);

  const styledProse = baseProse.replace(
    'Render `balance-card` with BALANCE and Button "Add Expense" with id="add-expense".',
    'Render `balance-card` with `.ledger-card` and BALANCE, and Button "Add Expense" with id="add-expense", class="btn-primary" and type="button".',
  );
  writeFileSync(join(setup.repo, 'prompts/ledger_screen.prompt.md'), styledProse);
  const clean = lintSvgLayouts({ root: setup.repo, files: ['app-map.json', 'styles/pocket.css', 'prompts/ledger_screen.prompt.md', 'prompts/notes_screen.prompt.md', 'prompts/place_order.prompt.md', 'prompts/views/ledger__stacked.ui.svg'] });
  assert.deepEqual(clean, []);

  rmSync(join(setup.repo, 'styles/pocket.css'));
  const missingFile = lintSvgLayouts({ root: setup.repo, files: ['app-map.json', 'prompts/ledger_screen.prompt.md', 'prompts/views/ledger__stacked.ui.svg'] });
  assert.equal(missingFile.length, 1);
  assert.match(missingFile[0], /app-map\.json -> styles\/pocket\.css: stylesheet:/);
});

test('lint ignores valid comments without reconstructing markup and warns on malformed comments', t => {
  const prose = '![drawing](game.ui.svg)\nVisible\n<!-- Missing -->';
  assert.deepEqual(lintSvgLayouts(drawing(t, prose, '<svg><!-- <script>unsafe only as active markup</script> --><text>Visible</text></svg>')), []);
  assert.deepEqual(lintSvgLayouts(drawing(t, '<!-- ![ignored](missing.ui.svg) -->\n' + prose, '<svg><text>Visible</text></svg>')), []);
  const boundary = lintSvgLayouts(drawing(t, prose, '<svg><scr<!-- harmless -->ipt/></svg>'));
  assert.match(boundary[0], /malformed|unsafe/);
  for (const comment of ['<!--outer<!-- nested -->', '<!-- unterminated', '<!-- bad -- content -->', '<!-- trailing --->']) {
    const badDrawing = lintSvgLayouts(drawing(t, prose, `<svg>${comment}<text>Visible</text></svg>`));
    assert.equal(badDrawing.length, 1); assert.match(badDrawing[0], /drawing:.*comment|drawing:.*malformed/i);
    const badPrompt = lintSvgLayouts(drawing(t, `${prose}\n${comment}`, '<svg><text>Visible</text></svg>'));
    assert.equal(badPrompt.length, 1); assert.match(badPrompt[0], /source:.*comment/i);
  }
  const literal = lintSvgLayouts(drawing(t, '![drawing](game.ui.svg)\n<script>', '<svg><text><![CDATA[<script>]]></text></svg>'));
  assert.deepEqual(literal, []);
  const active = lintSvgLayouts(drawing(t, prose, '<svg><!-- harmless --><script>alert(1)</script></svg>'));
  assert.match(active[0], /unsafe/);
});

test('non-control status, explanation and negated quotes absent from SVG never warn as controls', t => {
  const prose = [
    '# Dialog',
    '',
    '## Appearance',
    '',
    '![Dialog](game.ui.svg)',
    '',
    'Alongside the "Confirm" button (`id="confirm"`), show status text "Changes stay local until confirmed."',
    'Without controls enabled, explain "Read-only preview. Editing is locked."',
    'No button triggers "Auto-publish" in this state.',
    '`instructions` says "Enter confirms. Escape closes." Also explain "Drafts expire after 24 hours."'
  ].join('\n');
  assert.deepEqual(lintSvgLayouts(drawing(t, prose, '<svg xmlns="http://www.w3.org/2000/svg"><g id="confirm"><text>Confirm</text></g></svg>')), []);
  assert.deepEqual(lintSvgLayouts(drawing(t, prose, '<svg xmlns="http://www.w3.org/2000/svg"></svg>')), [
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "Confirm": prompt control absent from drawing.',
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "confirm": prompt control absent from drawing.'
  ]);
});

test('apostrophes, fenced HTML controls, raw HTML containers and non-control prose attributes stay bounded', t => {
  const prose = [
    '# Editor',
    '',
    '![Editor](game.ui.svg)',
    '',
    "Keep the requester's 'Retry' button visible when the screen's banner doesn't clear.",
    'Render a button with class="chip primary", role="button", aria-busy=\'true\', data-testid="save-chip", and id="next-step" labeled "Next".',
    '<div id="card-shell" class="panel">',
    '```html',
    '<div id="inner-box" class="stack">',
    '  <button id="apply" value="apply-now">Apply &amp; close</button>',
    '  <input type="hidden" id="csrf" name="csrf" value="secret-token"/>',
    '  <input type="reset" id="clear-all" name="clear-name" value="Clear"/>',
    '  <textarea id="notes" name="notes-body" placeholder="Write notes">Sample draft</textarea>',
    '</div>',
    '```',
    '</div>'
  ].join('\n');
  const svg = '<svg xmlns="http://www.w3.org/2000/svg"><g id="card-shell"><g id="apply"><text>Apply &amp; close</text></g></g></svg>';
  assert.deepEqual(lintSvgLayouts(drawing(t, prose, svg)), [
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "Clear": prompt control absent from drawing.',
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "Next": prompt control absent from drawing.',
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "Retry": prompt control absent from drawing.',
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "apply-now": prompt control absent from drawing.',
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "clear-all": prompt control absent from drawing.',
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "clear-name": prompt control absent from drawing.',
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "next-step": prompt control absent from drawing.',
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "notes": prompt control absent from drawing.',
    'Warning: SVG layout game.prompt.md -> game.ui.svg: control "notes-body": prompt control absent from drawing.'
  ]);
});

test('multi-drawing prompts scope per-tab list items, subsections and interleaved images while keeping shared and gallery controls', t => {
  const root = temp(t);
  mkdirSync(join(root, 'prompts/phone'), { recursive: true });
  mkdirSync(join(root, 'views'), { recursive: true });

  const shell = '<g id="pocket-tabs"><g id="tab-now"><text>Now</text></g><g id="tab-agents"><text>Agents</text></g><g id="tab-workflows"><text>Workflows</text></g><g id="tab-machines"><text>Machines</text></g></g>';
  const svgs = {
    'views/phone-now__stacked.ui.svg': `<svg xmlns="http://www.w3.org/2000/svg">${shell}<g id="approve-gate"><text>Approve</text></g><g id="reply-agent"><text>Reply</text></g></svg>`,
    'views/phone-agents__stacked.ui.svg': `<svg xmlns="http://www.w3.org/2000/svg">${shell}<g id="new-agent"><text>+ New Agent</text></g></svg>`,
    'views/phone-workflows__stacked.ui.svg': `<svg xmlns="http://www.w3.org/2000/svg">${shell}<g id="start-run"><text>Start Run</text></g></svg>`,
    'views/phone-machines__stacked.ui.svg': `<svg xmlns="http://www.w3.org/2000/svg">${shell}<g id="pair-machine"><text>Connect</text></g><g id="pause-login"><text>Pause</text></g></svg>`,
  };
  for (const [rel, content] of Object.entries(svgs)) writeFileSync(join(root, rel), content);

  const phonePrompt = [
    '# Pocket phone',
    '',
    '## Appearance',
    '',
    'Every tab renders bottom bar `pocket-tabs` with buttons `tab-now`, `tab-agents`, `tab-workflows`, and `tab-machines` labeled "Now", "Agents", "Workflows", and "Machines".',
    '',
    '1. **`Now` tab (`tab === "now"`):** Provide button "Reply" (`id="reply-agent"`) and button "Approve" (`id="approve-gate"`).',
    '2. **`Agents` tab (`tab === "agents"`):** Provide button "+ New Agent" (`id="new-agent"`).',
    '3. **`Workflows` tab (`tab === "workflows"`):** Provide button "Start Run" (`id="start-run"`).',
    '4. **`Machines` tab (`tab === "machines"`):** Provide button "Connect" (`id="pair-machine"`) and button "Pause" (`id="pause-login"`).',
    '',
    '![Now](../../views/phone-now__stacked.ui.svg)',
    '',
    '![Agents](../../views/phone-agents__stacked.ui.svg)',
    '',
    '![Workflows](../../views/phone-workflows__stacked.ui.svg)',
    '',
    '![Machines](../../views/phone-machines__stacked.ui.svg)',
    '',
    '## Dependencies',
    '',
    '- [Now layout](../../views/phone-now__stacked.ui.svg): `#approve-gate` and `#reply-agent`.',
    '- [Agents layout](../../views/phone-agents__stacked.ui.svg): `#new-agent`.',
    '- [Workflows layout](../../views/phone-workflows__stacked.ui.svg): `#start-run`.',
    '- [Machines layout](../../views/phone-machines__stacked.ui.svg): `#pair-machine` and `#pause-login`.',
  ].join('\n');
  writeFileSync(join(root, 'prompts/phone/phone.prompt.md'), phonePrompt);
  const phoneFiles = ['prompts/phone/phone.prompt.md', ...Object.keys(svgs)];
  assert.deepEqual(lintSvgLayouts({ root, files: phoneFiles }), []);

  writeFileSync(join(root, 'views/phone-machines__stacked.ui.svg'), `<svg xmlns="http://www.w3.org/2000/svg">${shell}<g id="pause-login"><text>Pause</text></g></svg>`);
  writeFileSync(join(root, 'views/phone-now__stacked.ui.svg'), '<svg xmlns="http://www.w3.org/2000/svg"><g id="pocket-tabs"><g id="tab-now"><text>Now</text></g><g id="tab-agents"><text>Agents</text></g><g id="tab-workflows"><text>Workflows</text></g></g><g id="approve-gate"><text>Approve</text></g><g id="reply-agent"><text>Reply</text></g></svg>');
  assert.deepEqual(lintSvgLayouts({ root, files: phoneFiles }), [
    'Warning: SVG layout prompts/phone/phone.prompt.md -> views/phone-machines__stacked.ui.svg: control "Connect": prompt control absent from drawing.',
    'Warning: SVG layout prompts/phone/phone.prompt.md -> views/phone-machines__stacked.ui.svg: control "pair-machine": prompt control absent from drawing.',
    'Warning: SVG layout prompts/phone/phone.prompt.md -> views/phone-now__stacked.ui.svg: control "Machines": prompt control absent from drawing.',
    'Warning: SVG layout prompts/phone/phone.prompt.md -> views/phone-now__stacked.ui.svg: control "tab-machines": prompt control absent from drawing.',
  ]);

  const interleavedPrompt = [
    '# Cart',
    '',
    '## Appearance',
    '',
    'Header keeps button "Help" (`id="help-btn"`).',
    '',
    '![Empty](../../views/cart--empty__stacked.ui.svg)',
    '',
    'Show button "Browse" (`id="browse-btn"`).',
    '',
    '### Filled',
    '',
    '![Filled](../../views/cart--filled__stacked.ui.svg)',
    '',
    'Show button "Checkout" (`id="checkout-btn"`).',
  ].join('\n');
  writeFileSync(join(root, 'prompts/phone/cart.prompt.md'), interleavedPrompt);
  writeFileSync(join(root, 'views/cart--empty__stacked.ui.svg'), '<svg xmlns="http://www.w3.org/2000/svg"><g id="help-btn"><text>Help</text></g><g id="browse-btn"><text>Browse</text></g></svg>');
  writeFileSync(join(root, 'views/cart--filled__stacked.ui.svg'), '<svg xmlns="http://www.w3.org/2000/svg"><g id="help-btn"><text>Help</text></g><g id="checkout-btn"><text>Checkout</text></g></svg>');
  const cartFiles = ['prompts/phone/cart.prompt.md', 'views/cart--empty__stacked.ui.svg', 'views/cart--filled__stacked.ui.svg'];
  assert.deepEqual(lintSvgLayouts({ root, files: cartFiles }), []);

  const galleryPrompt = [
    '# Board',
    '',
    '## Appearance',
    '',
    '![Split](../../views/board__split-pane.ui.svg)',
    '',
    '![Stacked](../../views/board__stacked.ui.svg)',
    '',
    'Provide button "New game" (`id="new-game"`).',
    '',
    '- **Split-pane layout:** Provide button "Hide sidebar" (`id="hide-sidebar"`).',
  ].join('\n');
  writeFileSync(join(root, 'prompts/phone/board.prompt.md'), galleryPrompt);
  writeFileSync(join(root, 'views/board__split-pane.ui.svg'), '<svg xmlns="http://www.w3.org/2000/svg"><g id="new-game"><text>New game</text></g><g id="hide-sidebar"><text>Hide sidebar</text></g></svg>');
  writeFileSync(join(root, 'views/board__stacked.ui.svg'), '<svg xmlns="http://www.w3.org/2000/svg"></svg>');
  const boardFiles = ['prompts/phone/board.prompt.md', 'views/board__split-pane.ui.svg', 'views/board__stacked.ui.svg'];
  assert.deepEqual(lintSvgLayouts({ root, files: boardFiles }), [
    'Warning: SVG layout prompts/phone/board.prompt.md -> views/board__stacked.ui.svg: control "New game": prompt control absent from drawing.',
    'Warning: SVG layout prompts/phone/board.prompt.md -> views/board__stacked.ui.svg: control "new-game": prompt control absent from drawing.',
  ]);
  writeFileSync(join(root, 'prompts/phone/board.prompt.md'), galleryPrompt.replace(/\n/g, '\r\n'));
  assert.deepEqual(lintSvgLayouts({ root, files: boardFiles }), [
    'Warning: SVG layout prompts/phone/board.prompt.md -> views/board__stacked.ui.svg: control "New game": prompt control absent from drawing.',
    'Warning: SVG layout prompts/phone/board.prompt.md -> views/board__stacked.ui.svg: control "new-game": prompt control absent from drawing.',
  ]);

  const edgePrompt = [
    '# Cart',
    '',
    '## Appearance ##',
    '',
    '![][empty-svg]',
    '![Filled](./../../views/cart--filled__stacked.ui.svg)',
    '',
    '- **State actions:**',
    "  - **Shopper's empty state --** Render:",
    '    ```html',
    '    <button id="browse-btn">Browse</button>',
    '    ```',
    "  - **Shopper's filled state:** Render:",
    '    ```html',
    '    <button id="checkout-btn">Checkout</button>',
    '    ```',
    '',
    'Header keeps button "Help" (`id="help-btn"`).',
    '',
    '[empty-svg]: ../../views/cart--empty__stacked.ui.svg "Empty button"',
    '[filled-dup]: ../../views/cart--filled__stacked.ui.svg',
  ].join('\r\n');
  writeFileSync(join(root, 'prompts/phone/cart.prompt.md'), edgePrompt);
  assert.deepEqual(lintSvgLayouts({ root, files: cartFiles }), []);

  const singleDupPrompt = [
    '# Single',
    '',
    '![First](./../../views/cart--empty__stacked.ui.svg)',
    '',
    '### Filled',
    '',
    'Show button "Checkout" (`id="checkout-btn"`).',
    '',
    '- [Second](../../views/cart--empty__stacked.ui.svg)',
  ].join('\r\n');
  writeFileSync(join(root, 'prompts/phone/cart.prompt.md'), singleDupPrompt);
  assert.deepEqual(lintSvgLayouts({ root, files: ['prompts/phone/cart.prompt.md', 'views/cart--empty__stacked.ui.svg'] }), [
    'Warning: SVG layout prompts/phone/cart.prompt.md -> views/cart--empty__stacked.ui.svg: control "Checkout": prompt control absent from drawing.',
    'Warning: SVG layout prompts/phone/cart.prompt.md -> views/cart--empty__stacked.ui.svg: control "checkout-btn": prompt control absent from drawing.',
    'Warning: SVG layout prompts/phone/cart.prompt.md -> views/cart--empty__stacked.ui.svg: label "Browse": drawing label absent from prompt.',
    'Warning: SVG layout prompts/phone/cart.prompt.md -> views/cart--empty__stacked.ui.svg: label "Help": drawing label absent from prompt.',
    'Warning: SVG layout prompts/phone/cart.prompt.md -> views/cart--empty__stacked.ui.svg: region #browse-btn: drawing region layout unspecified in prompt.',
    'Warning: SVG layout prompts/phone/cart.prompt.md -> views/cart--empty__stacked.ui.svg: region #help-btn: drawing region layout unspecified in prompt.',
  ]);
});
