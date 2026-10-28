import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { accessSync, constants, copyFileSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { compareScreen, formatScreenComparison } from '../src/screen-compare.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { sink, temp } from './runtime-fake.mjs';

const fixture = join(import.meta.dirname, 'fixtures/svg-layout/game.ui.svg');
const svg = readFileSync(fixture, 'utf8');
const chrome = [process.env.PDD_CHROME_PATH, '/usr/bin/google-chrome', '/usr/bin/chromium', '/usr/bin/chromium-browser', '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome'].find(path => { try { if (path) { accessSync(path, constants.X_OK); return true; } } catch { /* unavailable */ } return false; });
const point = (kind, value, node, x, y, extra = {}) => ({ kind, value, node, box: { x, y, width: 10, height: 10 }, visible: true, ancestors: [], region: null, ...extra });
function setup(t, source = svg) { const cwd = temp(t); writeFileSync(join(cwd, 'screen.ui.svg'), source); return { cwd, drawingPath: 'screen.ui.svg', url: 'http://example.test/' }; }

test('parts compare consumes repeated text, enforces ids/content, visibility, region, order and exact case', async t => {
  const input = setup(t);
  const reference = [point('id', 'score', 1, 20, 20), point('text', 'SCORE', 2, 20, 20, { region: 'score', ancestors: [1] }), point('text', '2', 3, 20, 100), point('text', '2', 4, 70, 100), point('text', 'READY', 5, 20, 200)];
  const compare = actual => compareScreen(input, { browser: async () => ({ viewport: { width: 400, height: 400 }, reference, actual }) });
  assert.equal((await compare(structuredClone(reference))).passed, true);
  const missing = await compare(reference.slice(0, 3));
  assert.equal(missing.rows[3].status, 'missing'); assert.equal(missing.rows[4].status, 'missing');
  const hidden = structuredClone(reference); hidden[0].visible = false; hidden[4].visible = false;
  assert.equal((await compare(hidden)).rows[4].status, 'hidden');
  const moved = structuredClone(reference); moved[0].box.x += 61;
  assert.equal((await compare(moved)).rows[0].status, 'region');
  const swapped = structuredClone(reference); swapped[2].box.x = 70; swapped[3].box.x = 20;
  // Identical labels can map to nearest identical occurrences; use named ids to
  // demonstrate a true inversion that remains within the region tolerance.
  const orderedRef = [point('id', 'a', 1, 20, 100), point('id', 'b', 2, 50, 100)];
  const orderedActual = [point('id', 'a', 3, 50, 100), point('id', 'b', 4, 20, 100)];
  const order = await compareScreen(input, { browser: async () => ({ viewport: { width: 400, height: 400 }, reference: orderedRef, actual: orderedActual }) });
  assert.ok(order.rows.every(row => row.status === 'order'));
  const differentContent = reference.filter(part => part.kind === 'id');
  assert.equal((await compare(differentContent)).rows[1].status, 'missing');
  const lowerCase = structuredClone(reference); lowerCase[1].value = 'score';
  assert.equal((await compare(lowerCase)).rows[1].status, 'missing');
  const duplicate = [...reference, point('id', 'score', 100, 20, 20)];
  assert.match((await compare(duplicate)).rows[0].actual, /duplicate/);
});

test('labels prefer their matched enclosing region and Markdown escapes untrusted content', async t => {
  const input = setup(t), reference = [point('id', 'box', 1, 20, 20), point('text', '2', 2, 20, 20, { region: 'box', ancestors: [1] })];
  const actual = [point('id', 'box', 10, 20, 20), point('text', '2', 11, 20, 20), point('text', '2', 12, 100, 20, { ancestors: [10] })];
  const report = await compareScreen(input, { browser: async () => ({ viewport: { width: 400, height: 400 }, reference, actual }) });
  assert.equal(report.rows[1].status, 'region', 'outside label cannot satisfy the owned region');
  report.rows[0].part = 'a|b\nrow';
  assert.match(formatScreenComparison(report), /a\\\|b row/);
  assert.match(formatScreenComparison(report), /Screen vs drawing: FAIL/);
});

test('bad input is rejected without browser work; execution failure never returns a passing report', async t => {
  const input = setup(t), never = { browser: () => assert.fail('invalid input must not launch') };
  for (const url of ['file:///tmp/page', 'http://user:password@example.test/', 'not a URL']) await assert.rejects(compareScreen({ ...input, url }, never), error => error.exitCode === 2);
  for (const drawingPath of ['missing.ui.svg', 'image.svg']) await assert.rejects(compareScreen({ ...input, drawingPath }, never), error => error.exitCode === 2);
  const unsafe = setup(t, '<svg xmlns="http://www.w3.org/2000/svg"><script>alert(1)</script></svg>');
  await assert.rejects(compareScreen(unsafe, never), /unsafe/);
  await assert.rejects(compareScreen(input, { browser: async () => ({ viewport: { width: 400, height: 400 }, reference: [], actual: [] }) }), /no valid reference/);
  const stdout = sink(), stderr = sink();
  assert.equal(await runCheck({ cwd: input.cwd, options: { '--screen': input.url, '--drawing': input.drawingPath, '--json': true } }, { env: { PDD_CHROME_PATH: '/no-installed-chrome' }, stdout, stderr, gh: () => assert.fail('No auth'), fetch: () => assert.fail('No runtime') }), 5);
  assert.equal(stdout.text, ''); assert.match(stderr.text, /PDD_CHROME_PATH/);
});

test('installed browser renders reference transforms/entities/repeated numbers and rejects real screen differences', { skip: !chrome, timeout: 120000 }, async t => {
  const input = setup(t), profileEnv = { ...process.env, PDD_CHROME_PATH: chrome };
  let page = `<!doctype html><style>body{margin:0}</style>${svg}`, status = 200;
  const server = createServer((_, res) => { res.writeHead(status, { 'content-type': 'text/html' }); res.end(page); });
  await new Promise(done => server.listen(0, '127.0.0.1', done)); t.after(() => new Promise(done => { server.closeAllConnections(); server.close(done); }));
  input.url = `http://127.0.0.1:${server.address().port}/`;
  const compare = () => compareScreen({ ...input, chromePath: chrome }, { env: profileEnv });
  const pass = await compare(); assert.equal(pass.passed, true, JSON.stringify(pass.rows));
  assert.deepEqual(pass.viewport, { width: 400, height: 400 });
  assert.equal(pass.rows.filter(row => row.part === '“2”').length, 2);
  assert.equal(pass.rows.find(row => row.part === '#seed').expected, 'visible at (80, 133)');
  assert.ok(!pass.rows.some(row => /HIDDEN|CONTEXT|#title|surroundings/.test(row.part)));
  await t.test('ordinary HTML/form controls satisfy the visible SVG parts', async () => {
    page = '<!doctype html><style>body{margin:0}section,span,input{position:absolute}section{width:120px;height:65px}input{width:50px;height:20px;border:0;padding:0}span{font:16px serif}#score{left:250px;top:20px}#seed{left:20px;top:100px}#status{left:20px;top:280px;width:350px;height:45px}</style><section id="score"><span style="left:10px;top:8px">SCORE</span><input style="left:10px;top:30px" value="0"></section><section id="seed"><span style="left:10px;top:8px">SEED</span><input style="left:10px;top:30px" value="42"></section><span style="left:40px;top:205px">2</span><span style="left:120px;top:205px">2</span><section id="status"><span style="left:10px;top:13px">READY</span></section>';
    const report = await compare(); assert.equal(report.passed, true, JSON.stringify(report.rows));
  });
  await t.test('score/seed ids and READY remain required despite unrelated data words', async () => {
    page = '<!doctype html><p>score 0 seed 42</p>';
    const report = await compare(); assert.equal(report.passed, false);
    for (const part of ['#score', '#seed', '“READY”']) assert.equal(report.rows.find(row => row.part === part).status, 'missing');
  });
  await t.test('hidden/offscreen ids/text and repeated occurrences cannot pass', async () => {
    page = `<!doctype html><style>body{margin:0}#score{display:none}#seed{transform:translateX(900px)}</style>${svg.replace('<text x="120" y="220">2</text>', '')}`;
    const report = await compare(); assert.equal(report.rows.find(row => row.part === '#score').status, 'hidden'); assert.equal(report.rows.find(row => row.part === '#seed').status, 'hidden');
    assert.equal(report.rows.filter(row => row.part === '“2”' && row.status === 'missing').length, 1);
  });
  await t.test('transparent text cannot satisfy the visible label', async () => {
    page = `<!doctype html><style>body{margin:0}#status text{fill:transparent}</style>${svg}`;
    const report = await compare(); assert.equal(report.rows.find(row => row.part === '“READY”').status, 'hidden');
  });
  await t.test('applied clipping cannot silently pass required text on either side', async t => {
    t.after(() => writeFileSync(join(input.cwd, input.drawingPath), svg));
    page = `<!doctype html><style>body{margin:0}#status text{clip-path:inset(100%)}</style>${svg}`;
    await assert.rejects(compare(), /unsupported.*clip|clip.*unsupported/i);
    const clipped = svg.replace('<text x="10" y="28">READY', '<text style="clip-path:inset(100%)" x="10" y="28">READY');
    assert.notEqual(clipped, svg);
    writeFileSync(join(input.cwd, input.drawingPath), clipped); page = `<!doctype html><style>body{margin:0}</style>${svg}`;
    await assert.rejects(compare(), /unsupported.*clip|clip.*unsupported/i);
    writeFileSync(join(input.cwd, input.drawingPath), svg);
  });
  await t.test('transparent primitive ids fail while transparent structural regions with painted descendants pass', async t => {
    t.after(() => writeFileSync(join(input.cwd, input.drawingPath), svg));
    const special = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><g id="region" fill="transparent"><rect id="box" x="20" y="20" width="120" height="80" fill="red"/><text x="20" y="160" fill="black">READY</text></g></svg>';
    writeFileSync(join(input.cwd, input.drawingPath), special); page = `<!doctype html><style>body{margin:0}</style>${special}`;
    assert.equal((await compare()).passed, true);
    page = `<!doctype html><style>body{margin:0}#box{fill:transparent;stroke:none}</style>${special}`;
    const report = await compare(); assert.equal(report.passed, false); assert.equal(report.rows.find(row => row.part === '#box').status, 'hidden');
    writeFileSync(join(input.cwd, input.drawingPath), special.replace('fill="red"', 'fill="transparent"'));
    const excluded = await compare(); assert.ok(!excluded.rows.some(row => row.part === '#box')); assert.equal(excluded.passed, true);
    writeFileSync(join(input.cwd, input.drawingPath), svg);
  });
  await t.test('empty transparent HTML box cannot satisfy a painted id; visible structural children can', async t => {
    t.after(() => writeFileSync(join(input.cwd, input.drawingPath), svg));
    const special = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><rect id="box" x="20" y="20" width="120" height="80"/><text x="20" y="160">READY</text></svg>';
    writeFileSync(join(input.cwd, input.drawingPath), special);
    const html = content => `<!doctype html><style>body{margin:0}#box{position:absolute;left:20px;top:20px;width:120px;height:80px}#label{position:absolute;left:20px;top:145px}</style><div id="box">${content}</div><span id="label">READY</span>`;
    page = html('');
    const hidden = await compare(); assert.equal(hidden.passed, false); assert.equal(hidden.rows.find(row => row.part === '#box').status, 'hidden'); assert.equal(hidden.rows.find(row => row.part === '“READY”').status, 'pass');
    page = html('<span>Visible child</span>');
    const visible = await compare(); assert.equal(visible.passed, true, JSON.stringify(visible.rows));
    page = html('<span style="opacity:0">Invisible child</span>');
    assert.equal((await compare()).rows.find(row => row.part === '#box').status, 'hidden');
  });
  await t.test('visible text joins around hidden descendants without hidden words or wrong geometry', async t => {
    t.after(() => writeFileSync(join(input.cwd, input.drawingPath), svg));
    for (const content of ['Visible<tspan style="display:none">SECRET</tspan>', 'Vis<tspan style="display:none">SECRET</tspan>ible', 'Vis<tspan style="visibility:hidden">SECRET</tspan>ible']) {
      const special = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><text x="20" y="60">${content}</text></svg>`;
      writeFileSync(join(input.cwd, input.drawingPath), special); page = `<!doctype html><style>body{margin:0}</style>${special}`;
      const report = await compare(); assert.equal(report.passed, true, JSON.stringify(report.rows)); assert.deepEqual(report.rows.map(row => row.part), ['“Visible”']);
    }
    writeFileSync(join(input.cwd, input.drawingPath), svg);
  });
  await t.test('quoted local fragment paint resources stay safe while external resources fail', async t => {
    t.after(() => writeFileSync(join(input.cwd, input.drawingPath), svg));
    for (const resource of ['url(#paint)', "url('#paint')", 'url(&quot;#paint&quot;)']) {
      const special = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><defs><linearGradient id="paint"><stop stop-color="red"/></linearGradient><clipPath id="unused"><rect width="50" height="50"/></clipPath></defs><rect id="box" x="20" y="20" width="120" height="80" fill="${resource}"/></svg>`;
      writeFileSync(join(input.cwd, input.drawingPath), special); page = `<!doctype html><style>body{margin:0}</style>${special}`;
      assert.equal((await compare()).passed, true, resource);
      writeFileSync(join(input.cwd, input.drawingPath), special.replace('#paint', 'https://example.test/a.svg#paint'));
      await assert.rejects(compare(), /external|unsupported/i);
    }
    writeFileSync(join(input.cwd, input.drawingPath), svg);
  });
  await t.test('separate text nodes in one element are distinct visible occurrences', async () => {
    writeFileSync(join(input.cwd, input.drawingPath), '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><text x="20" y="60">2</text><text x="20" y="90">2</text></svg>');
    page = '<!doctype html><div style="position:absolute;left:20px;top:40px;line-height:30px">2<br>2</div>';
    const report = await compare(); assert.equal(report.passed, true, JSON.stringify(report.rows)); assert.equal(report.rows.length, 2);
    writeFileSync(join(input.cwd, input.drawingPath), svg);
  });
  await t.test('moved regions and duplicate ids fail visibly', async () => {
    page = `<!doctype html><style>body{margin:0}#score{transform:translate(0,20px)}</style>${svg}<script type="application/json" id="seed">{}</script>`;
    const report = await compare(); assert.equal(report.rows.find(row => row.part === '#score').status, 'region'); assert.match(report.rows.find(row => row.part === '#seed').actual, /duplicate/);
  });
  await t.test('nonzero SVG origin and decoded entity geometry compare against the rendered reference', async () => {
    const special = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="100 200 400 400"><g transform="translate(120 220)"><text id="label" x="0" y="20">Go &amp; win</text></g></svg>';
    writeFileSync(join(input.cwd, input.drawingPath), special); page = `<!doctype html><style>body{margin:0}svg{width:400px;height:400px}</style>${special}`;
    const report = await compare(); assert.equal(report.passed, true); assert.ok(report.rows.some(row => row.part === '“Go & win”'));
    writeFileSync(join(input.cwd, input.drawingPath), svg);
  });
  await t.test('malformed/empty/unsafe references and invalid viewport never produce empty pass', async () => {
    for (const source of ['<svg><text>bad</svg>', '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"/>', '<svg xmlns="http://www.w3.org/2000/svg"><text>no viewport</text></svg>', '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 -1 400"><text>bad</text></svg>', '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><image href="https://example.test/a.png"/></svg>', '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><rect id="same" width="10" height="10"/><rect id="same" x="20" width="10" height="10"/></svg>']) {
      writeFileSync(join(input.cwd, input.drawingPath), source); await assert.rejects(compare(), error => error.exitCode === 2);
    }
    copyFileSync(fixture, join(input.cwd, input.drawingPath));
  });
  await t.test('failed URL and HTTP error are execution errors', async () => {
    status = 404; await assert.rejects(compare(), error => error.exitCode === 5); status = 200;
    await assert.rejects(compareScreen({ ...input, url: 'http://127.0.0.1:1/', chromePath: chrome }, { env: profileEnv }), error => error.exitCode === 5);
  });
  await t.test('public CLI uses injected browser env, requires no Git and returns mismatch JSON', async () => {
    page = '<!doctype html><p>No required parts</p>';
    const stdout = sink(), stderr = sink();
    const code = await runPdd(['check', '--screen', input.url, '--drawing', input.drawingPath, '--json'], { cwd: input.cwd, env: { ...profileEnv, PDD_RUNTIME_URL: 'invalid', PDD_STATE_DIR: input.cwd }, stdout, stderr });
    assert.equal(code, 1, stderr.text); const report = JSON.parse(stdout.text); assert.equal(report.exit_code, 1); assert.equal(report.passed, false);
  });
});
