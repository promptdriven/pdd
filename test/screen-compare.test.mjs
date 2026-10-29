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

test('public CLI requires effective text paint and literal displayed control labels', { skip: !chrome, timeout: 180000 }, async t => {
  const source = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><text id="label" x="20" y="160">READY</text></svg>';
  const input = setup(t, source);
  let page = '';
  const server = createServer((_, res) => { res.writeHead(200, { 'content-type': 'text/html' }); res.end(page); });
  await new Promise(done => server.listen(0, '127.0.0.1', done));
  t.after(() => new Promise(done => { server.closeAllConnections(); server.close(done); }));
  const url = `http://127.0.0.1:${server.address().port}/`;
  const check = async (markup, style = '') => {
    page = `<style>body{margin:0}#label{position:absolute;left:20px;top:145px;font:16px serif;width:90px;height:22px;padding:0;border:0;${style}}</style>${markup}`;
    const stdout = sink(), stderr = sink();
    const code = await runPdd(['check', '--screen', url, '--drawing', input.drawingPath, '--json'], { cwd: input.cwd, env: { ...process.env, PDD_CHROME_PATH: chrome, PDD_RUNTIME_URL: 'invalid-offline', PDD_STATE_DIR: input.cwd }, stdout, stderr });
    return { code, stdout: stdout.text, stderr: stderr.text, report: stdout.text ? JSON.parse(stdout.text) : null };
  };
  for (const [name, markup] of [
    ['ordinary span', '<span id="label">READY</span>'],
    ...['text', 'search', 'tel', 'url', 'email', 'submit', 'button', 'reset'].map(type => [type, `<input id="label" type="${type}" value="READY">`]),
    ['textarea current value', '<textarea id="label">OLD</textarea><script>document.querySelector("textarea").value="READY"</script>'],
    ['select option label', '<select id="label"><option label="READY" selected>WRONG</option></select>'],
  ]) await t.test(`${name} keeps its literal visible label`, async () => {
    const result = await check(markup); assert.equal(result.code, 0, result.stderr || result.stdout); assert.equal(result.report.passed, true);
  });
  for (const markup of ['<span id="label">READY</span>', '<input id="label" value="READY">', '<textarea id="label">READY</textarea>', '<select id="label"><option>READY</option></select>']) await t.test(`transparent effective fill hides text in ${markup.split(/[ >]/)[0]}`, async () => {
    const result = await check(markup, '-webkit-text-fill-color:transparent');
    assert.equal(result.code, 1, result.stderr || result.stdout); assert.equal(result.report.rows.find(row => row.kind === 'text').status, 'hidden');
    if (markup.startsWith('<span')) assert.equal(result.report.rows.find(row => row.kind === 'id').status, 'hidden');
  });
  await t.test('effective fill can paint text despite transparent color', async () => {
    const result = await check('<span id="label">READY</span>', 'color:transparent;-webkit-text-fill-color:black'); assert.equal(result.code, 0, result.stderr || result.stdout);
  });
  for (const type of ['password', 'checkbox', 'radio', 'color', 'range', 'image', 'file', 'hidden']) await t.test(`${type} stored value is not a literal label`, async t => {
    t.after(() => writeFileSync(join(input.cwd, input.drawingPath), source));
    const value = type === 'color' ? '#123456' : type === 'range' ? '42' : 'READY';
    writeFileSync(join(input.cwd, input.drawingPath), source.replace('READY', value));
    const result = await check(`<input id="label" type="${type}" value="${value}">`);
    assert.equal(result.code, 1, result.stderr || result.stdout); assert.equal(result.report.rows.find(row => row.kind === 'text').status, 'missing');
    if (['password', 'checkbox', 'radio'].includes(type)) assert.equal(result.report.rows.find(row => row.kind === 'id').status, 'pass');
  });
  await t.test('ordinary numeric input keeps its literal value', async t => {
    t.after(() => writeFileSync(join(input.cwd, input.drawingPath), source));
    writeFileSync(join(input.cwd, input.drawingPath), source.replace('READY', '42'));
    const result = await check('<input id="label" type="number" value="42">'); assert.equal(result.code, 0, result.stderr || result.stdout);
  });
  for (const [type, value] of [['date', '2026-10-28'], ['month', '2026-10'], ['week', '2026-W44'], ['time', '12:34'], ['datetime-local', '2026-10-28T12:34']]) await t.test(`${type} native formatting remains explicitly unproved`, async t => {
    t.after(() => writeFileSync(join(input.cwd, input.drawingPath), source));
    writeFileSync(join(input.cwd, input.drawingPath), source.replace('READY', value));
    const result = await check(`<input id="label" type="${type}" value="${value}">`);
    assert.equal(result.code, 5, result.stderr || result.stdout); assert.match(result.stderr, /unsupported.*format|format.*unsupported/i);
    writeFileSync(join(input.cwd, input.drawingPath), source);
  });
  for (const style of ['-webkit-text-security:disc', '-webkit-text-fill-color:transparent;-webkit-text-stroke:1px black', '-webkit-text-fill-color:transparent;text-shadow:0 0 1px black']) await t.test(`unsupported glyph rendering cannot manufacture a literal match: ${style}`, async () => {
    const result = await check('<span id="label">READY</span>', style); assert.equal(result.code, 5, result.stderr || result.stdout); assert.match(result.stderr, /unsupported.*text|text.*unsupported/i);
  });
  await t.test('private and stale control content never leaks into reports or supplies labels', async () => {
    const secret = 'PRIVATE_INPUT_VALUE_7301';
    const result = await check(`<input id="label" type="password" value="${secret}">`);
    assert.equal(result.code, 1); assert.ok(!`${result.stdout}${result.stderr}`.includes(secret));
    for (const markup of ['<textarea id="label">READY</textarea><script>document.querySelector("textarea").value="WRONG"</script>', '<select id="label"><option>READY</option><option selected>WRONG</option></select>', '<button id="label" value="READY">WRONG</button>']) {
      const wrong = await check(markup); assert.equal(wrong.code, 1, wrong.stderr || wrong.stdout); assert.equal(wrong.report.rows.find(row => row.kind === 'text').status, 'missing');
    }
  });
});

test('formatter preserves adversarial content as literal table text', () => {
  const literal = 'a\\|b <img src=x onerror=alert(1)> &lt;tag&gt; [link](javascript:alert(1)) `*em*';
  const output = formatScreenComparison({ drawing: literal, viewport: { width: 400, height: 400 }, passed: false, rows: [{ part: literal, kind: 'id', expected: 'a\nb', actual: literal, status: 'missing' }] });
  assert.ok(output.includes(String.raw`a\\\|b`), output);
  assert.ok(output.includes(String.raw`&lt;img src=x onerror=alert\(1\)&gt; &amp;lt;tag&amp;gt;`), output);
  assert.ok(output.includes(String.raw`\[link\]\(javascript:alert\(1\)\)`), output);
  assert.ok(output.includes('\\`' + String.raw`\*em\*`), output);
  assert.ok(!output.includes('<img'));
  assert.equal(output.split('\n').filter(line => line.startsWith('| ')).length, 3);
  assert.ok(output.includes('a b'));
});

test('public CLI refuses unestablished SVG geometry and keeps all rendered SVG ids required', { skip: !chrome, timeout: 180000 }, async t => {
  const wrap = body => `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400">${body}<text x="20" y="160">READY</text></svg>`;
  const input = setup(t);
  let page;
  const server = createServer((_, res) => { res.writeHead(200, { 'content-type': 'text/html' }); res.end(`<style>body{margin:0}</style>${page}`); });
  await new Promise(done => server.listen(0, '127.0.0.1', done));
  t.after(() => new Promise(done => { server.closeAllConnections(); server.close(done); }));
  const check = async (reference, actual = '') => {
    writeFileSync(join(input.cwd, input.drawingPath), wrap(reference)); page = actual.startsWith('<div') ? actual + wrap('') : wrap(actual);
    const stdout = sink(), stderr = sink();
    const code = await runPdd(['check', '--screen', `http://127.0.0.1:${server.address().port}/`, '--drawing', input.drawingPath, '--json'], { cwd: input.cwd, env: { ...process.env, PDD_CHROME_PATH: chrome, PDD_RUNTIME_URL: 'invalid-offline', PDD_STATE_DIR: input.cwd }, stdout, stderr });
    return { code, stderr: stderr.text, stdout: stdout.text, report: stdout.text ? JSON.parse(stdout.text) : null };
  };
  for (const [name, geometry] of [
    ['horizontal line', '<line id="rule" x1="20" y1="40" x2="180" y2="40"'],
    ['vertical line', '<line id="rule" x1="40" y1="20" x2="40" y2="180"'],
    ['horizontal path', '<path id="rule" d="M20 40H180"'],
    ['vertical polyline', '<polyline id="rule" points="40,20 40,180"'],
    ['group containing an unlabelled line', '<g id="rule"><line x1="20" y1="40" x2="180" y2="40"'],
  ]) await t.test(`${name} with visible stroke cannot vanish from the reference`, async () => {
    const result = await check(`${geometry} fill="none" stroke="black" stroke-width="6"/>${geometry.startsWith('<g') ? '</g>' : ''}`);
    assert.equal(result.code, 2, result.stderr || result.stdout); assert.match(result.stderr, /unsupported.*geometry|geometry.*unsupported/i);
  });
  for (const attrs of ['display="none"', 'visibility="hidden"', 'opacity="0"', 'stroke-opacity="0"', 'stroke="transparent"']) await t.test(`excluded degenerate paint remains excluded: ${attrs}`, async () => {
    const result = await check(`<line id="rule" x1="20" y1="40" x2="180" y2="40" stroke-width="6" ${attrs.includes('stroke=') ? '' : 'stroke="black"'} ${attrs}/>`);
    assert.equal(result.code, 0, result.stderr || result.stdout); assert.deepEqual(result.report.rows.map(row => row.part), ['“READY”']);
  });
  await t.test('inherited opacity and transparent local gradient strokes remain excluded', async () => {
    for (const reference of ['<g opacity="0"><line id="rule" x1="20" y1="40" x2="180" y2="40" stroke="black" stroke-width="6"/></g>', '<defs><linearGradient id="paint"><stop stop-color="transparent"/></linearGradient><filter id="unused"/></defs><line id="rule" x1="20" y1="40" x2="180" y2="40" stroke="url(#paint)" stroke-width="6" filter="url(#unused)"/>']) {
      const result = await check(reference); assert.equal(result.code, 0, result.stderr || result.stdout); assert.deepEqual(result.report.rows.map(row => row.part), ['“READY”']);
    }
  });
  await t.test('local use is already an explicit unsupported reference', async () => {
    const result = await check('<defs><rect id="shape" width="40" height="40"/></defs><use id="icon" href="#shape" x="20" y="20"/>');
    assert.equal(result.code, 2); assert.match(result.stderr, /unsupported.*use/i);
  });
  await t.test('textPath id cannot be supplied by the same words without that id', async () => {
    const reference = '<defs><path id="curve" d="M20 40H180"/></defs><text><textPath id="curved-label" href="#curve">Curved</textPath></text>';
    const missing = await check(reference, '<text x="20" y="40">Curved</text>');
    assert.equal(missing.code, 1, missing.stderr || missing.stdout); assert.equal(missing.report.rows.find(row => row.part === '#curved-label').status, 'missing');
    const positive = await check(reference, reference); assert.equal(positive.code, 0, positive.stderr || positive.stdout);
  });
  await t.test('a page use cannot silently serve as established painted geometry', async () => {
    const result = await check('<rect id="icon" x="20" y="20" width="40" height="40"/>', '<defs><rect id="shape" width="40" height="40"/></defs><use id="icon" href="#shape" x="20" y="20"/>');
    assert.equal(result.code, 5, result.stderr || result.stdout); assert.match(result.stderr, /unsupported.*use/i);
  });
  await t.test('page degenerate stroke cannot supply an established id match', async () => {
    const result = await check('<rect id="rule" x="20" y="20" width="160" height="40"/>', '<line id="rule" x1="20" y1="40" x2="180" y2="40" stroke="black" stroke-width="6"/>');
    assert.equal(result.code, 5, result.stderr || result.stdout); assert.match(result.stderr, /unsupported.*geometry|geometry.*unsupported/i);
  });
  await t.test('ordinary SVG groups, HTML regions, local gradients and unused resources stay supported', async () => {
    const reference = '<defs><linearGradient id="paint"><stop stop-color="red"/></linearGradient><filter id="unused"/></defs><g id="icon"><rect x="20" y="20" width="40" height="40" fill="url(#paint)"/></g>';
    for (const actual of [reference, '<div id="icon" style="position:absolute;left:20px;top:20px;width:40px;height:40px;background:black"></div>']) {
      const result = await check(reference, actual); assert.equal(result.code, 0, result.stderr || result.stdout);
    }
  });
  await t.test('valid comments and literal CDATA never become executable reference content', async () => {
    const result = await check('<!-- <script>throw Error("must not execute")</script> --><text x="20" y="40"><![CDATA[<script>]]></text>', '<text x="20" y="40">&lt;script&gt;</text>');
    assert.equal(result.code, 0, result.stderr || result.stdout);
    assert.deepEqual(result.report.rows.map(row => [row.part, row.status]), [['“<script>”', 'pass'], ['“READY”', 'pass']]);
  });
  for (const comment of ['<!--outer<!-- nested -->', '<!-- unterminated', '<!-- bad -- content -->', '<!-- trailing --->']) await t.test(`malformed reference comments cannot pass: ${comment}`, async () => {
    const result = await check(comment); assert.equal(result.code, 2, result.stderr || result.stdout); assert.match(result.stderr, /comment|malformed/i);
  });
});

test('public CLI requires literal CDATA labels, distinct occurrences and visible geometry', { skip: !chrome, timeout: 180000 }, async t => {
  const wrap = body => `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400">${body}<text x="20" y="320">READY</text></svg>`;
  const input = setup(t);
  let page;
  // XML preserves CDATA_SECTION_NODE on the actual page as well as the reference.
  const server = createServer((_, res) => { res.writeHead(200, { 'content-type': 'image/svg+xml' }); res.end(page); });
  await new Promise(done => server.listen(0, '127.0.0.1', done));
  t.after(() => new Promise(done => { server.closeAllConnections(); server.close(done); }));
  const check = async (reference, actual = reference) => {
    writeFileSync(join(input.cwd, input.drawingPath), wrap(reference)); page = wrap(actual);
    const stdout = sink(), stderr = sink();
    const code = await runPdd(['check', '--screen', `http://127.0.0.1:${server.address().port}/`, '--drawing', input.drawingPath, '--json'], { cwd: input.cwd, env: { ...process.env, PDD_CHROME_PATH: chrome, PDD_RUNTIME_URL: 'invalid-offline', PDD_STATE_DIR: input.cwd }, stdout, stderr });
    return { code, stderr: stderr.text, stdout: stdout.text, report: stdout.text ? JSON.parse(stdout.text) : null };
  };
  const label = '<text id="label" x="20" y="40"><![CDATA[CDATA REQUIRED]]></text>';
  await t.test('CDATA on both sides is required literal text', async () => {
    const result = await check(label); assert.equal(result.code, 0, result.stderr || result.stdout);
    assert.deepEqual(result.report.rows.map(row => [row.part, row.status]), [['#label', 'pass'], ['“CDATA REQUIRED”', 'pass'], ['“READY”', 'pass']]);
  });
  await t.test('an id with wrong content cannot hide a CDATA label mismatch', async () => {
    const result = await check(label, '<text id="label" x="20" y="40">WRONG</text>');
    assert.equal(result.code, 1, result.stderr || result.stdout);
    assert.equal(result.report.rows.find(row => row.part === '“CDATA REQUIRED”')?.status, 'missing');
  });
  await t.test('mixed text and CDATA aggregate literally without parsing markup or entities', async () => {
    const result = await check('<text x="20" y="40">Alpha <![CDATA[<literal>&word]]> Omega</text>', '<text x="20" y="40">Alpha &lt;literal&gt;&amp;word Omega</text>');
    assert.equal(result.code, 0, result.stderr || result.stdout);
    assert.deepEqual(result.report.rows.map(row => [row.part, row.status]), [['“Alpha <literal>&word Omega”', 'pass'], ['“READY”', 'pass']]);
  });
  const repeated = '<text x="20" y="40"><![CDATA[SAME]]></text><text x="20" y="80">SA<![CDATA[ME]]></text>';
  await t.test('repeated mixed labels use distinct displayed occurrences', async () => {
    const result = await check(repeated); assert.equal(result.code, 0, result.stderr || result.stdout);
    assert.deepEqual(result.report.rows.map(row => [row.part, row.status]), [['“SAME”', 'pass'], ['“SAME”', 'pass'], ['“READY”', 'pass']]);
  });
  await t.test('one mixed occurrence cannot supply two required labels through ancestor aggregation', async () => {
    const result = await check(repeated, '<g><text x="20" y="40">SA<![CDATA[ME]]></text></g>');
    assert.equal(result.code, 1, result.stderr || result.stdout);
    assert.deepEqual(result.report.rows.filter(row => row.part === '“SAME”').map(row => row.status), ['pass', 'missing']);
  });
  await t.test('hidden and context-only reference CDATA stays excluded', async () => {
    const result = await check('<text display="none" x="20" y="40"><![CDATA[HIDDEN]]></text><g opacity="0"><text x="20" y="80"><![CDATA[TRANSPARENT]]></text></g><text data-context-only="true" x="20" y="120"><![CDATA[CONTEXT]]></text>', '');
    assert.equal(result.code, 0, result.stderr || result.stdout);
    assert.deepEqual(result.report.rows.map(row => row.part), ['“READY”']);
  });
  await t.test('hidden page CDATA cannot satisfy a visible required label', async () => {
    const result = await check(label, '<text id="label" visibility="hidden" x="20" y="40"><![CDATA[CDATA REQUIRED]]></text>');
    assert.equal(result.code, 1, result.stderr || result.stdout);
    assert.equal(result.report.rows.find(row => row.part === '“CDATA REQUIRED”')?.status, 'hidden');
  });
  await t.test('CDATA uses its rendered region instead of passing moved text', async () => {
    const result = await check(label, label.replace('y="40"', 'y="200"'));
    assert.equal(result.code, 1, result.stderr || result.stdout);
    assert.equal(result.report.rows.find(row => row.part === '“CDATA REQUIRED”')?.status, 'region');
  });
});
