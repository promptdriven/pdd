import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { createServer } from 'node:http';
import { accessSync, constants, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

// Synthetic protocol fixtures exercise actual DOM capture through the public
// CLI process. They are not a hosted Runtime or original Snake reproduction.
const chrome = [process.env.PDD_CHROME_PATH, '/usr/local/bin/chromium', '/usr/bin/chromium', '/usr/bin/google-chrome'].find(path => {
  try { if (path) { accessSync(path, constants.X_OK); return true; } } catch { /* next */ } return false;
});
const cli = resolve(import.meta.dirname, '../bin/pdd.mjs');
const svg = '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><g id="score"><rect x="20" y="20" width="120" height="80" fill="silver"/><text x="30" y="50">SCORE</text><text x="30" y="75">0</text></g><g id="ready"><rect x="20" y="280" width="350" height="45" fill="silver"/><text x="30" y="307">READY</text></g></svg>';
const appHtml = '<style>html,body{margin:0;padding:0}section{position:absolute;background:silver}#score{left:5%;top:5%;width:30%;height:20%}#ready{left:5%;top:70%;width:87.5%;height:11.25%}span{position:absolute;font:16px serif;left:10px;top:12px}#score span+span{top:37px}</style><section id="score"><span>SCORE</span><span>0</span></section><section id="ready"><span>READY</span></section>';
function door({ state = 'ready', reason, version = '1', kind = 'html', content = appHtml, scale = false, script = '', extra = '' } = {}) {
  const attrs = `data-pdd-screen-door="${version}" data-pdd-screen-state="${state}"${reason ? ` data-pdd-screen-reason="${reason}"` : ''}`;
  const sizing = scale ? 'width:800px;height:800px;transform:scale(.4);transform-origin:top left' : 'width:400px;height:400px';
  let surface;
  if (kind === 'html') surface = `<iframe data-pdd-app-frame="html" style="border:0;${sizing}" srcdoc="${content.replaceAll('&', '&amp;').replaceAll('"', '&quot;')}"></iframe>`;
  else surface = `<div id="apphost" data-pdd-app-frame="shadow" style="position:relative;${sizing}"></div>`;
  return `<!doctype html><html ${attrs}><head><style>body{margin:0}#frame{margin:180px 0 0 24px}#shell{position:absolute;top:0}</style></head><body><div id="shell"><div id="score">SCORE 0</div><div id="ready">READY</div><button onclick="fetch('/action',{method:'POST'})">Open the app</button></div><div id="frame">${surface}${extra}</div><script>${kind !== 'html' ? `document.getElementById('apphost').attachShadow({mode:'open'}).innerHTML=${JSON.stringify(content)};` : ''}${script}</script></body></html>`;
}

test('Screen readiness public CLI regression: synthetic door protocol and actual app DOM', { skip: !chrome, timeout: 180000 }, async t => {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-screen-door-test-'));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  const drawing = join(cwd, 'screen.ui.svg'); writeFileSync(drawing, svg);
  let page = '', status = 200, posts = 0, fontDelay = 250;
  const requests = [];
  const server = createServer((req, res) => {
    requests.push(`${req.method} ${req.url}`);
    if (req.method !== 'GET') { posts++; res.writeHead(500); res.end('No actions allowed'); return; }
    if (req.url === '/font') { const timer = setTimeout(() => { res.writeHead(200, { 'content-type': 'font/woff2' }); res.end('controlled invalid font: use fallback after load'); }, fontDelay); res.on('close', () => clearTimeout(timer)); return; }
    res.writeHead(status, { 'content-type': 'text/html' }); res.end(page);
  });
  await new Promise(done => server.listen(0, '127.0.0.1', done));
  t.after(() => new Promise(done => { server.closeAllConnections(); server.close(done); }));
  const url = `http://127.0.0.1:${server.address().port}/`;
  const run = async ({ json = true, env = {}, target = url, reference = drawing } = {}) => {
    let stdout = '', stderr = '';
    const child = spawn(process.execPath, [cli, 'test', '--screen', target, '--drawing', reference, ...(json ? ['--json'] : [])], {
      cwd, env: { ...process.env, PDD_CHROME_PATH: chrome, PDD_RUNTIME_URL: 'invalid-no-runtime', PDD_STATE_DIR: join(cwd, 'state'), ...env }, stdio: ['ignore', 'pipe', 'pipe'],
    });
    child.stdout.on('data', data => { stdout += data; }); child.stderr.on('data', data => { stderr += data; });
    const exit = await new Promise((done, reject) => { child.on('error', reject); child.on('close', (code, signal) => signal ? reject(Error(`CLI killed: ${signal}`)) : done(code)); });
    return { exit, stdout, stderr, ...(json && stdout.trim() ? { report: JSON.parse(stdout) } : {}) };
  };
  const passing = (result, rows = 5) => {
    assert.equal(result.exit, 0, result.stderr || result.stdout); assert.equal(result.stderr, '');
    assert.deepEqual(result.report.viewport, { width: 400, height: 400 }); assert.equal(result.report.passed, true);
    assert.equal(result.report.rows.length, rows); assert.ok(result.report.rows.every(row => row.status === 'pass'));
  };
  const notReady = (result, state, reason) => {
    assert.equal(result.exit, 6, result.stderr || result.stdout); assert.equal(result.stderr, '');
    assert.deepEqual(Object.keys(result.report), ['drawing', 'url', 'outcome', 'code', 'state', 'reason', 'message', 'exit_code']);
    assert.equal(result.report.drawing, drawing); assert.equal(result.report.url, url);
    assert.equal(result.report.outcome, 'not-ready'); assert.equal(result.report.code, 'screen-not-ready');
    assert.equal(result.report.state, state); assert.equal(result.report.reason, reason); assert.equal(result.report.exit_code, 6);
    assert.equal(typeof result.report.message, 'string'); assert.ok(result.report.message.length > 0);
  };
  await t.test('AC1 delayed ready before deadline captures settled app rather than shell', async () => {
    page = door({ state: 'loading', script: "setTimeout(()=>document.documentElement.dataset.pddScreenState='ready',6000)" });
    passing(await run());
  });
  await t.test('AC1 AC5 HTML uses its own viewport despite shell offsets and renderer scaling', async () => { page = door({ scale: true }); passing(await run()); });
  for (const [format, content] of [
    ['SVG', svg.replace('<svg ', '<svg width="100%" height="100%" ')],
  ]) await t.test(`AC5 ${format} open shadow surface uses app-local geometry`, async () => { page = door({ kind: 'shadow', content, scale: true }); passing(await run()); });
  for (const format of ['text', 'grid']) await t.test(`AC5 ${format} literal rows stay inside their open shadow app surface`, async () => {
    const reference = join(cwd, `${format}.ui.svg`);
    writeFileSync(reference, '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><text x="10" y="40">SCORE 0 READY</text></svg>');
    const pre = '<pre style="margin:0;font:16px monospace">SCORE\n0\nREADY</pre>';
    page = door({ kind: 'shadow', content: format === 'grid' ? pre.replace('<pre ', '<pre class="appgrid" ') : `<div class="apptext">${pre}</div>`, scale: true });
    passing(await run({ reference }), 1);
  });
  await t.test('AC1 selected document fonts and layout settle before capture', async () => {
    page = door({ content: appHtml.replace('>READY<', '><'), script: `addEventListener('load',()=>{const doc=document.querySelector('iframe').contentDocument;const font=new doc.defaultView.FontFace('Controlled','url(/font)');doc.fonts.add(font);doc.fonts.load('16px Controlled').catch(()=>{});doc.fonts.ready.then(()=>doc.querySelector('#ready span').textContent='READY');});` });
    passing(await run());
    assert.ok(requests.includes('GET /font'));
  });
  for (const elapsed of [9999, 10000]) await t.test(`AC1 deadline boundary at ${elapsed} ms (controlled monotonic clock)`, async () => {
    page = door({ script: `let reads=0;Object.defineProperty(performance,'now',{value:()=>reads++===0?0:${elapsed}});` });
    const result = await run();
    if (elapsed < 10000) passing(result); else notReady(result, 'ready', 'timeout');
  });
  await t.test('AC2 loading old frame stays not ready through the deadline', async () => { page = door({ state: 'loading' }); notReady(await run(), 'loading', 'timeout'); });
  await t.test('AC1 app font wait is included in the readiness deadline', async () => {
    fontDelay = 15000;
    page = door({ script: `addEventListener('load',()=>{const doc=document.querySelector('iframe').contentDocument;const font=new doc.defaultView.FontFace('Controlled','url(/font)');doc.fonts.add(font);doc.fonts.load('16px Controlled').catch(()=>{});});` });
    notReady(await run(), 'ready', 'timeout'); fontDelay = 250;
  });
  await t.test('AC3 unopened screen reports deliberate opening and AI cost without clicking', async () => {
    page = door({ state: 'not-open' }); const result = await run(); notReady(result, 'not-open', 'not-open');
    assert.match(result.report.message, /[Dd]eliberately open/); assert.match(result.report.message, /AI calls/);
    const text = await run({ json: false }); assert.equal(text.exit, 6); assert.match(text.stdout, /^Screen not ready \(not-open; not-open\):/); assert.doesNotMatch(text.stdout, /\| Part|Screen vs drawing/);
  });
  for (const reason of ['state-read-failed', 'render-failed', 'action-unknown']) await t.test(`AC4 ${reason} rejects an older matching painted frame`, async () => { page = door({ state: 'error', reason }); notReady(await run(), 'error', reason); });
  await t.test('AC4 errors during app settling stop immediately', async () => {
    fontDelay = 15000; page = door({ script: `addEventListener('load',()=>{const doc=document.querySelector('iframe').contentDocument;const font=new doc.defaultView.FontFace('Controlled','url(/font)');doc.fonts.add(font);doc.fonts.load('16px Controlled').catch(()=>{});setTimeout(()=>{document.documentElement.dataset.pddScreenState='error';document.documentElement.dataset.pddScreenReason='action-unknown'},150);});` });
    const started = performance.now(); notReady(await run(), 'error', 'action-unknown'); assert.ok(performance.now() - started < 5000); fontDelay = 250;
  });
  await t.test('AC6 genuine missing app label cannot borrow the shell label', async () => {
    page = door({ content: appHtml.replace('>READY<', '>WAITING<') }); const result = await run();
    assert.equal(result.exit, 1); assert.equal(result.report.passed, false); assert.equal(result.report.rows.find(row => row.part === '“READY”').status, 'missing');
  });
  for (const [name, markup, status] of [
    ['hidden app label', appHtml.replace('>READY<', ' hidden>READY<'), 'hidden'],
    ['private app value', appHtml.replace('<span>READY</span>', '<input type="password" value="READY">'), 'missing'],
    ['label outside its app owner', appHtml.replace('<section id="ready"><span>READY</span></section>', '<section id="ready"></section><span>READY</span>'), 'missing'],
    ['offscreen app label', appHtml.replace('<span>READY</span>', '<span style="top:2000px">READY</span>'), 'hidden'],
  ]) await t.test(`AC6 ${name} cannot satisfy the drawing`, async () => {
    page = door({ content: markup }); const result = await run();
    assert.equal(result.exit, 1, result.stderr || result.stdout); assert.equal(result.report.rows.find(row => row.part === '“READY”').status, status);
  });
  for (const [effect, css] of [
    ['filter', 'filter:opacity(0)'],
    ['clip-path', 'clip-path:inset(100%)'],
    ['clip', 'position:absolute;clip:rect(0px,0px,0px,0px)'],
    ['mask', 'mask-image:linear-gradient(transparent,transparent)'],
  ]) for (const [target, selector] of [['iframe host', 'iframe'], ['outer ancestor', '#frame']]) {
    await t.test(`AC6 ${target} applied ${effect} cannot produce a passing drawing verdict`, async () => {
      page = door({ script: `document.querySelector(${JSON.stringify(selector)}).style.cssText+=${JSON.stringify(';' + css)};` });
      const result = await run();
      assert.equal(result.exit, 5, result.stderr || result.stdout);
      assert.equal(result.stdout, '');
      assert.equal(result.stderr, 'Screen comparison: Unsupported applied clip-path, clip, mask or filter; visible parts cannot be established.\n');
    });
  }
  for (const [target, selector, css] of [
    ['body ancestor', 'body', 'filter:opacity(0)'],
    ['root ancestor', 'html', 'mask-image:linear-gradient(transparent,transparent)'],
  ]) await t.test(`AC6 ${target} applied effect cannot produce a passing drawing verdict`, async () => {
    page = door({ script: `document.querySelector(${JSON.stringify(selector)}).style.cssText+=${JSON.stringify(';' + css)};` });
    const result = await run();
    assert.equal(result.exit, 5, result.stderr || result.stdout);
    assert.equal(result.stdout, '');
    assert.equal(result.stderr, 'Screen comparison: Unsupported applied clip-path, clip, mask or filter; visible parts cannot be established.\n');
  });
  for (const [target, selector] of [['iframe host', 'iframe'], ['outer ancestor', '#frame']]) {
    for (const hidden of ['opacity:0', 'visibility:hidden']) await t.test(`AC6 ${target} ${hidden} stays hidden before unsupported effects`, async () => {
      page = door({ script: `document.querySelector(${JSON.stringify(selector)}).style.cssText+=${JSON.stringify(';' + hidden + ';filter:opacity(0);clip-path:inset(100%)')};` });
      const result = await run();
      assert.equal(result.exit, 1, result.stderr || result.stdout);
      assert.equal(result.stderr, '');
      assert.equal(result.report.passed, false);
      assert.ok(result.report.rows.every(row => row.status === 'hidden'));
    });
  }
  await t.test('AC5 shell overflow and page scroll do not clip app-local visibility', async () => {
    page = door({ script: "const frame=document.querySelector('#frame');frame.style.cssText+=';overflow:hidden;height:10px';document.body.style.height='2000px';scrollTo(0,1000);" });
    passing(await run());
  });
  for (const [name, changes] of [
    ['missing', { kind: 'shadow', script: "document.getElementById('apphost').remove()" }],
    ['ambiguous', { extra: '<div data-pdd-app-frame="shadow"></div>' }],
    ['inaccessible iframe', { script: "const f=document.querySelector('iframe');f.setAttribute('sandbox','');f.srcdoc=f.srcdoc" }],
    ['closed shadow root', { kind: 'shadow', script: "const old=document.getElementById('apphost'),closed=document.createElement('div');closed.dataset.pddAppFrame='shadow';closed.style.cssText='width:400px;height:400px';closed.attachShadow({mode:'closed'}).innerHTML='READY';old.replaceWith(closed)" }],
  ]) await t.test(`AC7 ${name} selected surface is unavailable`, async () => { page = door(changes); notReady(await run(), 'ready', 'surface-unavailable'); });
  for (const [name, changes] of [['unsupported', { version: '2' }], ['invalid state', { state: 'working' }], ['invalid error reason', { state: 'error', reason: 'other' }]]) await t.test(`AC7 ${name} requires viewer update`, async () => { page = door(changes); notReady(await run(), 'unknown', 'viewer-update-required'); });
  await t.test('AC7 legacy fingerprint requires viewer update', async () => {
    page = '<!doctype html><html data-try-session="example"><head><base href="/__pdd/screen/"><script src="door-screen.js"></script></head><body>READY</body></html>';
    notReady(await run(), 'unknown', 'viewer-update-required');
  });
  await t.test('AC8 ordinary pass and mismatch preserve their JSON shape', async () => {
    page = '<!doctype html><style>body{margin:0}</style>' + svg; const result = await run(); passing(result);
    assert.deepEqual(Object.keys(result.report), ['drawing', 'url', 'viewport', 'rows', 'passed', 'exit_code']);
    page = page.replace('>READY<', '>WAITING<'); const mismatch = await run(); assert.equal(mismatch.exit, 1); assert.equal(mismatch.report.passed, false);
  });
  await t.test('AC8 a lone iframe or partial legacy fingerprint is an ordinary page', async () => {
    page = '<!doctype html><html data-try-session="ordinary"><style>body{margin:0}</style>' + svg + '<iframe hidden></iframe></html>'; passing(await run());
  });
  await t.test('AC8 HTTP and connection errors retain exit 5 and no drawing verdict', async () => {
    status = 503; const failed = await run(); assert.equal(failed.exit, 5); assert.equal(failed.stdout, ''); assert.match(failed.stderr, /HTTP 503/); status = 200;
    const disconnected = await run({ target: 'http://127.0.0.1:1/' }); assert.equal(disconnected.exit, 5); assert.equal(disconnected.stdout, '');
    const browser = await run({ env: { PDD_CHROME_PATH: '/no-chrome' } }); assert.equal(browser.exit, 5); assert.equal(browser.stdout, '');
  });
  await t.test('AC8 invalid drawing retains exit 2 before a not-open screen', async () => {
    page = door({ state: 'not-open' }); writeFileSync(join(cwd, 'bad.ui.svg'), '<svg>');
    const result = await run({ reference: join(cwd, 'bad.ui.svg') }); assert.equal(result.exit, 2); assert.equal(result.stdout, '');
  });
  assert.equal(posts, 0, 'comparison must not dispatch an app action');
  assert.ok(requests.every(request => request.startsWith('GET ')), JSON.stringify(requests));
});
