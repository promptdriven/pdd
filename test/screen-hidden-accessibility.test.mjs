import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { accessSync, constants, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { sink, temp } from './helpers/runtime-fake.mjs';

const chrome = [
  process.env.PDD_CHROME_PATH,
  '/usr/local/bin/chromium',
  '/usr/bin/google-chrome',
  '/usr/bin/chromium',
  '/usr/bin/chromium-browser',
  '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
].find(path => { try { if (path) { accessSync(path, constants.X_OK); return true; } } catch { /* next */ } return false; });

const spec = JSON.parse(readFileSync(new URL('../fixtures/native-cases/screen-hidden-accessibility.json', import.meta.url), 'utf8'));
const baseStyle = 'html,body{margin:0;padding:0}#search-box{position:absolute;left:20px;top:20px;width:360px;height:120px;background:#e2e8f0}h1{position:absolute;left:20px;top:22px;margin:0;font:20px sans-serif;color:#0f172a}';
const srOnly = 'position:absolute;width:1px;height:1px;padding:0;margin:-1px;overflow:hidden;clip:rect(0, 0, 0, 0);clip-path:inset(50%);white-space:nowrap;border:0';

async function serve(t) {
  let page = '';
  const server = createServer((_, res) => { res.writeHead(200, { 'content-type': 'text/html; charset=utf-8' }); res.end(page); });
  await new Promise(done => server.listen(0, '127.0.0.1', done));
  t.after(() => new Promise(done => { server.closeAllConnections(); server.close(done); }));
  return {
    url: `http://127.0.0.1:${server.address().port}/`,
    setPage(next) { page = next; },
  };
}

async function runScreen(cwd, url, drawingPath = 'screen.ui.svg') {
  const stdout = sink(), stderr = sink();
  const code = await runPdd(['test', '--screen', url, '--drawing', drawingPath, '--json'], {
    cwd,
    env: { ...process.env, PDD_CHROME_PATH: chrome, PDD_RUNTIME_URL: 'invalid-offline', PDD_STATE_DIR: join(cwd, 'state') },
    stdout,
    stderr,
    gh: () => assert.fail('screen comparison must not authenticate'),
    fetch: () => assert.fail('screen comparison must not call the runtime'),
  });
  return { code, stdout: stdout.text, stderr: stderr.text, report: stdout.text ? JSON.parse(stdout.text) : null };
}

test('public CLI replays all 13 pre-code screen-hidden-accessibility cases', { skip: !chrome, timeout: 180000 }, async t => {
  assert.equal(spec.schema_version, 'pdd.native-cases.v1');
  assert.equal(spec.cases.length, 13);
  const cwd = temp(t), host = await serve(t);
  let replayed = 0;
  for (const entry of spec.cases) {
    const drawing = spec.drawings[entry.drawing];
    assert.equal(typeof drawing, 'string', entry.id);
    writeFileSync(join(cwd, 'screen.ui.svg'), drawing);
    const label = entry.sr_style === null ? '' : `<label class="sr-only" style="${entry.sr_style}">Search query</label>`;
    host.setPage(`<!doctype html><style>${baseStyle}</style><div id="search-box"><h1>Search</h1>${label}</div>`);
    const result = await runScreen(cwd, host.url);
    assert.equal(result.code, entry.expected_exit, `${entry.id}: ${result.stderr || result.stdout}`);
    if (Object.hasOwn(entry, 'expected_passed')) {
      assert.equal(result.stderr, '', entry.id);
      assert.equal(result.report.exit_code, entry.expected_exit, entry.id);
      assert.equal(result.report.passed, entry.expected_passed, entry.id);
      assert.deepEqual(result.report.rows.map(({ part, status }) => ({ part, status })), entry.expected_rows, entry.id);
    }
    if (Object.hasOwn(entry, 'expected_stderr')) {
      assert.equal(result.stdout, '', entry.id);
      assert.ok(result.stderr.includes(entry.expected_stderr), `${entry.id}: ${result.stderr}`);
    }
    replayed++;
  }
  assert.equal(replayed, 13);
});

test('public CLI excludes descendant markup and ids inside fully clipped HTML accessibility elements while reporting required clipped ids as hidden', { skip: !chrome, timeout: 180000 }, async t => {
  const cwd = temp(t), host = await serve(t);
  writeFileSync(join(cwd, 'screen.ui.svg'), spec.drawings.base);
  for (const [name, clipCss] of [
    ['descendant markup and unreferenced id', srOnly],
    ['rounded inset', 'position:absolute;left:40px;top:90px;clip-path:inset(50% round 4px)'],
    ['geometry-box inset', 'position:absolute;left:40px;top:90px;clip-path:inset(50%) content-box'],
    ['3-value shorthand inset', 'position:absolute;left:40px;top:90px;clip-path:inset(30% 0px 70%)'],
    ['collapsed rect with auto horizontal bounds', 'position:absolute;left:40px;top:90px;clip:rect(0px, auto, 0px, auto)'],
  ]) {
    host.setPage(`<!doctype html><style>${baseStyle}.sr-only{${clipCss}}</style><div id="search-box" style="padding:22px 0 0 20px;box-sizing:border-box;font:20px sans-serif;color:#0f172a">Search<span class="sr-only"><b>Hidden</b> <i>words</i></span><span id="sr-help" class="sr-only">Help</span></div>`);
    const result = await runScreen(cwd, host.url);
    assert.equal(result.code, 0, `${name}: ${result.stderr || result.stdout}`);
    assert.equal(result.stderr, '', name);
    assert.equal(result.report.passed, true, name);
    assert.deepEqual(result.report.rows.map(({ part, status }) => [part, status]), [['#search-box', 'pass'], ['“Search”', 'pass']], name);
  }

  // Required id on a fully clipped HTML element reports hidden rather than pass or exit 5.
  const requiredIdSvg = spec.drawings.base.replace('</g></svg>', '<rect id="sr-help" x="40" y="90" width="80" height="24" fill="#cbd5e1"/></g></svg>');
  writeFileSync(join(cwd, 'screen.ui.svg'), requiredIdSvg);
  host.setPage(`<!doctype html><style>${baseStyle}.sr-only{${srOnly}}</style><div id="search-box"><h1>Search</h1><span id="sr-help" class="sr-only">Help</span></div>`);
  const hiddenId = await runScreen(cwd, host.url);
  assert.equal(hiddenId.code, 1, hiddenId.stderr || hiddenId.stdout);
  assert.equal(hiddenId.stderr, '');
  assert.equal(hiddenId.report.passed, false);
  assert.deepEqual(hiddenId.report.rows.map(({ part, status }) => [part, status]), [['#search-box', 'pass'], ['“Search”', 'pass'], ['#sr-help', 'hidden']]);

  // Unestablished px-only, calc, negative or ancestor-filter effect chains still exit 5.
  writeFileSync(join(cwd, 'screen.ui.svg'), spec.drawings.base);
  for (const [name, markup] of [
    ['px-only inset', '<span style="position:absolute;left:40px;top:90px;width:10px;height:10px;clip-path:inset(100px)">Help</span>'],
    ['calc inset', '<span style="position:absolute;left:40px;top:90px;width:10px;height:10px;clip-path:inset(calc(50% + 1px))">Help</span>'],
    ['ancestor filter around sr-only', `<div style="filter:blur(1px)"><span style="${srOnly}">Help</span></div>`],
  ]) {
    host.setPage(`<!doctype html><style>${baseStyle}</style><div id="search-box"><h1>Search</h1>${markup}</div>`);
    const rejected = await runScreen(cwd, host.url);
    assert.equal(rejected.code, 5, `${name}: ${rejected.stderr || rejected.stdout}`);
    assert.equal(rejected.stdout, '', name);
    assert.match(rejected.stderr, /Unsupported applied clip-path, clip, mask or filter/, name);
  }
});

test('public CLI treats fully clipped HTML accessibility elements as hidden inside ready Simulator Screen HTML and shadow surfaces while rejecting host and shell clipping', { skip: !chrome, timeout: 180000 }, async t => {
  const cwd = temp(t), host = await serve(t);
  const appContent = `<style>${baseStyle}.sr-inset{position:absolute;width:1px;height:1px;overflow:hidden;clip-path:inset(50%)}.sr-rect{position:absolute;width:1px;height:1px;overflow:hidden;clip:rect(0, 0, 0, 0)}</style><div id="search-box"><h1>Search</h1><label class="sr-inset">Search query</label><span class="sr-rect">Extra help</span></div>`;
  const door = ({ kind, outerCss = '', hostCss = '' }) => {
    const surface = kind === 'html'
      ? `<iframe id="apphost" data-pdd-app-frame="html" style="border:0;width:400px;height:400px;${hostCss}" srcdoc="${appContent.replaceAll('&', '&amp;').replaceAll('"', '&quot;')}"></iframe>`
      : `<div id="apphost" data-pdd-app-frame="shadow" style="position:relative;width:400px;height:400px;${hostCss}"></div>`;
    const attach = kind === 'shadow' ? `<script>document.getElementById('apphost').attachShadow({mode:'open'}).innerHTML=${JSON.stringify(appContent)};</script>` : '';
    return `<!doctype html><html data-pdd-screen-door="1" data-pdd-screen-state="ready"><head><style>body{margin:0}#frame{margin:120px 0 0 16px;${outerCss}}</style></head><body><div id="shell"><div id="search-box">Search query</div></div><div id="frame">${surface}</div>${attach}</body></html>`;
  };

  for (const kind of ['html', 'shadow']) {
    writeFileSync(join(cwd, 'screen.ui.svg'), spec.drawings.base);
    host.setPage(door({ kind }));
    const passed = await runScreen(cwd, host.url);
    assert.equal(passed.code, 0, `${kind}: ${passed.stderr || passed.stdout}`);
    assert.equal(passed.stderr, '', kind);
    assert.equal(passed.report.passed, true, kind);
    assert.deepEqual(passed.report.rows.map(({ part, status }) => [part, status]), [['#search-box', 'pass'], ['“Search”', 'pass']], kind);

    writeFileSync(join(cwd, 'screen.ui.svg'), spec.drawings.required_sr_text);
    const hidden = await runScreen(cwd, host.url);
    assert.equal(hidden.code, 1, `${kind} required sr: ${hidden.stderr || hidden.stdout}`);
    assert.equal(hidden.report.passed, false, kind);
    assert.equal(hidden.report.rows.find(row => row.part === '“Search query”')?.status, 'hidden', kind);
  }

  writeFileSync(join(cwd, 'screen.ui.svg'), spec.drawings.base);
  for (const kind of ['html', 'shadow']) {
    for (const clipCss of ['clip-path:inset(100%)', 'position:absolute;clip:rect(0px,0px,0px,0px)']) {
      for (const [label, opts] of [['host', { kind, hostCss: clipCss }], ['shell #frame', { kind, outerCss: clipCss }]]) {
        host.setPage(door(opts));
        const rejected = await runScreen(cwd, host.url);
        assert.equal(rejected.code, 5, `${kind} ${label} ${clipCss}: ${rejected.stderr || rejected.stdout}`);
        assert.equal(rejected.stdout, '');
        assert.match(rejected.stderr, /Unsupported applied clip-path, clip, mask or filter/);
      }
    }
  }
});
