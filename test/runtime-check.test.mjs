import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { captureSource, proseSha256, storyCriteria, tarFiles } from '../src/runtime-preflight.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { renderSessionIntro } from '../src/session-intro.mjs';

const root = fileURLToPath(new URL('..', import.meta.url));
const HARBOR = join(root, 'test/fixtures/harbor');
const GOLDEN = 'd5958a8577dcb8dd6ff25c8df4ea3b85e8c5dcf7c16863d8e502a24095db6abb';
const temp = t => { const p = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-runtime-'))); t.after(() => rmSync(p, { recursive: true, force: true })); return p; };
const git = (cwd, ...args) => { const r = spawnSync('git', args, { cwd, encoding: 'utf8' }); assert.equal(r.status, 0, r.stderr); return r.stdout; };
const sink = () => ({ text: '', write(value) { this.text += value; return true; } });
const readJson = path => JSON.parse(readFileSync(path, 'utf8'));
const writeJson = (path, value) => writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`);

// A Harbor Coffee repo in a temp folder: committed prompt, two stories, two tests.
function harbor(t) {
  const sandbox = temp(t), repo = join(sandbox, 'repo'), home = join(sandbox, 'home');
  cpSync(HARBOR, repo, { recursive: true }); mkdirSync(home);
  git(repo, 'init', '-q'); git(repo, 'add', '-A'); git(repo, '-c', 'user.email=t@example.com', '-c', 'user.name=t', 'commit', '-qm', 'init');
  return { sandbox, repo, home };
}

// Ports that fail the test if anything reaches the network or gh.
function offline(home) {
  const calls = { fetch: 0, gh: 0 };
  const ports = { env: { HOME: home, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, stdout: sink(), stderr: sink(),
    fetch: async () => { calls.fetch += 1; throw Error('network'); }, gh: () => { calls.gh += 1; return { status: 1, stdout: '' }; } };
  return { ports, calls };
}

async function check(repo, home, words = [], options = { '--json': true }) {
  const { ports, calls } = offline(home);
  const code = await runCheck({ words, options, cwd: repo }, ports);
  return { code, calls, out: ports.stdout.text, err: ports.stderr.text, json: options['--json'] && ports.stdout.text ? JSON.parse(ports.stdout.text) : null };
}

// Wrong: pdd hashes the prose differently from the engine, so every approved prompt looks stale.
test('RUNTIME-HASH1: the prose hash of the Harbor prompt equals the engine golden value', () => {
  assert.equal(proseSha256(readFileSync(join(HARBOR, 'prompts/place_order.prompt.md'), 'utf8')), GOLDEN);
});

// Wrong: --fill-hash rewrites other bytes, touches approved prompts or hides a stale approval.
test('RUNTIME-HASH2: --fill-hash fills a draft, keeps approved prompts and exits 4 on approved-stale', async t => {
  const { repo, home } = harbor(t), file = join(repo, 'prompts/place_order.prompt.md'), approved = readFileSync(file, 'utf8');
  const draft = approved.replace('"status": "approved"', '"status": "draft"').replace(GOLDEN, '');
  writeFileSync(file, draft);
  let result = await check(repo, home, [], { '--fill-hash': true });
  assert.equal(result.code, 0, result.err);
  assert.match(result.out, /Filled prose_sha256: prompts\/place_order\.prompt\.md/);
  assert.equal(readFileSync(file, 'utf8'), draft.replace('"prose_sha256": ""', `"prose_sha256": "${GOLDEN}"`));
  assert.deepEqual(result.calls, { fetch: 0, gh: 0 });
  writeFileSync(file, approved);
  result = await check(repo, home, [], { '--fill-hash': true });
  assert.equal(result.code, 0); assert.equal(readFileSync(file, 'utf8'), approved); assert.match(result.out, /1 current/);
  const stale = approved.replace('Use this menu.', 'Use this menu now.');
  writeFileSync(file, stale);
  result = await check(repo, home, [], { '--fill-hash': true });
  assert.equal(result.code, 4); assert.equal(readFileSync(file, 'utf8'), stale);
  assert.match(result.out, /the text changed after approval: set status to draft, run pdd check --fill-hash, ask the person/);
  writeFileSync(file, draft.replace('"prose_sha256": "",\n', ''));
  result = await check(repo, home, [], { '--fill-hash': true });
  assert.equal(result.code, 4); assert.match(result.out, /Add "prose_sha256": ""/);
});

// Wrong: pdd reads story criteria differently from the engine, so P5 refuses tests the engine accepts.
test('RUNTIME-STORY1: story criteria equal the engine for numbered, continued, bullet and odd lists', () => {
  const cases = readJson(join(root, 'test/fixtures/story-criteria.engine-7b03d3ea.json'));
  assert.ok(cases.length >= 20);
  for (const { source, expected } of cases) assert.deepEqual(storyCriteria(source), expected, JSON.stringify(source));
});

const RULES = [
  ['P1 bad JSON', 'invalid-document', r => writeFileSync(join(r, 'tests/place-order.json'), '{"schema_version": "prompt-runtime.program-scenario.v1",')],
  ['P1 extra key', 'invalid-document', (r, doc) => { doc.notes = 'x'; }],
  ['P1 version', 'invalid-document', (r, doc) => { doc.schema_version = 'prompt-runtime.program-scenario.v2'; }],
  ['P2 no story', 'pdd-no-story', (r, doc) => { delete doc.story_path; }],
  ['P2 story missing', 'story-missing', (r, doc) => { doc.story_path = 'user_stories/gone.md'; }],
  ['P3 scope', 'pdd-partial-test', (r, doc) => { doc.criteria_scope = ['ac-1']; }],
  ['P3 exemptions', 'pdd-partial-test', (r, doc) => { doc.check_exemptions = [{ criterion_id: 'AC1', reason: 'out-of-scope', detail: 'x' }]; }],
  ['P4 no criteria', 'story-criteria-missing', r => writeFileSync(join(r, 'user_stories/place-order.md'), '# Place a coffee order\n\nNo list.\n')],
  ['P5 mismatch', 'story-criterion-mismatch', (r, doc) => { doc.criteria[1].text = 'The order keeps the name.'; }],
  ['P6 duplicate', 'duplicate-criterion', (r, doc) => { doc.criteria[1].id = 'AC1'; }],
  ['P6 unchecked', 'unchecked-criteria', (r, doc) => { doc.steps[0].checks = doc.steps[0].checks.filter(c => c.criterion_id !== 'AC2'); }],
  ['P6 inexact', 'criterion-needs-exact-check', (r, doc) => {
    doc.steps[0].checks = [...doc.steps[0].checks.filter(c => c.criterion_id !== 'AC2'), { criterion_id: 'AC2', target: 'result', path: '/customerName', op: 'exists' }]; }],
  ['P7 entry missing', 'entry-missing', (r, doc) => { doc.steps[0].entry_path = 'prompts/gone.prompt.md'; }],
  ['P7 no interface', 'interface-missing', r => writeFileSync(join(r, 'prompts/place_order.prompt.md'), '# Place an order\n')],
  ['P7 two interfaces', 'pdd-two-interfaces', r => { const f = join(r, 'prompts/place_order.prompt.md'), s = readFileSync(f, 'utf8'); writeFileSync(f, s + s.slice(s.indexOf('<details>'))); }],
  ['P7 draft', 'interface-unapproved', r => { const f = join(r, 'prompts/place_order.prompt.md'); writeFileSync(f, readFileSync(f, 'utf8').replace('"approved"', '"draft"')); }],
  ['P7 stale', 'interface-stale', r => { const f = join(r, 'prompts/place_order.prompt.md'); writeFileSync(f, readFileSync(f, 'utf8').replace('Use this menu.', 'Use this menu now.')); }],
  ['P8 operation', 'entry-operation-missing', (r, doc) => { doc.steps[0].operation = 'cancel_order'; }],
  ['P9 input', 'invalid-input', (r, doc) => { doc.steps[0].input.items[0].quantity = 0; }],
  ['P10 unknown error', 'pdd-unknown-error', (r, doc) => { doc.steps[0].expected_error = 'sold-out'; doc.steps[0].checks.push({ criterion_id: 'AC1', target: 'error', path: '/code', op: 'equals', value: 'sold-out' }); }],
  ['P10 error check', 'missing-error-check', (r, doc) => { doc.steps[0].expected_error = 'unknown-item'; }],
  ['P11 two tests', 'pdd-story-has-two-tests', r => cpSync(join(r, 'tests/place-order.json'), join(r, 'tests/place-order-2.json'))],
];

// Wrong: a broken test reaches the server, or the refusal does not name the rule that broke.
test('RUNTIME-RULES1: each rule P1-P11 refuses with its code and nothing is sent', async t => {
  for (const [name, code, edit] of RULES) {
    const { repo, home } = harbor(t), file = join(repo, 'tests/place-order.json'), doc = readJson(file);
    if (edit(repo, doc) === undefined && edit.length === 2) writeJson(file, doc);
    const result = await check(repo, home, [name.startsWith('P11') ? 'tests/place-order.json' : 'place-order']);
    assert.equal(result.code, 4, `${name}: ${result.err}`);
    assert.deepEqual(result.calls, { fetch: 0, gh: 0 }, name);
    assert.equal(result.json.rows[0].state, 'refused', name);
    assert.equal(result.json.rows[0].refusals[0].code, code, name);
  }
});

// Wrong: the person reads a rule code with no field and no allowed range (RESULT.md issues 4, 5, 6).
test('RUNTIME-RULES2: quantity 0 gives the exact field and rule; the number warning names the text', async t => {
  const { repo, home } = harbor(t), file = join(repo, 'tests/place-order.json'), doc = readJson(file);
  doc.steps[0].input.items[0].quantity = 0;
  doc.steps[0].checks[0].value = 899;
  writeJson(file, doc);
  const result = await check(repo, home, ['place-order'], {});
  assert.equal(result.code, 4);
  assert.equal(result.out.split('\n').filter(Boolean).slice(2, 5).join('\n'), ['REFUSED before sending (not sent, 0 AI calls)',
    '  tests/place-order.json  step 1  invalid-input', '  steps[0] input /items/0/quantity is 0. The prompt allows 1 to 20.'].join('\n'));
  assert.match(result.out, /Warning: the AC1 check expects 899, but the AC1 text says 900\./);
  const prompt = join(repo, 'prompts/place_order.prompt.md');
  writeFileSync(prompt, readFileSync(prompt, 'utf8').replace('"approved"', '"draft"'));
  const unapproved = await check(repo, home, ['unknown-item'], {});
  assert.equal(unapproved.code, 4); assert.deepEqual(unapproved.calls, { fetch: 0, gh: 0 });
  assert.match(unapproved.out, /pdd: prompts\/place_order\.prompt\.md is "draft"\. The person must approve it first\./);
});

// Wrong: an unknown story sends every test, or the error hides the stories that exist.
test('RUNTIME-SELECT1: STORY is a story name, story path or test path; unknown words exit 2 with the list', async t => {
  const { repo, home } = harbor(t), file = join(repo, 'tests/place-order.json'), doc = readJson(file);
  doc.steps[0].input.items[0].quantity = 0; writeJson(file, doc);
  for (const word of ['place-order', 'user_stories/place-order.md', 'tests/place-order.json', './tests/place-order.json']) {
    const result = await check(repo, home, [word]);
    assert.equal(result.code, 4, word); assert.deepEqual(result.json.rows.map(row => row.test), ['tests/place-order.json'], word);
  }
  const fromSub = await runCheck({ words: ['../tests/place-order.json'], options: { '--json': true }, cwd: join(repo, 'prompts') }, offline(home).ports);
  assert.equal(fromSub, 4);
  const unknown = await check(repo, home, ['nope'], {});
  assert.equal(unknown.code, 2); assert.equal(unknown.out, '');
  assert.match(unknown.err, /Unknown story "nope"/); assert.match(unknown.err, /place-order {2}tests\/place-order\.json/); assert.match(unknown.err, /unknown-item/);
  const outside = await check(temp(t), home, []);
  assert.equal(outside.code, 2);
});

// Wrong: a secret, a link or a huge repo goes up, or the tar changes between runs (one source_sha256 per batch).
test('RUNTIME-CAPTURE1: capture refuses secrets, links and size limits, and makes the same tar bytes twice', async t => {
  const { repo, home } = harbor(t);
  const first = captureSource(repo), second = captureSource(repo);
  assert.ok(first.tar.equals(second.tar)); assert.equal(first.sha256, second.sha256);
  assert.deepEqual(first.files.map(file => file.path), ['README.md', 'prompts/place_order.prompt.md', 'tests/place-order.json',
    'tests/unknown-item.json', 'user_stories/place-order.md', 'user_stories/unknown-item.md']);
  const listed = await check(repo, home, [], { '--files': true });
  assert.equal(listed.code, 0); assert.match(listed.out, /^6 files, \d+ KB\. 1 of them are not prompt, story or test files\.$/m);
  for (const [name, setup, pattern] of [
    ['secret', r => writeFileSync(join(r, '.env.local'), 'TOKEN=x\n'), /\.env\.local: the name looks like a secret/],
    ['secret folder', r => { mkdirSync(join(r, 'config/secrets'), { recursive: true }); writeFileSync(join(r, 'config/secrets/a.txt'), 'x'); }, /config\/secrets\/a\.txt/],
    ['symlink', r => symlinkSync('README.md', join(r, 'link.md')), /link\.md: a symbolic link/],
    ['size', r => writeFileSync(join(r, 'big.bin'), Buffer.alloc(10_485_761)), /too big to send: 7 files, 10\.0 MB[\s\S]*big\.bin/],
    ['count', r => { mkdirSync(join(r, 'many')); for (let i = 0; i < 10_000; i += 1) writeFileSync(join(r, 'many', `${i}.txt`), ''); }, /too big to send: 10006 files/],
  ]) {
    const copy = harbor(t);
    setup(copy.repo);
    const result = await check(copy.repo, copy.home, ['place-order'], {});
    assert.equal(result.code, 4, name); assert.match(result.err, pattern, name); assert.deepEqual(result.calls, { fetch: 0, gh: 0 }, name);
    assert.equal((await check(copy.repo, copy.home, [], { '--files': true })).code, 4, name);
  }
});

// Wrong: the tar has local owners, times or modes, or long and non-ASCII names break on the server.
test('RUNTIME-CAPTURE2: the Node tar is plain ustar that system tar reads, with PAX paths for long names', t => {
  const dir = temp(t), long = `${'deep/'.repeat(22)}file.txt`;
  const tar = tarFiles([{ path: 'a.txt', bytes: Buffer.from('A\n') }, { path: long, bytes: Buffer.from('long\n') }, { path: 'café.md', bytes: Buffer.from('é\n') }]);
  assert.equal(tar.length % 512, 0);
  const header = tar.subarray(0, 512), field = (start, length) => header.subarray(start, start + length).toString('latin1').replace(/\0.*$/s, '');
  assert.deepEqual([field(0, 100), field(100, 8), field(108, 8), field(116, 8), field(136, 12), field(257, 6), field(265, 32)],
    ['a.txt', '0000600', '0000000', '0000000', '00000000000', 'ustar', '']);
  writeFileSync(join(dir, 'x.tar'), tar); mkdirSync(join(dir, 'out'));
  const extracted = spawnSync('tar', ['-xf', join(dir, 'x.tar'), '-C', join(dir, 'out')], { encoding: 'utf8' });
  assert.equal(extracted.status, 0, extracted.stderr);
  assert.equal(readFileSync(join(dir, 'out', long), 'utf8'), 'long\n');
  assert.equal(readFileSync(join(dir, 'out', 'café.md'), 'utf8'), 'é\n');
  assert.equal(readFileSync(join(dir, 'out', 'a.txt'), 'utf8'), 'A\n');
});

// Wrong: the state folder is inside the repo, so run state (and report links) could be committed.
test('RUNTIME-STATE1: a state folder inside the repo is refused before any work', async t => {
  const { repo, home } = harbor(t), { ports, calls } = offline(home);
  ports.env.PDD_STATE_DIR = join(repo, '.pdd-state');
  assert.equal(await runCheck({ words: [], options: {}, cwd: repo }, ports), 2);
  assert.match(ports.stderr.text, /inside this repository/); assert.deepEqual(calls, { fetch: 0, gh: 0 });
});

// Wrong: the CLI routes break, show the hidden option, or accept values outside the ranges.
test('RUNTIME-CLI1: check and try help, option ranges and option mixes', t => {
  const { repo, home } = harbor(t), env = { ...process.env, HOME: home, PDD_RUNTIME_URL: 'http://127.0.0.1:9' };
  delete env.CLAUDE_CONFIG_DIR;
  const pdd = (...args) => spawnSync(process.execPath, [join(root, 'bin/pdd.mjs'), ...args], { cwd: repo, env, encoding: 'utf8', timeout: 20000 });
  const help = pdd('check', '--help');
  assert.equal(help.status, 0); assert.match(help.stdout, /pdd check --fill-hash/); assert.match(help.stdout, /pdd check --read \[BATCH\]/);
  assert.doesNotMatch(help.stdout, /--request/);
  assert.match(pdd('try', '--help').stdout, /pdd try --stop \[STORY\]/);
  assert.doesNotMatch(pdd('completion', 'bash').stdout, /--request/);
  for (const args of [['check', '--max-calls', '0'], ['check', '--max-calls', '101'], ['check', '--timeout', 'x'], ['try', '--tab', 'phone'],
    ['check', '--request', 'nope'], ['check', '--fill-hash', '--json'], ['check', '--files', 'place-order'], ['check', '--read', 'a', 'b'],
    ['try', '--stop', '--new'], ['try', 'a', 'b']]) {
    const result = pdd(...args);
    assert.equal(result.status, 2, `${args.join(' ')}: ${result.stdout}${result.stderr}`); assert.equal(result.stdout, '', args.join(' '));
  }
  const filled = pdd('check', '--fill-hash');
  assert.equal(filled.status, 0, filled.stderr); assert.match(filled.stdout, /Hashes: 0 filled, 1 current/);
});

// Wrong: the package has no runbook, so the intro and check steps never mention pdd check, or the runbook names commands pdd refuses.
test('RUNTIME-RUNBOOK1: the package ships RUNBOOK.md, the intro names it, and its commands parse', () => {
  const runbook = readFileSync(join(root, 'RUNBOOK.md'), 'utf8');
  assert.ok(readJson(join(root, 'package.json')).files.includes('RUNBOOK.md'));
  const intro = renderSessionIntro({ packageRoot: root, cwd: '/work/project' }).split('\n');
  assert.ok(intro.includes(`Runtime: read ${join(root, 'RUNBOOK.md')} before you run a check.`));
  const commands = [...runbook.matchAll(/`?(pdd (?:check|try)[^`#\n]*?)\s*(?:`|#|\n)/g)].map(match => match[1].trim());
  assert.ok(commands.length >= 6, commands.join(' | '));
  for (const command of commands) assert.doesNotThrow(() => parseArgv(command.split(/\s+/).slice(1)), command);
});
