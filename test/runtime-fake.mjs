import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { createServer } from 'node:http';
import { cpSync, mkdirSync, mkdtempSync, readdirSync, realpathSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

// Shared helpers for the runtime client tests: a Harbor repo, a fake runtime on 127.0.0.1 and in-process ports.
export const root = fileURLToPath(new URL('..', import.meta.url));
export const TOKEN = 'gho_TESTTOKEN_never_print_7f3a';
export const PLACE = 'prompts/place_order.prompt.md';
export const temp = t => { const p = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-runtime-'))); t.after(() => rmSync(p, { recursive: true, force: true })); return p; };
const git = (cwd, ...args) => { const r = spawnSync('git', args, { cwd, encoding: 'utf8' }); assert.equal(r.status, 0, r.stderr); };
export const sink = () => ({ text: '', write(value) { this.text += value; return true; } });
export const sha = bytes => createHash('sha256').update(bytes).digest('hex');
export const filesUnder = dir => readdirSync(dir, { recursive: true }).map(name => join(dir, name));

export function harbor(t, edit) {
  const sandbox = temp(t), repo = join(sandbox, 'repo'), home = join(sandbox, 'home');
  cpSync(join(root, 'test/fixtures/harbor'), repo, { recursive: true }); mkdirSync(home);
  edit?.(repo);
  git(repo, 'init', '-q'); git(repo, 'add', '-A'); git(repo, '-c', 'user.email=t@example.com', '-c', 'user.name=t', 'commit', '-qm', 'init');
  return { sandbox, repo, home, state: join(sandbox, 'state') };
}

const usage = calls => ({ calls, model: 'unknown', requested_model: calls ? 'gpt-6.1-sol' : 'unknown', seconds: 10.4686, input_tokens: calls ? 6835 : 'unknown', output_tokens: calls ? 110 : 'unknown' });
const PASSED_CHECKS = [{ criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true }];

// A fake PDD runtime on 127.0.0.1. `answer(entry, fake)` returns {status, json | text, headers} or {destroy: true}.
export async function fakeRuntime(t, answer) {
  const fake = { posts: [], jsonPosts: [], gets: [], deletes: [], authorization: new Set(), jobs: new Map() };
  const server = createServer(async (req, res) => {
    const chunks = [];
    for await (const chunk of req) chunks.push(chunk);
    const body = Buffer.concat(chunks), entry = { method: req.method, url: req.url, headers: req.headers };
    fake.authorization.add(req.headers.authorization);
    if (req.method === 'POST' && String(req.headers['content-type']).startsWith('application/json')) {
      entry.json = JSON.parse(body.toString('utf8'));
      fake.jsonPosts.push(entry);
    } else if (req.method === 'POST') {
      const form = await new Request('http://fake/', { method: 'POST', headers: { 'content-type': req.headers['content-type'] }, body }).formData();
      entry.request = JSON.parse(await form.get('request').text());
      entry.tar = Buffer.from(await form.get('source').arrayBuffer());
      entry.command = req.url.split('/').at(-1);
      fake.posts.push(entry);
    } else (req.method === 'GET' ? fake.gets : fake.deletes).push(entry);
    const reply = await answer(entry, fake);
    if (reply.destroy) { req.socket.destroy(); return; }
    res.writeHead(reply.status, { 'content-type': reply.text === undefined ? 'application/json' : 'text/plain', ...reply.headers });
    res.end(reply.text ?? JSON.stringify(reply.json));
  });
  await new Promise(done => server.listen(0, '127.0.0.1', done));
  t.after(() => { server.closeAllConnections(); server.close(); });
  fake.origin = `http://127.0.0.1:${server.address().port}`;
  fake.job = (id, command, state, result = null, calls = 0) => ({ requestId: id, id, command, state, engine_sha: 'eae2202a68d00ab762fcbbf1eba0d8607a132a15',
    result, usage: usage(calls), report_url: `${fake.origin}/r/${createHash('md5').update(id).digest('hex')}` });
  fake.lint = (id, prompts = [{ path: PLACE, state: 'approved', admission_state: 'approved', interface: { calls: [] } }], refused = []) =>
    fake.job(id, 'lint', 'passed', { exitCode: 0, refusals: [], report: { verdict: 'passed', program: { prompts, refused_prompts: refused } } });
  fake.check = (id, state = 'passed', checks = PASSED_CHECKS, refusals = []) => fake.job(id, 'check', state, ['queued', 'running'].includes(state) ? null
    : { exitCode: state === 'passed' ? 0 : 1, outcome: state === 'passed' ? 'Pass' : 'Fail', refusals, who: null, why: state === 'passed' ? 'All checked criteria passed.' : 'Checks failed.',
      next_step: null, report: { samples: [{ sample: 1, steps: [{ checks }] }], evaluation: { requested_model: 'gpt-6.1-sol' },
        criterion_results: [...new Set(checks.map(check => check.criterion_id))].map(id => ({ criterion_id: id, status: checks.every(check => check.criterion_id !== id || check.passed) ? 'passed' : 'failed' })) } },
    state === 'refused' ? 0 : 1);
  fake.tryJob = (id, url = `${fake.origin}/s/${'t'.repeat(43)}/`, session = 'running') => fake.job(id, 'try', 'passed',
    { exitCode: 0, refusals: [], url, session: { id, state: session, tab: 'call', max_calls: 40, remaining_calls: 40 } });
  fake.stopJob = (id, tryId) => fake.job(id, 'stop', 'passed', { exitCode: 0, refusals: [], output: 'Try stopped. Saved results can be replayed.', session: { id: tryId, state: 'stopped' } });
  // The usual server: lint passes at once; checks are queued, then pass on the first read.
  fake.normal = entry => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId) };
    if (entry.method === 'POST') return { status: 202, json: fake.check(entry.request.requestId, 'queued') };
    const id = entry.url.split('/').at(-1);
    return { status: 200, json: fake.check(id) };
  };
  return fake;
}

// In-process ports: a fake clock (sleep moves time), a fake gh and spies on IDs and interrupts.
export function portsFor(env, extra = {}) {
  const clock = { now: Date.parse('2026-10-27T16:27:47Z'), uuids: 0, gh: [] };
  const ports = { env, stdout: sink(), stderr: sink(), pollMs: 2000, interactive: false,
    now: () => clock.now, sleep: async ms => { clock.now += ms; await new Promise(done => setImmediate(done)); },
    randomUUID: () => { clock.uuids += 1; return randomUUID(); },
    gh: args => { clock.gh.push(args); return args[0] === 'auth' ? { status: 0, stdout: `${TOKEN}\n` } : { status: 0, stdout: 'octo 4242\n' }; },
    onInterrupt: handler => { clock.interrupt = handler; return () => { clock.interrupt = null; }; }, ...extra };
  return { ports, clock };
}

