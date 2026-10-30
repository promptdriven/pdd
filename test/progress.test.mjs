import test from 'node:test';
import assert from 'node:assert/strict';
import { runCheck, runTry } from '../src/runtime-client.mjs';
import { createAgentBridge } from '../src/agent-chat.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { fakeRuntime, harbor, portsFor, sink } from './runtime-fake.mjs';

// A slow server: each job stays queued, then running, for a few reads before it ends.
function slow() {
  const reads = new Map();
  return (entry, f) => {
    if (entry.method === 'POST') return { status: 202, json: f.job(entry.request.requestId, entry.command, 'queued') };
    if (entry.url.endsWith('/tests') || entry.url.endsWith('/approvals')) return { status: 404, json: { error: { code: 'not-found' } } };
    const id = entry.url.split('/').at(-1), count = (reads.get(id) ?? 0) + 1, lint = f.posts.find(post => post.request.requestId === id)?.command === 'lint';
    reads.set(id, count);
    if (count < 12) return { status: 200, json: f.job(id, lint ? 'lint' : 'try', count < 4 ? 'queued' : 'running') };
    return { status: 200, json: lint ? f.lint(id) : f.tryJob(id) };
  };
}
const plain = text => !/[\r\x1b]/.test(text);

// Wrong (Oct 28): pdd try was silent for about a minute while it linted and made the Try.
test('PROGRESS1: a slow lint and Try setup print progress lines on stderr; stdout keeps only the result', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, slow());
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state }, { openUrl: async () => true });
  assert.equal(await runTry({ words: ['place-order'], options: {}, cwd: setup.repo }, ports), 0, ports.stderr.text);
  const err = ports.stderr.text.trimEnd().split('\n');
  assert.ok(err.filter(text => text.endsWith('…')).length >= 2, ports.stderr.text);
  assert.ok(err.some(text => / · \d+ s$/.test(text)), 'a long wait shows the elapsed time');
  assert.ok(plain(ports.stderr.text), 'no spinner or colour codes');
  assert.ok(!ports.stdout.text.includes('…'));
  assert.match(ports.stdout.text.trimEnd().split('\n').at(-1), new RegExp(`${fake.origin}/s/t{43}/`));
});

test('PROGRESS2: check --lint --json keeps one JSON object on stdout while progress goes to stderr', async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, slow());
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  assert.equal(await runCheck({ words: ['place-order'], options: { '--lint': true, '--json': true }, cwd: setup.repo }, ports), 0, ports.stderr.text);
  assert.equal(JSON.parse(ports.stdout.text).exit_code, 0);
  assert.ok(ports.stderr.text.trim().length > 0);
});

// Wrong: a wrong address or no network looked like a lost answer, and pdd read for minutes before "unknown".
test('PROGRESS3: unreachable advisory capacity fails open, then unsent lint stops at once with the cause', async t => {
  const setup = harbor(t);
  const requests = [];
  const fetch = async (url, init = {}) => {
    requests.push({ method: init.method ?? 'GET', path: new URL(url).pathname });
    throw Object.assign(new TypeError('fetch failed'), { cause: { code: 'ENOTFOUND' } });
  };
  const { ports, clock } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: 'https://runtime.invalid', PDD_STATE_DIR: setup.state }, { fetch });
  const started = clock.now;
  assert.equal(await runTry({ words: ['place-order'], options: { '--no-open': true }, cwd: setup.repo }, ports), 5);
  assert.deepEqual(requests, [
    { method: 'GET', path: '/v1/capacity' },
    { method: 'POST', path: '/v1/lint' }
  ]);
  assert.ok(clock.now - started < 5000, 'no wait loop');
  assert.match(ports.stderr.text, /ENOTFOUND/);
  assert.match(ports.stderr.text, /runtime\.invalid/);
});

// Wrong (Oct 28): Codex failed on its own config, the page said "could not answer safely" and the terminal said nothing.
test('PROGRESS4: an agent that cannot answer says why in the terminal', async () => {
  const stderr = sink(), sent = [];
  let polls = 0;
  const send = async (path, init) => {
    sent.push(path);
    if (path.endsWith('/model')) return { status: 200, json: { entries: [] } };
    if (path.endsWith('/agent/connect')) return { status: 200, json: { bridge_id: JSON.parse(init.body).bridge_id, connected: true, browser_key: 'k'.repeat(43) } };
    if (path.includes('/agent/poll')) { polls += 1; return { status: 200, json: { connected: polls < 3, selected: 'codex', message: polls === 1 ? { id: 'm1', text: 'hi', agent: 'codex' } : null } }; }
    return { status: 200, json: { ok: true } };
  };
  const state = {};
  const context = { ports: { stderr, randomUUID: () => 'b1', now: Date.now, sleep: async () => {}, env: {},
    discoverAgents: async () => [{ id: 'codex', name: 'Codex', state: 'ready' }],
    askAgent: async () => ({ say: 'x', fill: null, error: { state: 'error', message: 'Codex could not start: Error loading config.toml' } }) },
    root: '/repo', secrets: [], runtime: { send }, store: { repo: () => state, saveRepo: () => {} } };
  const bridge = await createAgentBridge(context, { story: 's' }, 'try1', { '--agent': 'codex' }, 'https://runtime.example/s/abc/');
  await bridge.run();
  assert.match(stderr.text, /Codex could not answer: Codex could not start: Error loading config\.toml/);
});

test('PROGRESS5: an unexpected workflow error names its real reason', async () => {
  const stderr = sink();
  assert.equal(await runPdd(['workflow', 'status'], { stdout: sink(), stderr, workflowRunner: { runStatus: async () => { throw Error('herdr socket closed'); } } }), 1);
  assert.match(stderr.text, /herdr socket closed/);
});
