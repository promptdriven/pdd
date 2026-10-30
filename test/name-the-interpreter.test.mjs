import test from 'node:test';
import assert from 'node:assert/strict';
import { runPdd } from '../src/pdd-cli.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { runJobs } from '../src/runtime-slots.mjs';
import { fakeRuntime, harbor, portsFor, sink } from './runtime-fake.mjs';

// Rules of user_stories/name-the-interpreter.md for lines that need an interpreter answer: pdd's own
// error, progress and status lines call the hosted service the interpreter. Machine-read words and
// server texts that pdd prints as it got them keep "runtime".
// The last one is this test's own temporary folder name (runtime-fake.mjs), shown in --json `repo`.
const KEEP = [/PDD_RUNTIME_URL/g, /Runtime check\b/g, /[Rr]untime interface/g, /prompt-runtime\.[a-z.-]+/g, /pdd check --read/g, /pdd-runtime-\w+/g];
// `marker` finds the line that the case is about; that line must name the interpreter.
function wordRule(output, marker, serverTexts = []) {
  if (marker) assert.match(output.split('\n').find(line => marker.test(line)) ?? '', /interpreter/, `${marker}: ${output}`);
  let rest = output;
  for (const text of serverTexts) { assert.ok(rest.includes(text), `server text passes through unchanged: ${text}`); rest = rest.split(text).join(''); }
  for (const word of KEEP) rest = rest.replace(word, '');
  assert.match(rest, /interpreter/, output);
  assert.doesNotMatch(rest, /runtime/i, output);
}
const restart = (f, id) => f.job(id, 'check', 'unknown', { why: 'The result is unknown.', refusals: [{ code: 'service-restarted', message: 'The service restarted.' }] }, 'unknown');

const CASES = [
  ['lint progress', (e, f) => f.normal(e), 0, /^Checking \d+ files/],
  ['queue progress', (e, f) => e.command === 'check'
    ? { status: 202, json: { ...f.check(e.request.requestId, 'queued'), queue: { ahead: 2, slots_in_use: 8, slots: 8 } } } : f.normal(e), 0, /2 ahead/],
  ['HTTP 401', (e, f) => e.command === 'lint' ? { status: 401, json: { error: { code: 'auth-required', message: 'no' } } } : f.normal(e), 5, /HTTP 401/],
  ['HTTP 500 with a message', (e, f) => e.command === 'check' ? { status: 500, json: { error: { message: 'boom' } } }
    : e.method === 'GET' ? { status: 404, json: {} } : f.normal(e), 3, /HTTP 500/],
  ['not-invited', () => ({ status: 403, json: { code: 'not-invited', login: 'octo' } }), 5, /invite list/],
  ['no-cloud-access without a server message', () => ({ status: 403, json: { error: { code: 'no-cloud-access' } } }), 5, /Sign up/],
  ['another engine build', (e, f) => { const reply = f.normal(e); reply.json.engine_sha = '7b03d3ea8cc0ffee'; return reply; }, 0, /^Warning: .*engine/],
  ['a confirmed restart', (e, f) => e.command === 'check' ? { status: 200, json: restart(f, e.request.requestId) } : f.normal(e), 3, /sends it again/],
  ['lint problems', (e, f) => e.command === 'lint' ? { status: 200, json: f.lint(e.request.requestId, [], [{ path: 'prompts/place_order.prompt.md', code: 'interface-stale', message: 'stale' }]) } : f.normal(e), null, /^Lint problems/, { '--lint': true }],
];

for (const [name, answer, exit, marker, options = {}] of CASES) test(`interpreter words: ${name}`, async t => {
  const setup = harbor(t), fake = await fakeRuntime(t, answer);
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const code = await runCheck({ words: ['place-order'], cwd: setup.repo, options }, ports);
  if (exit !== null) assert.equal(code, exit, ports.stdout.text + ports.stderr.text);
  wordRule(ports.stdout.text + ports.stderr.text, marker);
});

test('interpreter words: an address that is not reachable, with --json stdout kept apart', async t => {
  const setup = harbor(t);
  const refused = async () => { throw Object.assign(Error('refused'), { cause: { code: 'ECONNREFUSED' } }); };
  for (const options of [{}, { '--json': true }]) {
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, { fetch: refused });
    assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options }, ports), 5, ports.stderr.text);
    wordRule(ports.stdout.text + ports.stderr.text, /could not reach/);
    if (options['--json']) JSON.parse(ports.stdout.text);
  }
});

test('the server gate and server texts keep their words, and pdd still detects the gate', async t => {
  for (const [reply, said] of [[{ status: 503, text: 'The runtime opens soon.' }, 'The runtime opens soon.'],
    [{ status: 429, json: { error: { code: 'other', message: 'The runtime is busy. Try again later.' } } }, 'The runtime is busy. Try again later.']]) {
    const setup = harbor(t), fake = await fakeRuntime(t, (e, f) => e.command === 'check' ? reply : f.normal(e));
    const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
    assert.equal(await runCheck({ words: ['place-order'], cwd: setup.repo, options: {} }, ports), 5);
    assert.equal(fake.posts.filter(entry => entry.command === 'check').length, 1, 'no new attempt after the answer');
    wordRule(ports.stdout.text + ports.stderr.text, null, [said]);
  }
});

test('interpreter words: pdd jobs, an empty list and a list that could not be read', async () => {
  const stdout = sink(), stderr = sink();
  assert.equal(await runJobs({ env: { PDD_STATE_DIR: '/state', PDD_RUNTIME_URL: 'http://127.0.0.1:9' } }, { stdout, stderr, files: { listRecords: () => ({ jobs: [] }) } }), 0);
  assert.equal(stderr.text, ''); wordRule(stdout.text, /jobs/);
  const out = sink(), err = sink();
  assert.equal(await runPdd(['jobs'], { stdout: out, stderr: err, env: {}, runtimeSlots: { runJobs: async () => { throw Error('denied'); } } }), 5);
  assert.equal(out.text, ''); wordRule(err.text, /jobs/);
});
