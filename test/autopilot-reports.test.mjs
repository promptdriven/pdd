import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, rmSync, writeFileSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileReport, listReportDrafts, sendReportDraft } from '../src/autopilot-reports.mjs';

// A synthetic source line and private prose: neither may reach a public GitHub write.
const SOURCE = 'const confidentialCustomerDiscount = 0.37; // synthetic source';
const PROSE = 'Customer Acme Corp asked for the private pricing rule';
const versions = { pdd: '0.1.28', node: 'v22.23.2', platform: 'darwin', agent: 'codex' };

function folder(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-reports-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  return root;
}
// A fake GitHub REST API: every repository is readable, no report exists yet, and every write is captured.
function fakeGithub({ readable = true } = {}) {
  const writes = [];
  const reply = (status, value) => ({ code: 0, stdout: `HTTP/1.1 ${status} OK\r\n\r\n${value === undefined ? '' : JSON.stringify(value)}`, stderr: '' });
  const gh = async (args, options = {}) => {
    const method = args[args.indexOf('--method') + 1], endpoint = args.find(arg => arg.startsWith('repos/'));
    if (method === 'GET' && /^repos\/[^/]+\/[^/]+$/.test(endpoint)) return readable ? reply(200, { full_name: endpoint.slice(6) }) : reply(404, {});
    if (method === 'GET') return reply(200, []);
    writes.push({ method, endpoint, body: options.input ?? '' });
    return reply(201, { number: 501, id: 9501 });
  };
  return { gh, writes };
}
const publicText = writes => writes.map(write => write.body).join('\n');

// Wrong: a public report carries free-form detail (a source line or private prose) from the agent's result.
test('a filed report holds only fixed fields; the detail stays out of every public write', async t => {
  for (const kind of ['pdd', 'runtime']) {
    const root = folder(t), fake = fakeGithub();
    const cause = { kind, component: 'pdd test', code: kind === 'runtime' ? 'no-verdict' : 'cli-error', text: PROSE, detail: `${SOURCE}\n${PROSE}` };
    const sent = await fileReport({ cause, mode: 'file', root, machine: 'm', versions, step: 'build' }, { gh: fake.gh, now: () => 0 });
    assert.equal(sent.state, 'filed');
    const posted = publicText(fake.writes);
    assert.doesNotMatch(posted, /confidentialCustomerDiscount|synthetic source|Acme|private pricing/);
    const issue = JSON.parse(fake.writes.find(write => write.endpoint.endsWith('/issues')).body);
    for (const field of ['Kind:', 'Component:', 'Error code:', 'Step: build', 'Versions: PDD 0.1.28', 'Seen on this machine: 1', '<!-- pdd:autopilot-report:'])
      assert.ok(issue.body.includes(field), field);
  }
});

// Wrong: draft mode, or a send of a draft (also one written before this rule), posts the local detail.
test('a draft keeps the detail locally, and sending it, also an older draft, posts no detail', async t => {
  const root = folder(t), fake = fakeGithub();
  const cause = { kind: 'pdd', component: 'pdd', code: 'crash', text: PROSE, detail: SOURCE };
  const kept = await fileReport({ cause, mode: 'draft', root, machine: 'm', versions, step: 'build' }, { gh: fake.gh, now: () => 0 });
  assert.equal(kept.state, 'draft');
  assert.deepEqual(fake.writes, [], 'draft mode writes nothing to GitHub');
  const [draft] = listReportDrafts({ root });
  assert.match(draft.detail, /confidentialCustomerDiscount/, 'the operator keeps the detail on this machine');
  assert.doesNotMatch(draft.body, /confidentialCustomerDiscount|Acme/);
  assert.equal((await sendReportDraft({ root, fingerprint: draft.fingerprint, machine: 'm' }, { gh: fake.gh, now: () => 0 })).exitCode, 0);
  assert.doesNotMatch(publicText(fake.writes), /confidentialCustomerDiscount|synthetic source|Acme|private pricing/);

  // A resumed draft from before this rule: its body and title carry the detail; the send builds them again.
  const older = fakeGithub(), fingerprint = 'pdd.pdd.crash.0.1';
  mkdirSync(join(root, 'drafts'), { recursive: true });
  writeFileSync(join(root, 'drafts', `${fingerprint}.json`), JSON.stringify({ fingerprint, kind: 'pdd', repository: 'promptdriven/pdd',
    title: `Autopilot report: ${SOURCE}`, body: `Redacted detail:\n${SOURCE}\n${PROSE}\n<!-- pdd:autopilot-report:${fingerprint} -->`,
    labels: ['pdd:autopilot-report'], assignees: ['someone'], count: 2, firstAt: 0, lastAt: 0 }));
  assert.equal((await sendReportDraft({ root, fingerprint, machine: 'm' }, { gh: older.gh, now: () => 0 })).exitCode, 0);
  const issue = JSON.parse(older.writes.find(write => write.endpoint.endsWith('/issues')).body);
  assert.doesNotMatch(publicText(older.writes), /confidentialCustomerDiscount|synthetic source|Acme|private pricing/);
  assert.match(issue.body, /Error code: crash/); assert.match(issue.body, /Seen on this machine: 2/);
  assert.deepEqual(issue.assignees, [], 'an older draft keeps no assignee of its own');
});

// Wrong: the product assigns a named person, or a configured owner where that owner was not configured.
test('a report has no assignee unless the operator configures a Runtime owner for the Runtime repository', async t => {
  const cause = { kind: 'runtime', component: 'pdd test', code: 'interpreter-error', text: 'x' };
  const assigned = async (options, readable = true) => {
    const root = folder(t), fake = fakeGithub({ readable });
    await fileReport({ cause, mode: 'file', root, machine: 'm', versions, step: 'build', ...options }, { gh: fake.gh, now: () => 0 });
    const issue = fake.writes.find(write => write.endpoint.endsWith('/issues'));
    return { endpoint: issue.endpoint, assignees: JSON.parse(issue.body).assignees };
  };
  assert.deepEqual(await assigned({}), { endpoint: 'repos/promptdriven/pdd/issues', assignees: [] });
  assert.deepEqual(await assigned({ runtimeRepo: 'acme/runtime' }), { endpoint: 'repos/acme/runtime/issues', assignees: [] });
  assert.deepEqual(await assigned({ runtimeRepo: 'acme/runtime', runtimeOwner: 'dana-ops' }), { endpoint: 'repos/acme/runtime/issues', assignees: ['dana-ops'] });
  assert.deepEqual(await assigned({ runtimeRepo: 'acme/runtime', runtimeOwner: 'dana-ops' }, false), { endpoint: 'repos/promptdriven/pdd/issues', assignees: [] },
    'the owner is for the configured Runtime repository only');
  assert.deepEqual(await assigned({ runtimeOwner: 'not a login!' }), { endpoint: 'repos/promptdriven/pdd/issues', assignees: [] });
  const pdd = folder(t), fake = fakeGithub();
  await fileReport({ cause: { kind: 'pdd', component: 'pdd', code: 'crash', text: 'x' }, mode: 'file', root: pdd, machine: 'm', versions, runtimeRepo: 'acme/runtime', runtimeOwner: 'dana-ops' }, { gh: fake.gh, now: () => 0 });
  assert.deepEqual(JSON.parse(fake.writes.find(write => write.endpoint.endsWith('/issues')).body).assignees, [], 'a PDD report is never assigned');

  // A draft carries the configured owner to a later send.
  const root = folder(t), later = fakeGithub();
  await fileReport({ cause, mode: 'draft', root, machine: 'm', versions, runtimeRepo: 'acme/runtime', runtimeOwner: 'dana-ops' }, { gh: later.gh, now: () => 0 });
  const [draft] = listReportDrafts({ root });
  assert.equal(draft.runtimeOwner, 'dana-ops');
  await sendReportDraft({ root, fingerprint: draft.fingerprint, machine: 'm' }, { gh: later.gh, now: () => 0 });
  assert.deepEqual(JSON.parse(later.writes.find(write => write.endpoint.endsWith('/issues')).body).assignees, ['dana-ops']);
  assert.doesNotMatch(readFileSync(new URL('../src/autopilot-reports.mjs', import.meta.url), 'utf8'), /agarwal/i, 'the product names no person');
});
