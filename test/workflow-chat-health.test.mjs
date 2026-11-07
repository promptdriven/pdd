// #2902: the agent stays alive in its pane, but every turn fails on a login error or a usage limit. Status must say that
// the chat cannot work, say how to restart it, and list the run as waiting for the person. pdd only reads: the bottom of
// the screen and the tail of the agent's own session file. It never sends keys or answers to the chat.
import test from 'node:test';
import assert from 'node:assert/strict';
import * as nodeFs from 'node:fs';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runStatus, stepDone } from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

const stateLine = message => message.split('\n').find(line => line.startsWith('State: ')) ?? '';
const nextLine = message => message.split('\n').find(line => line.startsWith('Next: ')) ?? '';
const iso = ms => new Date(ms).toISOString();
// Status may read the chat (agent get, pane read); it never types, pastes, answers or launches.
const READ_ONLY = new Set(['agent get', 'pane read']);
function assertOnlyReads(f, from) {
  const calls = f.herdr.calls.slice(from).map(([group, verb]) => `${group} ${verb}`);
  assert.ok(calls.length > 0, 'status inspected the chat');
  assert.deepEqual(calls.filter(call => !READ_ONLY.has(call)), [], 'status sent nothing to the chat');
}
async function statusAll(f) {
  const ref = '17';
  const detail = await runStatus({ ref, cwd: f.source }, f.ports);
  const list = await runStatus({ all: true, cwd: f.source }, f.ports);
  const json = JSON.parse((await runStatus({ ref, json: true, cwd: f.source }, f.ports)).message).runs[0];
  assert.equal(detail.exitCode, 0); assert.equal(list.exitCode, 0);
  return { detail: detail.message, line: list.message.split('\n').find(l => l.startsWith('example/project#17 ')) ?? '', json };
}

// Claude Code transcript rows, as Claude Code 2.1 writes them.
const claudeRows = {
  user: (text, at) => ({ type: 'user', timestamp: iso(at), message: { role: 'user', content: text } }),
  reply: (text, at) => ({ type: 'assistant', timestamp: iso(at), message: { model: 'claude-opus-4-5', role: 'assistant', content: [{ type: 'text', text }] } }),
  apiError: (error, text, at, extra = {}) => ({ type: 'assistant', isApiErrorMessage: true, error, timestamp: iso(at),
    message: { model: '<synthetic>', role: 'assistant', content: [{ type: 'text', text }] }, ...extra }),
};
const DISABLED_KEY = 'Your ANTHROPIC_API_KEY belongs to a disabled organization · Update or unset the environment variable';
async function claudeChat(t) {
  const f = await fixture(t);
  f.ports.timeZone = 'UTC';
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), chat = run.chats.at(-1), pane = f.herdr.paneOf(chat);
  const file = join(f.ports.env.CLAUDE_CONFIG_DIR, 'projects', run.root.replace(/[^a-zA-Z0-9]/g, '-'), `${chat.session.id}.jsonl`);
  const write = (rows, prefix = '') => { mkdirSync(join(file, '..'), { recursive: true });
    writeFileSync(file, prefix + rows.map(row => JSON.stringify({ sessionId: chat.session.id, cwd: run.root, ...row })).join('\n') + '\n'); };
  // The agent finished its failed turn and waits at its prompt.
  pane.agent.agent_status = 'idle';
  f.tick(60_000);
  return { f, run, chat, pane, write, file };
}

test('claude: every turn fails on a login error, so status says the chat cannot work, how to restart, and that the run waits for you', async t => {
  const { f, chat, write } = await claudeChat(t);
  write([claudeRows.user('Start the plan area.', chat.startedAt + 2000),
    claudeRows.apiError('authentication_failed', DISABLED_KEY, chat.startedAt + 3000, { apiErrorStatus: 401 }),
    claudeRows.user('Please go on.', chat.startedAt + 20_000),
    claudeRows.apiError('authentication_failed', DISABLED_KEY, chat.startedAt + 21_000, { apiErrorStatus: 401 })]);
  const before = f.herdr.calls.length;
  const { detail, line, json } = await statusAll(f);
  assert.match(stateLine(detail), /^State: the chat cannot work: the agent's login failed \(Your ANTHROPIC_API_KEY belongs to a disabled organization/);
  assert.match(stateLine(detail), /pdd workflow open 17 --new/, 'status says how to restart the chat');
  assert.match(nextLine(detail), /pdd workflow open 17 --new/);
  assert.doesNotMatch(detail, /the agent works on/);
  assert.match(line, /^example\/project#17 · small-change · plan · the chat cannot work: the agent's login failed · /);
  assert.equal(json.group, 'waiting', 'the run is listed under "waiting for you"');
  assert.equal(json.words, "the chat cannot work: the agent's login failed");
  assert.deepEqual(json.chatProblem, { kind: 'login', agent: 'claude', until: null, message: DISABLED_KEY });
  assertOnlyReads(f, before);
});

test('claude: a usage limit with a reset time says "usage limit until <time>", also while the limit menu shows', async t => {
  const { f, chat, pane, write } = await claudeChat(t);
  const reset = Date.parse('2026-10-28T15:00:00Z');
  const limit = "You've hit your weekly limit · resets Oct 28 at 3pm (UTC)";
  write([claudeRows.user('Start the plan area.', chat.startedAt + 2000),
    claudeRows.apiError('rate_limit', limit, chat.startedAt + 3000, { apiError: 'usage_limit_reached', apiErrorStatus: 429,
      apiErrorParams: { rate_limit_info: { status: 'rejected', resetsAt: reset / 1000, rateLimitType: 'seven_day' } } })]);
  // Claude Code shows its limit menu, and Herdr reports the agent as blocked. pdd never picks an option.
  pane.agent.agent_status = 'blocked';
  pane.screen = `> Start the plan area.\n  ⎿  ${limit}\n\n What do you want to do?\n\n ❯ 1. Stop and wait for limit to reset\n   2. Wait here, then continue automatically\n\n Enter to confirm · Esc to cancel\n`;
  const before = f.herdr.calls.length;
  const { detail, line, json } = await statusAll(f);
  assert.match(stateLine(detail), /^State: the chat cannot work: usage limit until Oct 28, 15:00\./);
  assert.match(stateLine(detail), /pdd workflow open 17 --new/, 'status says how to restart the chat');
  assert.doesNotMatch(detail, /asks a question in its window|the agent works on/);
  assert.match(line, /^example\/project#17 · small-change · plan · the chat cannot work: usage limit until Oct 28, 15:00 · /);
  assert.equal(json.group, 'waiting');
  assert.deepEqual(json.chatProblem, { kind: 'usage-limit', agent: 'claude', until: '2026-10-28T15:00:00.000Z', message: limit });
  assertOnlyReads(f, before);
  // After the reset time the limit is over, but the chat still waits for the person to ask it to go on.
  f.clock = Date.parse('2026-10-28T16:00:00Z');
  const later = await statusAll(f);
  assert.match(stateLine(later.detail), /^State: the chat stopped at its usage limit\. The limit reset at Oct 28, 15:00\./);
  assert.match(stateLine(later.detail), /pdd workflow open 17\b/);
  assert.equal(later.json.group, 'waiting');
});

test('claude: without a transcript, the failed turn or the limit menu on the screen counts', async t => {
  const { f, pane } = await claudeChat(t);
  pane.screen = `> Start the plan area.\n  ⎿  ${DISABLED_KEY}\n\n╭──────────────────╮\n│ >                │\n╰──────────────────╯\n  ⏵⏵ bypass permissions on\n`;
  let shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /^State: the chat cannot work: the agent's login failed \(Your ANTHROPIC_API_KEY belongs to a disabled organization/);
  assert.equal(shown.json.group, 'waiting');
  pane.agent.agent_status = 'blocked';
  pane.screen = "> Start the plan area.\n  ⎿  You've hit your weekly limit · resets Oct 28 at 3pm (UTC)\n\n What do you want to do?\n\n ❯ 1. Stop and wait for limit to reset\n   2. Wait here, then continue automatically\n\n Enter to confirm · Esc to cancel\n";
  const before = f.herdr.calls.length;
  shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /^State: the chat cannot work: usage limit until Oct 28 at 3pm \(UTC\)\./);
  assert.match(shown.line, / · the chat cannot work: usage limit until Oct 28 at 3pm \(UTC\) · /);
  assertOnlyReads(f, before);
  // The person chose "Wait here, then continue automatically": after the limit, the agent went on in the same turn.
  pane.agent.agent_status = 'idle';
  pane.screen = "> Start the plan area.\n  ⎿  You've hit your session limit · resets 7pm (UTC)\n\n⏺ The limit is over. I go on with the plan.\n\n> \n";
  shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: the agent works on scope');
  // An agent reply that quotes such a line is not an error of the chat.
  pane.screen = "⏺ The issue says Claude Code showed:\n  You've hit your weekly limit · resets Nov 6 at 3pm\n\n> \n";
  shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: the agent works on scope');
});

test('claude: only the tail of a long transcript is read', async t => {
  const { f, chat, write } = await claudeChat(t);
  // About 6 MB of earlier work, then a turn that fails on the login.
  const filler = `${JSON.stringify({ sessionId: chat.session.id, ...claudeRows.reply('x'.repeat(2000), chat.startedAt + 1000) })}\n`.repeat(3000);
  write([claudeRows.user('Please go on.', chat.startedAt + 20_000),
    claudeRows.apiError('authentication_failed', 'Not logged in · Please run /login', chat.startedAt + 21_000)], filler);
  let bytes = 0;
  f.ports.sessionFs = { ...nodeFs, readSync: (...args) => { const n = nodeFs.readSync(...args); bytes += n; return n; } };
  const status = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.match(stateLine(status.message), /^State: the chat cannot work: the agent's login failed \(Not logged in · Please run \/login\)/);
  assert.ok(bytes > 0 && bytes <= 256 * 1024, `status read ${bytes} bytes of a ${filler.length}-byte transcript`);
});

test('claude: a healthy chat keeps its status words', async t => {
  const { f, chat, pane, write } = await claudeChat(t);
  // An earlier turn failed on the login; the person signed in, and the next turn worked.
  write([claudeRows.user('Start the plan area.', chat.startedAt + 2000),
    claudeRows.apiError('authentication_failed', 'Not logged in · Please run /login', chat.startedAt + 3000),
    claudeRows.user('Please go on.', chat.startedAt + 20_000),
    claudeRows.reply('I read the issue. Next I write the plan.', chat.startedAt + 25_000)]);
  // The screen still shows the old error line above the later work.
  pane.screen = '> Start the plan area.\n  ⎿  Not logged in · Please run /login\n\n> Please go on.\n\n⏺ I read the issue. Next I write the plan.\n\n> \n';
  let shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: the agent works on scope');
  assert.match(shown.line, / · agent working on scope · /);
  assert.equal(shown.json.group, 'working');
  assert.equal(shown.json.chatProblem, undefined);
  // The person asked again after a failed turn, and the agent works on it now.
  write([claudeRows.user('Start the plan area.', chat.startedAt + 2000),
    claudeRows.apiError('rate_limit', "You've hit your session limit · resets 7pm (UTC)", chat.startedAt + 3000),
    claudeRows.user('Please go on.', chat.startedAt + 40_000)]);
  pane.agent.agent_status = 'working';
  shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: the agent works on scope');
  // No transcript at all, and an ordinary screen: nothing changes.
  nodeFs.rmSync(join(f.ports.env.CLAUDE_CONFIG_DIR, 'projects'), { recursive: true, force: true });
  pane.agent.agent_status = 'idle'; pane.screen = '⏺ I wrote the plan.\n\n> \n';
  shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: the agent works on scope');
});

test('claude: a gate keeps its words even when the chat cannot work', async t => {
  const { f, run, write } = await claudeChat(t);
  f.tick(); assert.equal((await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts())).exitCode, 0);
  f.herdr.idle(); f.tick();
  write([claudeRows.user('Please go on.', f.clock - 500), claudeRows.apiError('authentication_failed', DISABLED_KEY, f.clock - 400)]);
  const { detail } = await statusAll(f);
  assert.match(stateLine(detail), /^State: waiting for you: approve the plan area/);
});

// Codex shows a failed turn as an error line that starts with "■". Its session file keeps the user message, not the error.
async function codexChat(t) {
  const f = await fixture(t, { agent: 'codex' });
  const home = join(f.base, 'codexhome'); mkdirSync(home); f.ports.env.CODEX_HOME = home;
  f.ports.timeZone = 'UTC';
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), pane = f.herdr.paneOf(run.chats.at(-1));
  // A Codex thread id is a UUIDv7: its first 48 bits are the session start in milliseconds.
  const started = f.clock, hex = started.toString(16).padStart(12, '0');
  const id = `${hex.slice(0, 8)}-${hex.slice(8, 12)}-7abc-8def-0123456789ab`;
  pane.agent.agent_session.value = id;
  pane.agent.agent_status = 'idle';
  const day = new Date(started), folder = join(home, 'sessions', String(day.getFullYear()), String(day.getMonth() + 1).padStart(2, '0'), String(day.getDate()).padStart(2, '0'));
  const file = join(folder, `rollout-2026-10-27T17-00-00-${id}.jsonl`);
  const write = rows => { mkdirSync(folder, { recursive: true });
    writeFileSync(file, [{ timestamp: iso(started), type: 'session_meta', payload: { id, cwd: run.root, timestamp: iso(started) } }, ...rows].map(row => JSON.stringify(row)).join('\n') + '\n'); };
  f.tick(60_000);
  return { f, run, pane, id, write };
}
const codexRows = {
  user: (text, at) => ({ timestamp: iso(at), type: 'event_msg', payload: { type: 'user_message', message: text } }),
  reply: (text, at) => ({ timestamp: iso(at), type: 'event_msg', payload: { type: 'agent_message', message: text } }),
  tokens: (rateLimits, at) => ({ timestamp: iso(at), type: 'event_msg', payload: { type: 'token_count', info: null, rate_limits: rateLimits } }),
};
// A long error line wraps; its reset time is on the next screen line.
const CODEX_LIMIT = "■ You've hit your usage limit. Upgrade to Pro (https://chatgpt.com/explore/pro)\n  or try again at 4:17 PM.";
const codexScreen = body =>`› Start the build area.\n\n${body}\n\n› Ask Codex to do anything\n\n  ? for shortcuts                                    100% context left\n`;

test('codex: a usage limit on the screen says "usage limit until <time>" and how to restart, also on another account', async t => {
  const { f, pane, write } = await codexChat(t);
  write([codexRows.user('Start the build area.', f.clock - 50_000)]);
  pane.screen = codexScreen(CODEX_LIMIT);
  const before = f.herdr.calls.length;
  const { detail, line, json } = await statusAll(f);
  assert.match(stateLine(detail), /^State: the chat cannot work: usage limit until 4:17 PM\./);
  assert.match(stateLine(detail), /pdd workflow open 17 --new/);
  assert.match(stateLine(detail), /CODEX_HOME=<folder> pdd workflow open 17 --new/, 'a Codex run can move to another account');
  assert.match(line, / · the chat cannot work: usage limit until 4:17 PM · /);
  assert.equal(json.group, 'waiting');
  assert.equal(json.chatProblem.kind, 'usage-limit');
  assertOnlyReads(f, before);
});

test('codex: its session file says the account reached its limit, with the time the limit ends', async t => {
  const { f, pane, write } = await codexChat(t);
  const ends = Date.parse('2026-10-27T21:30:00Z');
  write([codexRows.user('Start the build area.', f.clock - 50_000), codexRows.reply('I start with the tests.', f.clock - 40_000),
    codexRows.tokens({ limit_id: 'codex', primary: { used_percent: 100, window_minutes: 300, resets_at: ends / 1000 }, secondary: null,
      credits: { has_credits: false, unlimited: false, balance: '0' }, plan_type: 'plus', rate_limit_reached_type: 'primary' }, f.clock - 39_000)]);
  pane.screen = codexScreen('• I start with the tests.');
  const { detail, json } = await statusAll(f);
  assert.match(stateLine(detail), /^State: the chat cannot work: usage limit until Oct 27, 21:30\./);
  assert.equal(json.chatProblem.until, '2026-10-27T21:30:00.000Z');
});

test('codex: a 401 on the screen says the login failed', async t => {
  const { f, pane } = await codexChat(t);
  pane.screen = codexScreen('■ unexpected status 401 Unauthorized: Your access token could not be refreshed. Please log out and sign in again.');
  const { detail, line, json } = await statusAll(f);
  assert.match(stateLine(detail), /^State: the chat cannot work: the agent's login failed \(unexpected status 401 Unauthorized/);
  assert.match(stateLine(detail), /pdd workflow open 17 --new/);
  assert.match(line, / · the chat cannot work: the agent's login failed · /);
  assert.equal(json.group, 'waiting');
});

test('codex: a healthy chat keeps its status words', async t => {
  const { f, pane, write } = await codexChat(t);
  // The limit error is old: a later turn worked (the agent replied after it on the screen).
  pane.screen = codexScreen(`${CODEX_LIMIT}\n\n› Please go on.\n\n• The tests pass now.`);
  let shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: the agent works on scope');
  assert.equal(shown.json.group, 'working');
  // The session file shows that the newest turn got a reply, so an old error line on the screen does not count.
  write([codexRows.user('Start the build area.', f.clock - 50_000), codexRows.reply('The tests pass now.', f.clock - 40_000),
    codexRows.tokens({ primary: { used_percent: 100, window_minutes: 10080, resets_at: (f.clock + 3_600_000) / 1000 }, secondary: null,
      credits: { has_credits: true, unlimited: false, balance: '400' }, rate_limit_reached_type: null }, f.clock - 39_000)]);
  pane.screen = codexScreen(CODEX_LIMIT);
  shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: the agent works on scope', 'a full window with credits left is no limit');
  // The agent works now: pdd does not judge it by the screen.
  write([codexRows.user('Please go on.', f.clock - 1000)]);
  pane.agent.agent_status = 'working';
  shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: the agent works on scope');
});
