// #2902: the agent stays alive in its pane, but every turn fails on a login error or a usage limit. Status must say that
// the chat cannot work, say how to restart it, and list the run as waiting for the person. pdd only reads: the bottom of
// the screen and the tail of the agent's own session file. It never sends keys or answers to the chat.
import test from 'node:test';
import assert from 'node:assert/strict';
import * as nodeFs from 'node:fs';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { chatHealth } from '../src/workflow-chat.mjs';
import { runStatus, stepDone } from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

const stateLine = message => message.split('\n').find(line => line.startsWith('State: ')) ?? '';
const nextLine = message => message.split('\n').find(line => line.startsWith('Next: ')) ?? '';
const iso = ms => new Date(ms).toISOString();
// Status may read the chat (agent get, pane read); it never types, pastes, answers or launches.
const READ_ONLY = new Set(['agent get', 'pane read', 'pane list', 'workspace list']);
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
  assert.match(stateLine(detail), /Sign the agent in again \(\/login in the chat, or fix its API key\)/, 'status says where to sign in');
  assert.match(nextLine(detail), /pdd workflow open 17 --new/);
  assert.doesNotMatch(detail, /the agent works on/);
  assert.match(line, /^example\/project#17 · small-change · plan · the chat cannot work: the agent's login failed · /);
  assert.equal(json.group, 'waiting', 'the run is listed under "waiting for you"');
  assert.equal(json.words, "the chat cannot work: the agent's login failed");
  assert.deepEqual(json.chatProblem, { kind: 'login', agent: 'claude', until: null, message: DISABLED_KEY });
  const saved = f.record();
  saved.chats.at(-1).evidence = { kind: 'pane-exit' };
  writeFileSync(join(f.git(f.source, 'rev-parse', '--path-format=absolute', '--git-common-dir'), 'pdd', 'runs', '17', 'status.json'), JSON.stringify(saved));
  const versioned = await runStatus({ cwd: f.source, all: true, json: true }, f.ports);
  assert.deepEqual(JSON.parse(versioned.message).runs[0].waiting, {kind:'chat_stopped', gate:null, question:null, reason:'unknown'});
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
  assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/);
  // An agent reply that quotes such a line is not an error of the chat.
  pane.screen = "⏺ The issue says Claude Code showed:\n  You've hit your weekly limit · resets Nov 6 at 3pm\n\n> \n";
  shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/);
});

test('claude: without a transcript, status keeps only the limit sentence and the reset time of the limit block, never the lines under it', async t => {
  const { f, pane } = await claudeChat(t);
  // Claude Code 2.1 draws its limit block in one column under "  ⎿  ": the limit line, then dim lines such as an offer
  // (the texts below are from its offer table) or a key hint. In a narrow pane the limit line wraps onto the next line.
  const limit = "You've hit your weekly limit · resets Nov 6 at 3pm (America/Los_Angeles)", until = ' until Nov 6 at 3pm (America/Los_Angeles)';
  const blocks = {
    'an upgrade or usage-credits offer': [`  ⎿  ${limit}\n     /upgrade or /usage-credits to finish what you’re working on.`, until, limit],
    'an API billing offer': [`  ⎿  ${limit}\n     /login to switch to an API usage-billed account.`, until, limit],
    'a key hint, then an offer': [`  ⎿  ${limit}\n     Press Enter to continue after reset\n     /upgrade to increase your usage limit.`, until, limit],
    'a wrapped limit line, then an offer': ["  ⎿  You've hit your weekly limit · resets Nov 6 at\n     3pm (America/Los_Angeles)\n     /usage-credits to finish what you’re working on.", until, limit],
    'no reset time, then an admin offer': ["  ⎿  You've hit your weekly limit\n     Your admin can enable extra usage at https://example.test/admin.", '', "You've hit your weekly limit"],
  };
  for (const [name, [block, words, message]] of Object.entries(blocks)) {
    pane.screen = `> Start the plan area.\n${block}\n\n╭──────────────────╮\n│ >                │\n╰──────────────────╯\n  ⏵⏵ bypass permissions on\n`;
    const before = f.herdr.calls.length;
    const { detail, line, json } = await statusAll(f);
    assert.equal(stateLine(detail).split('. ')[0], `State: the chat cannot work: usage limit${words}`, name);
    assert.match(stateLine(detail), / open the chat and ask it to go on: pdd workflow open 17\. /, name);
    assert.ok(line.includes(` · the chat cannot work: usage limit${words} · `), `${name}: ${line}`);
    assert.equal(json.chatProblem.message, message, name);
    // pdd's own status never passes on the agent's offers or key hints.
    for (const text of [detail, line, JSON.stringify(json)]) assert.doesNotMatch(text, /\/upgrade|\/usage-credits|usage-billed|\/login to switch|Press Enter|extra usage/, name);
    assertOnlyReads(f, before);
  }
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
  assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/);
  assert.match(shown.line, / · agent idle since \d{2}:\d{2} · /);
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
  assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/);
});

test('claude: a gate keeps its words even when the chat cannot work', async t => {
  const { f, run, write } = await claudeChat(t);
  f.tick(); assert.equal((await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts())).exitCode, 0);
  f.herdr.idle(); f.tick();
  write([claudeRows.user('Please go on.', f.clock - 500), claudeRows.apiError('authentication_failed', DISABLED_KEY, f.clock - 400)]);
  const { detail } = await statusAll(f);
  assert.match(stateLine(detail), /^State: waiting for you: approve the plan area/);
});

test('claude: a healthy chat that quotes an error line or the limit menu keeps its status words', async t => {
  const { f, pane } = await claudeChat(t);
  // No transcript, so only the screen counts. Claude draws its own error line right under the user's prompt line; the
  // same "  ⎿  " line under a reply or a tool call is quoted text or a tool result.
  const screens = {
    'a reply quotes the limit line': "> Start the plan area.\n\n⏺ The issue says Claude Code showed:\n  ⎿  You've hit your weekly limit · resets Nov 6 at 3pm\n\n> \n",
    'a reply quotes the login line further down': "> Start the plan area.\n\n⏺ I found the cause.\n  The screen showed:\n  ⎿  Not logged in · Please run /login\n  I fix the check now.\n\n> \n",
    'a reply quotes the limit menu': "> Start the plan area.\n\n⏺ The issue shows the limit menu:\n  ❯ 1. Stop and wait for limit to reset\n    2. Wait here, then continue automatically\n\n> \n",
  };
  for (const [name, screen] of Object.entries(screens)) {
    pane.screen = screen;
    const shown = await statusAll(f);
    assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/, name);
    assert.equal(shown.json.chatProblem, undefined, name);
  }
  // A tool result with a 401 above a real question dialog: the dialog keeps its words.
  pane.agent.agent_status = 'blocked';
  pane.screen = "> Check the PR.\n\n⏺ Bash(gh pr view 12)\n  ⎿  Error: gh: HTTP 401: Bad credentials\n\n Do you want to proceed?\n ❯ 1. Yes\n   2. No\n\n Esc to cancel\n";
  const shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: waiting for you: the chat asks a question in its window (pdd workflow open 17)');
});

// Codex rollout rows, in the shapes that Codex 0.159 to 0.167 writes (copied from real local rollouts; the texts, ids and
// paths are replaced, and fields that do not matter here are left out). Each turn starts with task_started and ends with
// task_complete; a failed turn keeps its error there.
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
  let ordinal = 0;
  const row = (at, type, payload) => ({ timestamp: iso(at), ordinal: ordinal++, type, payload });
  const turnId = n => `${hex.slice(0, 8)}-${hex.slice(8, 12)}-7000-8000-${String(n).padStart(12, '0')}`, seconds = at => Math.floor(at / 1000);
  const rows = {
    // The person's message starts a turn.
    start: (n, text, at) => [
      row(at, 'event_msg', { type: 'task_started', turn_id: turnId(n), root_turn_id: turnId(n), started_at: seconds(at), model_context_window: 258400, collaboration_mode_kind: 'default' }),
      row(at, 'response_item', { type: 'message', id: `msg_user_${n}`, role: 'user', content: [{ type: 'input_text', text }] }),
      row(at, 'turn_context', { turn_id: turnId(n), root_turn_id: turnId(n), cwd: run.root, workspace_roots: [run.root], approval_policy: 'never', sandbox_policy: { type: 'danger-full-access' }, model: 'gpt-test' }),
      row(at, 'event_msg', { type: 'item_completed', thread_id: id, turn_id: turnId(n), item: { type: 'UserMessage', id: `item_user_${n}`, content: [{ type: 'text', text, text_elements: [] }] }, started_at_ms: at, completed_at_ms: at })],
    reply: (n, text, at) => [
      row(at, 'event_msg', { type: 'item_completed', thread_id: id, turn_id: turnId(n), item: { type: 'AgentMessage', id: `item_agent_${n}`, content: [{ type: 'Text', text }], phase: 'final_answer' }, started_at_ms: at, completed_at_ms: at }),
      row(at, 'response_item', { type: 'message', id: `msg_agent_${n}`, role: 'assistant', content: [{ type: 'output_text', text }] })],
    // At a real usage limit, the rate-limit windows are empty: this row does not show the limit.
    tokens: at => row(at, 'event_msg', { type: 'token_count', info: null, rate_limits: { limit_id: 'premium', limit_name: null, primary: null, secondary: null,
      credits: { has_credits: false, unlimited: false, balance: '0' }, plan_type: null, rate_limit_reached_type: null } }),
    end: (n, at, startedAt, { reply = null, error } = {}) => row(at, 'event_msg', { type: 'task_complete', turn_id: turnId(n), last_agent_message: reply,
      ...(error ? { error } : {}), started_at: seconds(startedAt), completed_at: seconds(at), duration_ms: at - startedAt }),
    // The person stopped the turn (Esc).
    aborted: (n, at, startedAt) => row(at, 'event_msg', { type: 'turn_aborted', turn_id: turnId(n), reason: 'interrupted', started_at: seconds(startedAt), completed_at: seconds(at), duration_ms: at - startedAt }),
  };
  const write = list => { mkdirSync(folder, { recursive: true });
    const meta = row(started, 'session_meta', { session_id: id, id, timestamp: iso(started), cwd: run.root, originator: 'codex-tui', cli_version: '0.167.0', source: 'cli', model_provider: 'openai' });
    writeFileSync(file, [meta, ...list.flat()].map(item => JSON.stringify(item)).join('\n') + '\n'); };
  f.tick(60_000);
  return { f, run, pane, id, rows, write };
}
// Codex draws its own error line with "■ " at column 0. A long one wraps; its reset time is on the next screen line.
const CODEX_LIMIT = "■ You've hit your usage limit. More about your plan at https://example.test/limits\n  or try again at 4:17 PM.";
const codexScreen = body =>`› Start the build area.\n\n${body}\n\n› Ask Codex to do anything\n\n  ? for shortcuts                                    100% context left\n`;
// The real error texts, with the address, the middle of the limit text and the request id replaced.
const CODEX_ERRORS = {
  limit: { message: 'You’ve hit your usage limit. More at https://example.test/limits or try again at Nov 3rd, 2026 10:35 PM.', codex_error_info: 'usage_limit_exceeded' },
  unauthorized: { message: 'unexpected status 401 Unauthorized: Missing bearer or basic authentication in header, url: https://example.test/v1/responses, request id: req_0000', codex_error_info: { http_connection_failed: { http_status_code: 401 } } },
  refresh: { message: "Failed to refresh token: 400 Bad Request: Invalid 'refresh_token': empty string.", codex_error_info: 'other' },
  overloaded: { message: 'Selected model is at capacity. Please try a different model.', codex_error_info: 'server_overloaded' },
};
const paneReads = (f, from) => f.herdr.calls.slice(from).filter(([group, verb]) => group === 'pane' && verb === 'read').length;

test('codex: without its session file, a usage limit on the screen says "usage limit until <time>" and how to restart, also on another account', async t => {
  const { f, pane } = await codexChat(t);
  pane.screen = codexScreen(CODEX_LIMIT);
  const before = f.herdr.calls.length;
  const { detail, line, json } = await statusAll(f);
  assert.match(stateLine(detail), /^State: the chat cannot work: usage limit until 4:17 PM\./);
  assert.match(stateLine(detail), /pdd workflow open 17 --new/);
  assert.match(stateLine(detail), /CODEX_HOME=<folder> pdd workflow open 17 --new/, 'a Codex run can move to another account');
  assert.match(line, / · the chat cannot work: usage limit until 4:17 PM · /);
  assert.equal(json.group, 'waiting');
  assert.equal(json.chatProblem.kind, 'usage-limit');
  assert.equal(json.chatProblem.message, "You've hit your usage limit.", 'pdd does not repeat the rest of the limit text');
  assertOnlyReads(f, before);
});

test('codex: its session file says the newest turn failed at the usage limit, with the time Codex names', async t => {
  const { f, pane, rows, write } = await codexChat(t);
  const at = f.clock - 50_000;
  write([rows.start(1, 'Start the build area.', at), rows.tokens(at + 900), rows.end(1, at + 1900, at, { error: CODEX_ERRORS.limit })]);
  // The error line is no longer on the screen: the file decides, and pdd does not read the screen.
  pane.screen = '› Ask Codex to do anything\n';
  const before = f.herdr.calls.length;
  const { detail, line, json } = await statusAll(f);
  assert.match(stateLine(detail), /^State: the chat cannot work: usage limit until Nov 3rd, 2026 10:35 PM\./);
  assert.match(line, / · the chat cannot work: usage limit until Nov 3rd, 2026 10:35 PM · /);
  assert.equal(json.group, 'waiting');
  assert.deepEqual(json.chatProblem, { kind: 'usage-limit', agent: 'codex', until: null, message: 'You’ve hit your usage limit.' });
  assertOnlyReads(f, before);
  assert.equal(paneReads(f, before), 0, 'the session file decided');
});

test('codex: its session file says the newest turn failed on the login (a 401, or a failed token refresh)', async t => {
  const { f, pane, rows, write } = await codexChat(t);
  const at = f.clock - 50_000;
  pane.screen = '› Ask Codex to do anything\n';
  write([rows.start(1, 'Start the build area.', at), rows.reply(1, 'I start with the tests.', at + 5000), rows.end(1, at + 6000, at, { reply: 'I start with the tests.' }),
    rows.start(2, 'Please go on.', at + 20_000), rows.end(2, at + 36_000, at + 20_000, { error: CODEX_ERRORS.unauthorized })]);
  const before = f.herdr.calls.length;
  let shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /^State: the chat cannot work: the agent's login failed \(unexpected status 401 Unauthorized: Missing bearer/);
  assert.match(stateLine(shown.detail), /Sign the agent in again \(codex login with this run's CODEX_HOME\), then start a new chat for this area: pdd workflow open 17 --new$/);
  assert.match(nextLine(shown.detail), /pdd workflow open 17 --new/);
  assert.match(shown.line, / · the chat cannot work: the agent's login failed · /);
  assert.equal(shown.json.group, 'waiting');
  assert.equal(shown.json.chatProblem.kind, 'login');
  assertOnlyReads(f, before);
  assert.equal(paneReads(f, before), 0, 'the session file decided');
  write([rows.start(1, 'Start the build area.', at), rows.end(1, at + 2000, at, { error: CODEX_ERRORS.refresh })]);
  shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /^State: the chat cannot work: the agent's login failed \(Failed to refresh token/);
  // Another error of the newest turn is no login or limit problem.
  write([rows.start(1, 'Start the build area.', at), rows.end(1, at + 2000, at, { error: CODEX_ERRORS.overloaded })]);
  shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/);
});

test('codex: after the reset time that Codex names, status says that the limit reset', async t => {
  const { f, pane, rows, write } = await codexChat(t);
  pane.screen = '› Ask Codex to do anything\n';
  const at = f.clock - 50_000, limitAt = time => ({ ...CODEX_ERRORS.limit, message: `You’ve hit your usage limit. More at https://example.test/limits or try again at ${time}.` });
  // Codex writes the local time of its own process (UTC here). It leaves out the date when the limit ends on the day of
  // the failed turn.
  write([rows.start(1, 'Start the build area.', at), rows.end(1, at + 1900, at, { error: limitAt('9:40 PM') })]);
  f.clock = Date.parse('2026-10-27T21:00:00Z');
  let shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /^State: the chat cannot work: usage limit until 9:40 PM\. After that time, /);
  f.clock = Date.parse('2026-10-27T22:00:00Z');
  shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /^State: the chat stopped at its usage limit\. The limit reset at 9:40 PM\. Open the chat and ask it to go on: pdd workflow open 17\./);
  assert.match(shown.line, / · the chat stopped at its usage limit \(reset at 9:40 PM\) · /);
  assert.equal(shown.json.group, 'waiting');
  // A limit that ends on a later day: Codex names the date.
  write([rows.start(1, 'Start the build area.', at), rows.end(1, at + 1900, at, { error: CODEX_ERRORS.limit })]);
  f.clock = Date.parse('2026-11-04T09:00:00Z');
  shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /^State: the chat stopped at its usage limit\. The limit reset at Nov 3rd, 2026 10:35 PM\. /);
  assert.match(nextLine(shown.detail), /pdd workflow open 17$/);
  assert.doesNotMatch(shown.detail, /until Nov 3rd/);
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

test('codex: a chat whose newest turn worked keeps its status words, also when the screen still shows an old error line', async t => {
  const { f, pane, rows, write } = await codexChat(t);
  const at = f.clock - 50_000;
  // The first turn failed at the limit; after the limit, the person asked again and the turn worked.
  write([rows.start(1, 'Start the build area.', at), rows.tokens(at + 900), rows.end(1, at + 1900, at, { error: CODEX_ERRORS.limit }),
    rows.start(2, 'Please go on.', at + 20_000), rows.reply(2, 'The tests pass now.', at + 30_000), rows.end(2, at + 31_000, at + 20_000, { reply: 'The tests pass now.' })]);
  pane.screen = codexScreen(`${CODEX_LIMIT}\n\n› Please go on.\n\n• The tests pass now.`);
  const before = f.herdr.calls.length;
  let shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/);
  assert.equal(shown.json.group, 'working');
  assert.equal(shown.json.chatProblem, undefined);
  assert.equal(paneReads(f, before), 0, 'the session file decided');
  // The file says the newest turn worked, so an error line on the screen does not count.
  pane.screen = codexScreen(CODEX_LIMIT);
  shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/);
  // A new turn has started: the file gives no answer. The agent works now, so pdd does not judge it by the screen.
  write([rows.start(1, 'Start the build area.', at), rows.end(1, at + 1900, at, { error: CODEX_ERRORS.limit }), rows.start(2, 'Please go on.', f.clock - 1000)]);
  pane.agent.agent_status = 'working';
  shown = await statusAll(f);
  assert.equal(stateLine(shown.detail), 'State: the agent works on scope');
});

test('codex: without its session file, an old error line above a later prompt keeps its status words', async t => {
  const { f, pane } = await codexChat(t);
  // No session file, so only the screen counts. The limit error is old: the person asked again later.
  const screens = {
    'the agent replied to the later prompt': `${CODEX_LIMIT}\n\n› Please go on.\n\n• The tests pass now.`,
    'the person stopped the later turn': `${CODEX_LIMIT}\n\n› Please go on.\n\n■ Conversation interrupted - use /feedback if something went wrong`,
  };
  for (const [name, body] of Object.entries(screens)) {
    pane.screen = codexScreen(body);
    const before = f.herdr.calls.length;
    const shown = await statusAll(f);
    assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/, name);
    assert.equal(shown.json.group, 'working', name);
    assert.equal(shown.json.chatProblem, undefined, name);
    assert.ok(paneReads(f, before) > 0, `${name}: the screen decided`);
  }
});

test('codex: a turn that the person stopped after a failed turn clears the old error', async t => {
  const { f, pane, rows, write } = await codexChat(t);
  const at = f.clock - 50_000;
  // The first turn failed at the limit. Later the person asked again and stopped that turn: Codex writes turn_aborted.
  write([rows.start(1, 'Start the build area.', at), rows.end(1, at + 1900, at, { error: CODEX_ERRORS.limit }),
    rows.start(2, 'Please go on.', at + 20_000), rows.aborted(2, at + 25_000, at + 20_000)]);
  pane.screen = codexScreen(`${CODEX_LIMIT}\n\n› Please go on.\n\n■ Conversation interrupted - use /feedback if something went wrong`);
  const before = f.herdr.calls.length;
  const shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/);
  assert.equal(shown.json.chatProblem, undefined);
  assert.equal(paneReads(f, before), 0, 'the session file decided');
});

test('codex: a healthy chat that quotes an error line in its reply keeps its status words', async t => {
  const { f, pane, rows, write } = await codexChat(t);
  // No session file, so only the screen counts. Codex indents the lines of a reply under its "•" line, so an indented
  // "■" line is quoted text, not the agent's own error line.
  const quotes = [
    "• The issue shows this screen:\n  ■ You've hit your usage limit. Try again at 4:17 PM.\n  I add a check for it now.",
    '• The log has this line:\n\n  ■ unexpected status 401 Unauthorized\n\n  I keep the old token check.',
  ];
  for (const quote of quotes) {
    pane.screen = codexScreen(quote);
    const shown = await statusAll(f);
    assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/, quote);
    assert.equal(shown.json.chatProblem, undefined, quote);
  }
  // With its session file, the newest turn that worked decides before the screen.
  const at = f.clock - 50_000;
  write([rows.start(1, 'Start the build area.', at), rows.reply(1, 'I add a check for it now.', at + 5000), rows.end(1, at + 6000, at, { reply: 'I add a check for it now.' })]);
  const before = f.herdr.calls.length;
  const shown = await statusAll(f);
  assert.match(stateLine(shown.detail), /idle since \d{2}:\d{2}/);
  assert.equal(paneReads(f, before), 0, 'the session file decided');
});

for (const [words, now, expected] of [
  ['Nov 1, 2026 at 2:30am', '2026-11-01T10:00:00Z', '2026-11-01T10:30:00Z'],
  ['Mar 8, 2026 at 3:30am', '2026-03-08T10:45:00Z', '2026-03-08T10:30:00Z'],
  ['Nov 1, 2026 at 1:30am', '2026-11-01T10:00:00Z', null],
  ['Mar 8, 2026 at 2:30am', '2026-03-08T10:45:00Z', null],
]) test(`reset local time round trip: ${words}`, async t => {
  const { f, run, chat, pane } = await claudeChat(t);
  f.clock = Date.parse('2026-11-02T10:00:00Z');
  pane.screen = `> Continue\n  ⎿  You've hit your weekly limit · resets Nov 2, 2026 at 2:30am (America/Los_Angeles)\n\n> \n`;
  const control = await chatHealth({ run, chat, live: { alive: true, status: 'idle' } }, f.ports);
  assert.equal(control?.resetsAt, Date.parse('2026-11-02T10:30:00Z'));
  f.clock = Date.parse(now);
  pane.screen = `> Continue\n  ⎿  You've hit your weekly limit · resets ${words} (America/Los_Angeles)\n\n> \n`;
  const health = await chatHealth({ run, chat, live: { alive: true, status: 'idle' } }, f.ports);
  assert.equal(health?.kind, 'usage-limit');
  assert.equal(health.resetsAt, expected === null ? null : Date.parse(expected));
  const shown = await statusAll(f);
  assert.equal(shown.json.group, 'waiting');
  if (expected !== null) {
    const state = stateLine(shown.detail);
    assert.equal(/limit reset at/i.test(state), Date.parse(expected) < f.clock);
    assert.equal(/until/i.test(state), Date.parse(expected) > f.clock);
  }
});

test('Gemini startup warns about unattended shell safety stops', async t => {
  const f = await fixture(t, { agent: 'gemini' });
  const started = await f.run();
  assert.match(started.message, /Gemini.*shell safety dialogs.*--yolo.*person.*unattended/i);
});

test('Gemini shell safety dialog appears in status without answering it', async t => {
  const f = await fixture(t, { agent: 'gemini' });
  await f.run();
  const pane = f.herdr.paneOf(f.record().chats.at(-1));
  pane.agent.agent_status = 'blocked';
  for (const heading of ['CRITICAL SECURITY WARNING: Untrusted Command Flags Detected', 'CAUTION: Build Configuration Was Recently Modified']) {
    pane.screen = `⚠ ${heading}\nThe command needs confirmation.\nAllow execution of [Shell]?\n● 1. Allow once\n  2. No, suggest changes (esc)\n`;
    const before = f.herdr.calls.length;
    const shown = await statusAll(f);
    for (const words of [shown.detail, shown.line, shown.json.words]) assert.match(words, /Gemini shell-safety dialog.*pdd workflow open 17/);
    assert.equal(shown.json.group, 'waiting');
    assertOnlyReads(f, before);
  }
  pane.screen = 'Other question\n(Use Enter to select)\n';
  assert.match((await statusAll(f)).detail, /the chat asks a question in its window/);
});


test('Gemini shell safety status names the menu when the second choice is selected', async t => {
  const f = await fixture(t, { agent: 'gemini' });
  await f.run();
  const pane = f.herdr.paneOf(f.record().chats.at(-1));
  pane.agent.agent_status = 'blocked';
  const menu = '⚠ CRITICAL SECURITY WARNING: Untrusted Command Flags Detected\nAllow execution of [Shell]?\n  1. Allow once\n● 2. No, suggest changes (esc)\n';
  for (const footer of ['', '(Use Enter to select)\n']) {
    pane.screen = menu + footer;
    const before = f.herdr.calls.length;
    const shown = await statusAll(f);
    for (const words of [shown.detail, shown.line, shown.json.words]) assert.match(words, /Gemini shell-safety dialog.*pdd workflow open 17/);
    assertOnlyReads(f, before);
  }
});

test('Gemini status keeps generic blocked words for stale or unreadable screens', async t => {
  const f = await fixture(t, { agent: 'gemini' });
  await f.run();
  const pane = f.herdr.paneOf(f.record().chats.at(-1));
  pane.agent.agent_status = 'blocked';
  const old = '⚠ CRITICAL SECURITY WARNING: Untrusted Command Flags Detected\nAllow execution of [Shell]?\n● 1. Allow once\n  2. No, suggest changes (esc)\n';
  for (const suffix of ['> \n', 'Another question?\n● 1. Yes\n  2. No\n(Use Enter to select)\n']) {
    pane.screen = old + suffix;
    const shown = await statusAll(f);
    assert.match(shown.json.words, /the chat asks a question/);
  }
  const original = f.ports.herdr;
  f.ports.herdr = async args => { if (args[0] === 'pane' && args[1] === 'read') throw Error('unavailable'); return original(args); };
  assert.match((await statusAll(f)).json.words, /the chat asks a question/);
});

test('Gemini Ink bordered shell safety dialog above status bar is named while stale scrollback above Edit or normal Shell dialogs stays generic', async t => {
  const f = await fixture(t, { agent: 'gemini' });
  await f.run();
  const pane = f.herdr.paneOf(f.record().chats.at(-1));
  pane.agent.agent_status = 'blocked';

  // (a) Real Gemini Ink <Box> with ANSI escapes, inner command box, padded rows, bottom border, and YOLO/model status bar
  for (const heading of ['CRITICAL SECURITY WARNING: Untrusted Command Flags Detected', 'CAUTION: Build Configuration Was Recently Modified']) {
    pane.screen = [
      '> Read /tmp/from-issue.md',
      '✦ Inspecting file.',
      '╭──────────────────────────────────────────────────────────────────────╮',
      '│ \x1b[33m? Shell\x1b[0m  cat /tmp/from-issue.md                                      │',
      '│ ╭──────────────────────────────────────────────────────────────────╮ │',
      '│ │ cat /tmp/from-issue.md                                           │ │',
      '│ ╰──────────────────────────────────────────────────────────────────╯ │',
      '│                                                                      │',
      `│ ⚠  ⚠️ ${heading.padEnd(61, ' ')} │`,
      '│    • /tmp/from-issue.md                                              │',
      '│    Carefully verify before approving.                                │',
      '│                                                                      │',
      '│ Allow execution of [Shell]?                                          │',
      '│                                                                      │',
      '│ ● 1. Allow once                                                      │',
      '│   2. No, suggest changes (esc)                                       │',
      '│                                                                      │',
      '│ (Use Enter to select)                                                │',
      '╰──────────────────────────────────────────────────────────────────────╯',
      'YOLO mode (ctrl + y to toggle)',
      '~/work/project   no sandbox (see /docs)   gemini-2.5-pro (98% context left)',
      '',
    ].join('\n');
    const before = f.herdr.calls.length;
    const shown = await statusAll(f);
    for (const words of [shown.detail, shown.line, shown.json.words]) assert.match(words, /Gemini shell-safety dialog.*pdd workflow open 17/);
    assertOnlyReads(f, before);
  }

  // (b) Earlier shell-safety warning above > input line followed by non-shell Edit confirmation dialog -> generic blocked
  for (const editQuestion of ['Allow execution of [Edit]?', 'Apply this change?']) {
    pane.screen = [
      '⚠ CRITICAL SECURITY WARNING: Untrusted Command Flags Detected',
      'Allow execution of [Shell]?',
      '● 1. Allow once',
      '  2. No, suggest changes (esc)',
      '> Edit src/index.mjs instead',
      '╭──────────────────────────────────────────────────────────╮',
      '│ ? Edit  src/index.mjs                                    │',
      `│ ${editQuestion.padEnd(56, ' ')} │`,
      '│ ● 1. Allow once                                          │',
      '│   2. No, suggest changes (esc)                           │',
      '│ (Use Enter to select)                                    │',
      '╰──────────────────────────────────────────────────────────╯',
      'YOLO mode (ctrl + y to toggle)',
      '',
    ].join('\n');
    assert.match((await statusAll(f)).json.words, /the chat asks a question/);
  }

  // (c) Earlier quoted or resolved shell-safety warning followed by a normal non-tainted Allow execution of [Shell]? dialog -> generic blocked
  for (const normalShellScreen of [
    [
      '> Check issue #2887',
      '✦ Issue #2887 quotes CRITICAL SECURITY WARNING: Untrusted Command Flags Detected.',
      '> Run git status',
      'Allow execution of [Shell]?',
      '● 1. Allow once',
      '  2. No, suggest changes (esc)',
      '(Use Enter to select)',
      '',
    ].join('\n'),
    [
      '> Check issue #2887',
      '✦ Issue #2887 quotes CRITICAL SECURITY WARNING: Untrusted Command Flags Detected.',
      '╭──────────────────────────────────────────────────────────╮',
      '│ ? Shell  git status                                      │',
      '│ ╭──────────────────────────────────────────────────────╮ │',
      '│ │ git status                                           │ │',
      '│ ╰──────────────────────────────────────────────────────╯ │',
      '│ Allow execution of [Shell]?                              │',
      '│ ● 1. Allow once                                          │',
      '│   2. No, suggest changes (esc)                           │',
      '│ (Use Enter to select)                                    │',
      '╰──────────────────────────────────────────────────────────╯',
      'YOLO mode (ctrl + y to toggle)',
      '',
    ].join('\n'),
  ]) {
    pane.screen = normalShellScreen;
    assert.match((await statusAll(f)).json.words, /the chat asks a question/);
  }
});

test('other agent startup does not warn about Gemini safety dialogs', async t => {
  const f = await fixture(t, { agent: 'claude' });
  assert.doesNotMatch((await f.run()).message, /Gemini shell safety dialogs/);
});

test('2571 versioned list reports usage-limit evidence', async t => {
  const { f, pane } = await claudeChat(t);
  pane.agent.agent_status = 'blocked';
  pane.screen = "> Start the plan area.\n  ⎿  You've hit your weekly limit · resets Oct 28 at 3pm (UTC)\n\n What do you want to do?\n\n ❯ 1. Stop and wait for limit to reset\n   2. Wait here, then continue automatically\n\n Enter to confirm · Esc to cancel\n";
  const result = await runStatus({cwd:f.source,all:true,json:true}, f.ports);
  assert.deepEqual(JSON.parse(result.message).runs[0].waiting, {kind:'chat_stopped',gate:null,question:null,reason:'usage_limit'});
});
