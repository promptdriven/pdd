import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';

const root = resolve('.');
const capture = () => ({ text: '', write(s) { this.text += s; } });
async function fixture(t, options = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-autopilot-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, 'repo'), home = join(dir, 'home');
  mkdirSync(cwd); mkdirSync(home);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: options.mode ?? { mode: 'auto', trust: ['helper'] } }));
  const f = { cwd, home, time: Date.parse('2026-11-04T00:00:00Z'), polls: [], prompts: [], runs: [], timers: [], comments: [], ack: [], issues: [], etag: '"one"', active: false };
  f.ports = {
    stateRoot: join(home, 'state'), now: () => f.time,
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }),
    pathDiagnostic: () => [],
    run: async (command, args) => {
      f.runs.push([command, args]);
      if (command === 'git') return { code: 0, stdout: cwd + '\n', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api') { if (args.some(x => String(x).includes('/permission'))) return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n{"permission":"none"}', stderr: '' }; f.ack.push(args); return { code: 0, stdout: '{}', stderr: '' }; }
      if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
      throw Error(`unexpected process ${command} ${args}`);
    },
    timer: async (action, state) => { f.timers.push([action, structuredClone(state)]); if (action === 'start') f.active = true; if (action === 'stop') f.active = false; return f.active; },
    queryIssues: async (state) => { f.polls.push(state.etag); return { status: f.status ?? 200, etag: f.etag, issues: structuredClone(f.issues) }; },
    comments: async number => { f.comments.push(number); return f.issueComments?.[number] ?? []; },
    herdr: async args => {
      f.herdrCalls ??= []; f.herdrCalls.push(args);
      if (args[0] === 'workspace') return { result: { workspace: { workspace_id: 'w1' }, root_pane: { pane_id: 'p1' } } };
      if (args[0] === 'agent' && args[1] === 'get') {
        if (!f.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' });
        return { result: { agent: { agent_status: 'idle' } } };
      }
      if (args[0] === 'pane') {
        f.agentStarted = true;
        const packetFile = readdirSync(f.ports.stateRoot).find(x => x.endsWith('.message.md'));
        f.prompts.push(readFileSync(join(f.ports.stateRoot, packetFile), 'utf8'));
      }
      if (args[0] === 'agent' && args[1] === 'prompt') f.prompts.push(args[3] ?? args[2]);
      return {};
    },
  };
  f.module = await import('../src/autopilot-launcher.mjs');
  f.invoke = async (command, extra = {}) => f.module.runAutopilotLauncher({ command, cwd, env: { HOME: home, PATH: process.env.PATH }, packageRoot: root, issues: [], ...extra }, f.ports);
  f.stateFile = () => join(f.ports.stateRoot, readdirSync(f.ports.stateRoot).find(x => x.endsWith('.json')));
  f.state = () => JSON.parse(readFileSync(f.stateFile(), 'utf8'));
  f.tick = () => f.module.tickAutopilot(f.stateFile(), f.ports);
  return f;
}
const issue = (number, extra = {}) => ({ number, state: 'open', title: `Issue ${number}`, body: 'trusted body', user: { login: 'owner' }, author_association: 'OWNER', created_at: '2026-11-04T00:01:00Z', updated_at: '2026-11-04T00:01:00Z', comments: 0, labels: [], html_url: `https://github.com/owner/repo/issues/${number}`, ...extra });

test('autopilot routes parse and dispatch without setup or a runtime call', async () => {
  const stdout = capture(), stderr = capture(); let seen;
  assert.equal(parseArgv(['autopilot', 'start', '--runs', '1200000']).local, 'autopilot-start');
  assert.equal(await runPdd(['autopilot', 'start', '--runs', '3'], { cwd: '/repo', stdout, stderr, autopilotLauncher: { runAutopilotLauncher: async input => { seen = input; return { exitCode: 0, message: 'started' }; } } }), 0);
  assert.equal(seen.command, 'start'); assert.equal(seen.runs, '3');
  assert.equal(stdout.text, 'started\n'); assert.equal(stderr.text, '');
  assert.deepEqual(parseArgv(['autopilot', 'add', '12', '15']).operands, ['12', '15']);
});

test('start installs a timer and runs the recipe immediately; unchanged empty ticks wake no AI', async t => {
  const f = await fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  assert.equal(f.polls.length, 1); assert.equal(f.prompts.length, 1);
  assert.match(f.prompts[0], /"recipeFirst":true/);
  assert.equal(f.state().runs, undefined);
  assert.equal(f.state().nextTick, f.time + 1800000);
  f.status = 304; await f.tick(); await f.tick();
  assert.equal(f.prompts.length, 1); assert.deepEqual(f.polls, [undefined, '"one"', '"one"']);
});

test('new issues and named backlog run; old backlog, PRs, closed and working issues do not', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(1), issue(2, { created_at: '2026-01-01T00:00:00Z' }), issue(3, { created_at: '2026-01-01T00:00:00Z', labels: [{ name: 'pdd:autopilot' }] }), issue(4, { pull_request: {} }), issue(5, { state: 'closed' }), issue(6, { labels: [{ name: 'pdd:working' }] })];
  await f.tick();
  const prompt = f.prompts.at(-1);
  assert.match(prompt, /"number":1,/); assert.match(prompt, /"number":3,/);
  for (const n of [2, 4, 5, 6]) assert.doesNotMatch(prompt, new RegExp(`"number":${n},`));
  await f.tick(); assert.equal(f.prompts.length, 3); // Unclaimed work is offered again when room may have changed.
  await f.invoke('stop'); f.time += 3600000; await f.invoke('start');
  assert.equal(f.state().activatedAt, '2026-11-04T00:00:00.000Z');
});

test('stranger text never reaches AI; a trusted comment admits only trusted text; acknowledgement once', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(8, { title: 'STRANGER TITLE', body: 'STRANGER BODY', user: { login: 'outside' }, author_association: 'NONE' })];
  await f.tick(); await f.tick();
  assert.equal(f.prompts.length, 1); assert.equal(f.ack.length, 1);
  f.issues[0].comments = 3; f.issues[0].updated_at = '2026-11-04T00:02:00Z';
  f.issueComments = { 8: [
    { body: 'STRANGER COMMENT', user: { login: 'outside' }, author_association: 'NONE' },
    { body: 'thanks, a maintainer will look\n\n<!-- pdd:autopilot:thanks -->', user: { login: 'owner' }, author_association: 'OWNER' },
    { body: 'Please fix the broken login', user: { login: 'helper' }, author_association: 'NONE' },
  ] };
  await f.tick();
  assert.equal(f.prompts.length, 2);
  assert.match(f.prompts[1], /Please fix the broken login/);
  assert.doesNotMatch(f.prompts[1], /STRANGER|thanks, a maintainer/);
});

test('trusted issue comments are filtered, and failed delivery is retried', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(9, { comments: 1 })];
  f.issueComments = { 9: [{ body: 'OUTSIDER', user: { login: 'outside' }, author_association: 'NONE' }] };
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => { if (args[1] === 'prompt') throw Error('delivery failed'); return herdr(args); };
  await assert.rejects(f.tick(), /delivery failed/);
  f.ports.herdr = herdr; await f.tick();
  assert.match(f.prompts[1], /trusted body/); assert.doesNotMatch(f.prompts[1], /OUTSIDER/);
});

test('stop disables only the timer and status is local; runs is optional, never fixed', async t => {
  const f = await fixture(t); await f.invoke('start', { runs: '7' });
  assert.match(f.prompts[0], /"runs":7/);
  const before = f.herdrCalls.length, polls = f.polls.length;
  const status = await f.invoke('status'); assert.match(status.message, /owner\/repo.*codex/); assert.match(status.message, /2026-11-04T00:30:00/);
  await f.invoke('stop'); await f.tick(); await f.invoke('stop');
  assert.equal(f.herdrCalls.length, before); assert.equal(f.polls.length, polls);
  assert.match((await f.invoke('status')).message, /stopped/);
  assert.equal((await f.invoke('start', { runs: '0' })).exitCode, 2);
});

test('add marks every named old issue with exactly pdd:autopilot', async t => {
  const f = await fixture(t);
  assert.equal((await f.invoke('add', { issues: ['12', '15'] })).exitCode, 0);
  assert.equal(f.ack.filter(args => args.some(x => String(x).includes('pdd:autopilot'))).length, 3);
});

test('off and missing dependencies give one actionable line without starting an agent', async t => {
  const f = await fixture(t, { mode: 'off' });
  const result = await f.invoke('start'); assert.equal(result.exitCode, 0); assert.match(result.message, /off/);
  assert.equal(f.prompts.length, 0); assert.equal(f.timers.length, 0);
  writeFileSync(join(f.cwd, 'pdd.json'), '{"autopilot":"auto"}');
  f.ports.selectAgent = async () => null;
  const missing = await f.invoke('start'); assert.equal(missing.message.split('\n').length, 1); assert.match(missing.message, /sign in/i);
});

test('two machine launchers offer the same issue to the skill without making a competing claim', async t => {
  const a = await fixture(t), b = await fixture(t);
  a.issues = [issue(21)]; b.issues = [issue(21)];
  await a.invoke('start'); await b.invoke('start');
  assert.match(a.prompts[0], /"number":21,/); assert.match(b.prompts[0], /"number":21,/);
  assert.equal(a.ack.length + b.ack.length, 0);
  assert.match(a.prompts[0], /pdd:working/);
  // The unmerged #2890 skill owns the atomic claim; this proves independent launch state, not that claim.
});

test('native Linux and macOS user timers pin Node, script, state and environment without a shell', async t => {
  for (const platform of ['linux', 'darwin']) {
    const f = await fixture(t); delete f.ports.timer; f.ports.platform = platform; f.ports.uid = 123;
    const run = f.ports.run;
    f.ports.run = async (command, args, opts) => ['systemctl', 'launchctl'].includes(command) ? (f.runs.push([command, args]), { code: 0, stdout: '', stderr: '' }) : run(command, args, opts);
    assert.equal((await f.invoke('start')).exitCode, 0);
    if (platform === 'linux') {
      const folder = join(f.home, '.config', 'systemd', 'user');
      const service = readdirSync(folder).find(x => x.endsWith('.service'));
      const text = readFileSync(join(folder, service), 'utf8');
      assert.ok(text.includes(process.execPath)); assert.ok(text.includes('/src/autopilot-launcher.mjs'));
      assert.ok(text.includes(f.stateFile())); assert.match(text, /Environment="PATH=/);
      assert.doesNotMatch(text, /\/bin\/.*sh|TOKEN|API_KEY/);
      assert.match(readFileSync(join(folder, service.replace('.service', '.timer')), 'utf8'), /OnActiveSec=30min/);
    } else {
      const folder = join(f.home, 'Library', 'LaunchAgents');
      const text = readFileSync(join(folder, readdirSync(folder)[0]), 'utf8');
      assert.ok(text.includes(process.execPath)); assert.match(text, /<integer>1800<\/integer>/);
      assert.match(text, /EnvironmentVariables/); assert.ok(text.includes(f.stateFile()));
      assert.ok(f.runs.some(([cmd, args]) => cmd === 'launchctl' && args[0] === 'bootstrap' && args[1] === 'gui/123'));
    }
    await f.invoke('stop');
    assert.equal(f.state().enabled, false);
    const definitions = platform === 'linux' ? join(f.home, '.config', 'systemd', 'user') : join(f.home, 'Library', 'LaunchAgents');
    assert.deepEqual(readdirSync(definitions), []);
  }
});

test('native HTTP tick uses ETags and revalidates cached later pages, including a close', async t => {
  const f = await fixture(t); delete f.ports.queryIssues;
  let phase = 0; const queries = [];
  const run = f.ports.run;
  f.ports.run = async (command, args, opts) => {
    if (command === 'gh' && args[0] === 'api' && args.includes('--include')) {
      queries.push(args);
      const second = args[4]?.includes('page=2');
      if (phase === 0) return { code: 0, stderr: '', stdout: second
        ? `HTTP/2.0 200 OK\r\nETag: "second"\r\n\r\n${JSON.stringify([issue(31)])}`
        : 'HTTP/2.0 200 OK\r\nETag: "first"\r\nLink: <https://api.github.com/repos/owner/repo/issues?page=2>; rel="next"\r\n\r\n[]' };
      return { code: 0, stderr: '', stdout: second ? 'HTTP/2.0 200 OK\r\nETag: "closed"\r\n\r\n[]' : 'HTTP/2.0 304 Not Modified\r\n\r\n' };
    }
    return run(command, args, opts);
  };
  await f.invoke('start'); assert.match(f.prompts[0], /"number":31,/);
  phase = 1; await f.tick();
  assert.equal(f.prompts.length, 1); assert.equal(f.state().cachedIssues.length, 0);
  assert.ok(queries[2].includes('If-None-Match: "first"'));
  assert.ok(queries[3].includes('If-None-Match: "second"'));
});

test('native empty 304 tick makes exactly one GitHub request and no model request', async t => {
  const f = await fixture(t); delete f.ports.queryIssues;
  const run = f.ports.run; let queries = 0;
  f.ports.run = async (command, args, opts) => {
    if (command === 'gh' && args.includes('--include')) return { code: 0, stderr: '', stdout: ++queries === 1 ? 'HTTP/2.0 200 OK\nETag: "empty"\n\n[]' : 'HTTP/2.0 304 Not Modified\n\n' };
    return run(command, args, opts);
  };
  await f.invoke('start'); await f.tick();
  assert.equal(queries, 2); assert.equal(f.prompts.length, 1);
});

test('rate limit reset is saved and no GitHub retry happens before it', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.ports.queryIssues = async () => { f.polls.push('limited'); return { status: 429, resetAt: f.time + 7200000 }; };
  await f.tick(); const polls = f.polls.length;
  await f.tick(); f.time += 1800000; await f.tick();
  assert.equal(f.polls.length, polls);
  f.time += 5400000; await f.tick(); assert.equal(f.polls.length, polls + 1);
});

test('association alone cannot admit a read-only collaborator or a forged acknowledgement', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(41, { user: { login: 'reader' }, author_association: 'COLLABORATOR', body: 'READ ONLY', comments: 1 })];
  f.issueComments = { 41: [{ user: { login: 'reader' }, author_association: 'MEMBER', body: 'thanks, a maintainer will look\n\n<!-- pdd:autopilot:thanks -->' }] };
  const run = f.ports.run;
  f.ports.run = async (cmd, args, opts) => args.some(x => String(x).endsWith('/reader/permission')) ? { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n{"permission":"read"}', stderr: '' } : run(cmd, args, opts);
  await f.tick(); assert.equal(f.prompts.length, 1); assert.equal(f.ack.length, 1);
  f.ports.run = async (cmd, args, opts) => args.some(x => String(x).endsWith('/reader/permission')) ? { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n{"permission":"write"}', stderr: '' } : run(cmd, args, opts);
  await f.tick(); assert.equal(f.prompts.length, 2); assert.match(f.prompts[1], /READ ONLY/);
});

test('native sign-in probes choose each supported interactive provider without a model call', async t => {
  for (const provider of ['codex', 'claude', 'agy', 'gemini']) {
    const f = await fixture(t); delete f.ports.selectAgent;
    if (provider === 'gemini') { mkdirSync(join(f.home, '.gemini')); writeFileSync(join(f.home, '.gemini', 'oauth_creds.json'), '{"refresh_token":"synthetic-test-token"}'); }
    const run = f.ports.run; const probes = [];
    f.ports.run = async (command, args, opts) => {
      if (['codex', 'claude', 'agy', 'gemini'].includes(command)) {
        probes.push([command, args]);
        const stdout = command === 'codex' ? 'Logged in using ChatGPT' : command === 'claude' ? '{"loggedIn":true}' : command === 'agy' ? 'default agent' : '1.0';
        return { code: command === provider ? 0 : 1, stdout: command === provider ? stdout : '', stderr: '' };
      }
      return run(command, args, opts);
    };
    assert.equal((await f.invoke('start')).exitCode, 0); assert.equal(f.state().agent.kind, provider);
    assert.ok(probes.every(([, args]) => ['login', 'auth', 'agents', '--version'].includes(args[0])));
    assert.doesNotMatch(readFileSync(f.stateFile(), 'utf8'), /synthetic-test-token/);
    const launch = f.herdrCalls.find(args => args[0] === 'pane' && args[1] === 'run')[3];
    assert.doesNotMatch(launch, /\bexec\b|--print|\s-p\b/);
  }
});

test('a missing Gemini sign-in is not inferred from a successful version command', async t => {
  const f = await fixture(t); delete f.ports.selectAgent; const run = f.ports.run;
  f.ports.run = async (command, args, opts) => ['codex', 'claude', 'agy', 'gemini'].includes(command) ? { code: command === 'gemini' ? 0 : 1, stdout: 'installed', stderr: '' } : run(command, args, opts);
  const result = await f.invoke('start'); assert.equal(result.exitCode, 1); assert.match(result.message, /Sign in/);
  assert.equal(f.prompts.length, 0);
});

test('failed timer installation leaves stopped state and launches no agent', async t => {
  const f = await fixture(t); f.ports.timer = async () => { throw Error('no user bus'); };
  const result = await f.invoke('start'); assert.equal(result.exitCode, 1); assert.match(result.message, /user session/);
  assert.equal(f.state().enabled, false); assert.equal(f.prompts.length, 0);
});

test('a fresh repo runs real setup actions, then the active-switch seam delivers recipe before work', async t => {
  const f = await fixture(t); rmSync(join(f.cwd, 'pdd.json'));
  const stdout = capture(), stderr = capture();
  const env = { HOME: f.home, PATH: process.env.PATH };
  assert.equal(await runPdd(['setup'], { cwd: f.cwd, packageRoot: root, env, stdout, stderr,
    pathDiagnostic: () => [], workflowAgents: { checkWorkflowAgents: async () => ({ ok: true, agent: 'codex', message: '' }) }, setupAgentMcp: async () => 0 }), 0);
  assert.ok(readFileSync(join(f.cwd, 'AGENTS.md'), 'utf8').includes('pdd:start'));
  // #2852 owns this saved switch, and #2890 owns executing the recipe. Neither is in alpha yet.
  writeFileSync(join(f.cwd, 'pdd.json'), '{"autopilot":"auto"}');
  await f.invoke('start'); assert.match(f.prompts[0], /"recipeFirst":true/);
});

test('permission lookup rate limiting defers all work without sending the outsider reply', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(55, { user: { login: 'writer' }, author_association: 'MEMBER' }), issue(56, { user: { login: 'other' }, author_association: 'NONE' })];
  const run = f.ports.run; let permissionReads = 0;
  const resetAt = f.time + 3600000;
  f.ports.run = async (command, args, opts) => {
    if (args.some(x => String(x).endsWith('/permission'))) { permissionReads++; return { code: 1, stderr: '', stdout: `HTTP/2.0 403 Forbidden\r\nx-ratelimit-reset: ${resetAt / 1000}\r\n\r\n{"message":"API rate limit exceeded"}` }; }
    return run(command, args, opts);
  };
  await f.tick(); assert.equal(f.state().retryAt, resetAt); assert.equal(permissionReads, 1);
  assert.equal(f.ack.length, 0); assert.equal(f.prompts.length, 1);
  await f.tick(); assert.equal(permissionReads, 1);
});

test('an unavailable trust lookup does not misclassify a writer and send a reply', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(57, { user: { login: 'writer' }, author_association: 'MEMBER' })];
  const run = f.ports.run;
  f.ports.run = async (command, args, opts) => args.some(x => String(x).endsWith('/permission'))
    ? { code: 1, stderr: '', stdout: 'HTTP/2.0 503 Unavailable\r\n\r\n{}' } : run(command, args, opts);
  await assert.rejects(f.tick(), /lookup unavailable/);
  assert.equal(f.ack.length, 0); assert.equal(f.prompts.length, 1);
});

test('a removed Herdr pane is replaced, then queued work is delivered', async t => {
  const f = await fixture(t); await f.invoke('start'); f.issues = [issue(58)];
  const herdr = f.ports.herdr; let missing = true;
  f.ports.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'get' && missing) { missing = false; throw Object.assign(Error('pane removed'), { code: 'pane_not_found' }); }
    if (args[0] === 'workspace') return { result: { workspace: { workspace_id: 'w2' }, root_pane: { pane_id: 'p2' } } };
    return herdr(args);
  };
  await f.tick(); assert.equal(f.state().paneId, 'p2');
  assert.ok(f.herdrCalls.some(args => args[0] === 'pane' && args[2] === 'p2'));
  assert.match(f.prompts.at(-1), /"number":58,/);
});

test('rate limiting on the static reply also waits for reset', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(59, { user: { login: 'outside' }, author_association: 'NONE' })];
  const run = f.ports.run; const resetAt = f.time + 3600000;
  f.ports.run = async (command, args, opts) => args.includes('POST') && args.some(x => String(x).endsWith('/comments'))
    ? { code: 1, stderr: '', stdout: `HTTP/2.0 429 Too Many Requests\r\nx-ratelimit-reset: ${resetAt / 1000}\r\n\r\n{}` } : run(command, args, opts);
  await f.tick(); assert.equal(f.state().retryAt, resetAt);
  const polls = f.polls.length; await f.tick(); assert.equal(f.polls.length, polls);
  assert.equal(f.state().acknowledged[59], undefined);
});

test('a later stop retries timer cleanup after a transient failure', async t => {
  const f = await fixture(t); await f.invoke('start');
  const timer = f.ports.timer; let attempts = 0;
  f.ports.timer = async (action, state) => { if (action === 'stop' && ++attempts === 1) throw Error('transient user bus failure'); return timer(action, state); };
  assert.equal((await f.invoke('stop')).exitCode, 1); assert.equal(f.state().enabled, false);
  assert.equal((await f.invoke('stop')).exitCode, 0); assert.equal(attempts, 2);
  assert.equal(f.state().timerInstalled, false);
});
