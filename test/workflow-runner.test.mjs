import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, existsSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { startRun, stepDone, approveRun, changeRun, cancelRun, runStatus, openRun } from '../src/workflow-runner.mjs';

const exec = promisify(callbackExec);
const packageRoot = resolve(import.meta.dirname, '..');
const issueUrl = 'https://github.com/example/project/issues/17';

// A fake Herdr server for session pdd: workspaces, tabs, panes and the agents that pane commands start.
function fakeHerdr() {
  const h = { workspaces: [], tabs: [], panes: [], calls: [], next: 1, focus: null };
  const id = prefix => `${prefix}${h.next++}`;
  const commonDir = cwd => realpathSync(execFileSync('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'], { cwd, encoding: 'utf8' }).trim());
  const pane = (workspace, tab, cwd) => { const p = { workspace_id: workspace, tab_id: tab, pane_id: id('p'), terminal_id: id('term'), cwd, agent: null }; h.panes.push(p); return p; };
  const fail = code => { throw Object.assign(Error(code), { code }); };
  h.herdr = async args => {
    h.calls.push(args);
    const [group, verb, ...rest] = args;
    const flag = name => rest[rest.indexOf(name) + 1];
    if (group === 'status') return { running: true, session: 'pdd', compatible: true };
    if (group === 'workspace' && verb === 'list') return { id: 'cli:workspace:list', result: { type: 'workspace_list', workspaces: h.workspaces } };
    if (group === 'workspace' && verb === 'create') {
      const cwd = flag('--cwd'), w = { workspace_id: id('w'), label: flag('--label'), worktree: { checkout_path: cwd, repo_key: commonDir(cwd), is_linked_worktree: false } };
      h.workspaces.push(w); const t = { tab_id: id('t'), workspace_id: w.workspace_id, label: '1' }; h.tabs.push(t); pane(w.workspace_id, t.tab_id, cwd);
      return { id: 'cli:workspace:create', result: { workspace: w } };
    }
    if (group === 'worktree' && verb === 'open') {
      const cwd = flag('--path'), w = { workspace_id: id('w'), label: flag('--label'), worktree: { checkout_path: cwd, repo_key: commonDir(cwd), is_linked_worktree: true } };
      h.workspaces.push(w); const t = { tab_id: id('t'), workspace_id: w.workspace_id, label: '1' }; h.tabs.push(t); const p = pane(w.workspace_id, t.tab_id, cwd);
      return { id: 'cli:worktree:open', result: { workspace: w, tab: t, root_pane: p } };
    }
    if (group === 'workspace' && verb === 'close') {
      h.workspaces = h.workspaces.filter(w => w.workspace_id !== rest[0]); h.tabs = h.tabs.filter(t => t.workspace_id !== rest[0]);
      return { id: 'cli:workspace:close', result: { type: 'ok' } };
    }
    if (group === 'pane' && verb === 'list') return { id: 'cli:pane:list', result: { type: 'pane_list', panes: h.panes.filter(p => p.workspace_id === flag('--workspace') && h.tabs.some(t => t.tab_id === p.tab_id)) } };
    if (group === 'tab' && verb === 'create') {
      const t = { tab_id: id('t'), workspace_id: flag('--workspace'), label: flag('--label') }; h.tabs.push(t);
      return { id: 'cli:tab:create', result: { tab: t, root_pane: pane(t.workspace_id, t.tab_id, flag('--cwd')) } };
    }
    if (group === 'tab' && verb === 'list') return { id: 'cli:tab:list', result: { type: 'tab_list', tabs: h.tabs.filter(t => t.workspace_id === flag('--workspace')) } };
    if (group === 'tab' && verb === 'get') { const t = h.tabs.find(t => t.tab_id === rest[0]) ?? fail('tab_not_found'); return { result: { tab: t } }; }
    if (group === 'tab' && verb === 'focus') { h.tabs.find(t => t.tab_id === rest[0]) ?? fail('tab_not_found'); h.focus = rest[0]; return { result: { type: 'ok' } }; }
    if (group === 'tab' && verb === 'close') { h.tabs = h.tabs.filter(t => t.tab_id !== rest[0]); return { id: 'cli:tab:close', result: { type: 'ok' } }; }
    if (group === 'pane' && verb === 'run') {
      const p = h.panes.find(p => p.pane_id === rest[0]) ?? fail('pane_not_found');
      const command = rest[1], kind = / claude /.test(command) ? 'claude' : / codex /.test(command) ? 'codex' : null;
      const session = command.match(/--(?:session-id|resume) ([0-9a-f-]{36})/)?.[1] ?? command.match(/ resume ([0-9a-f-]{36})/)?.[1] ?? '00000000-0000-4000-8000-000000000017';
      p.commands = [...(p.commands ?? []), command];
      if (kind) p.agent = { agent: kind, agent_status: 'working', agent_session: { agent: kind, kind: 'id', value: session }, prompts: [] };
      return {};
    }
    if (group === 'agent' && verb === 'get') { const p = h.panes.find(p => p.pane_id === rest[0]); if (!p?.agent) fail('agent_not_found'); return { result: { agent: { ...p.agent, pane_id: p.pane_id } } }; }
    if (group === 'agent' && verb === 'prompt') { const p = h.panes.find(p => p.pane_id === rest[0]); if (!p?.agent) fail('agent_not_found'); p.agent.prompts.push(rest[1]); return { result: { type: 'agent_prompted' } }; }
    fail(`unexpected herdr ${args.join(' ')}`);
  };
  h.paneOf = chat => h.panes.find(p => p.pane_id === chat.paneId);
  return h;
}

async function fixture(t, { agent = 'claude', name = 'small-change' } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-runner-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const source = join(base, 'project'), state = join(base, 'state'), home = join(base, 'home');
  for (const dir of [source, state, home]) mkdirSync(dir);
  const git = (cwd, ...args) => execFileSync('git', args, { cwd, encoding: 'utf8' }).trim();
  git(source, 'init', '-q', '-b', 'main'); git(source, 'config', 'user.email', 'test@example.invalid'); git(source, 'config', 'user.name', 'Runner Test');
  git(source, 'remote', 'add', 'origin', 'https://github.com/example/project.git');
  writeFileSync(join(source, 'value.mjs'), 'export const value = 1;\n'); git(source, 'add', '.'); git(source, 'commit', '-qm', 'initial');
  git(source, 'update-ref', 'refs/remotes/origin/main', git(source, 'rev-parse', 'HEAD'));
  const f = { base, source, state, git, herdr: fakeHerdr(), prs: [], pushes: [], fetches: 0, clock: Date.parse('2026-10-27T17:00:00Z'), ci: [], merged: false };
  async function execFile(file, args, opts) {
    if (file === 'git' && args[0] === 'push') { f.pushes.push(args); return { stdout: '' }; }
    if (file === 'git' && args[0] === 'fetch') { f.fetches++; return { stdout: '' }; }
    if (file !== 'gh') return exec(file, args, { ...opts, encoding: 'utf8' });
    if (args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/example/project' }) };
    if (args[0] === 'api' && args[1] === 'repos/example/project/issues/17') return { stdout: JSON.stringify({ number: 17, html_url: issueUrl, title: 'Use value two', body: 'Value must be two.' }) };
    if (args[0] === 'pr' && args[1] === 'create') {
      const value = flag => args[args.indexOf(flag) + 1];
      const pr = { number: 23, url: 'https://github.com/example/project/pull/23', state: 'OPEN', headRefName: value('--head'), baseRefName: value('--base'),
        headRefOid: (await exec('git', ['rev-parse', 'HEAD'], { cwd: opts.cwd })).stdout.trim(), body: readFileSync(value('--body-file'), 'utf8'), title: value('--title'),
        headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, isCrossRepository: false, mergeCommit: null };
      f.prs.push(pr); return { stdout: pr.url + '\n' };
    }
    if (args[0] === 'pr' && args[1] === 'list') return { stdout: JSON.stringify(f.prs) };
    if (args[0] === 'pr' && args[1] === 'view') return { stdout: JSON.stringify({ state: f.merged ? 'MERGED' : 'OPEN', mergedAt: null, statusCheckRollup: f.ci }) };
    throw Error(`unexpected gh ${args.join(' ')}`);
  }
  f.prompts = [];
  f.ports = { execFile, herdr: f.herdr.herdr, stateDir: state, layoutDirectory: join(state, 'herdr-layout'), now: () => f.clock,
    env: { HOME: home, CLAUDE_CONFIG_DIR: join(home, '.claude') }, isTTY: true, pdd: '/abs/node /abs/pdd.mjs',
    confirm: async question => { f.prompts.push(question); return f.answer ?? true; },
    attach: async () => 0, readApprovalEvidence: async () => assert.fail('A terminal person needs no chat evidence') };
  f.run = () => startRun({ name, issue: '17', agent, cwd: source, packageRoot }, f.ports);
  f.record = () => JSON.parse(readFileSync(join(f.git(source, 'rev-parse', '--path-format=absolute', '--git-common-dir'), 'pdd', 'runs', '17', 'status.json'), 'utf8'));
  f.tick = (ms = 1000) => { f.clock += ms; };
  f.agentPorts = extra => ({ ...f.ports, isTTY: false, env: { ...f.ports.env, PDD_AGENT_SESSION: '1' }, ...extra });
  return f;
}

test('small-change: run exits at once, done reaches the gate, changes go to the same chat, approve opens a new chat, done verify opens the PR', async t => {
  const f = await fixture(t);
  const started = await f.run();
  assert.equal(started.exitCode, 0, started.message);
  assert.match(started.message, /pdd workflow open 17/); assert.match(started.message, /pdd workflow approve 17/);
  let run = f.record();
  assert.equal(run.v, 1); assert.equal(run.state, 'running'); assert.equal(run.area, 0); assert.equal(run.chats.length, 1);
  assert.equal(run.workflow, 'small-change'); assert.equal(run.issue.number, 17); assert.equal(f.fetches, 1);
  assert.ok(existsSync(run.root) && run.root !== f.source); assert.match(run.branch, /^pdd\/small-change-17-/);
  const first = run.chats[0], pane = f.herdr.paneOf(first);
  assert.equal(pane.commands.length, 1);
  assert.match(pane.commands[0], /^env PDD_AGENT_SESSION=1 CLAUDE_CONFIG_DIR=\S+ claude --dangerously-skip-permissions --session-id [0-9a-f-]{36} "\$\(cat '.+plan-start\.md'\)"$/);
  assert.equal(first.session.id, pane.agent.agent_session.value);
  const message = readFileSync(join(run.runDir, 'plan-start.md'), 'utf8');
  for (const part of ['Use the pdd-small-change skill', '#17', 'Use value two', issueUrl, run.root, run.runDir, 'plan', 'scope', '/abs/node /abs/pdd.mjs workflow done'])
    assert.ok(message.includes(part), part);
  assert.ok(message.split('\n').length <= 14, message);
  assert.doesNotMatch(message, /Prompting guide/);
  assert.equal(f.herdr.tabs.find(tab => tab.tab_id === first.tabId).label, 'plan');
  assert.equal(f.herdr.workspaces.find(w => w.workspace_id === first.workspaceId).label, '#17 small-change');

  f.tick();
  const gate = await stepDone({ step: 'scope', summary: 'Change value.mjs to 2.', cwd: run.root }, f.agentPorts());
  assert.equal(gate.exitCode, 0, gate.message);
  assert.match(gate.message, /show the person|ask the person/i); assert.match(gate.message, /stop/i);
  assert.match(gate.message, /\/abs\/node \/abs\/pdd\.mjs workflow approve 17/);
  run = f.record();
  assert.equal(run.state, 'waiting'); assert.deepEqual(run.waitingFor.decisions, ['approve', 'changes']); assert.equal(run.stage.id, 'approve');
  assert.equal(run.gate.at, f.clock); assert.equal(run.done.scope.summary, 'Change value.mjs to 2.');

  f.tick();
  const changed = await changeRun({ ref: '17', text: 'Also explain why.', cwd: f.source }, f.ports);
  assert.equal(changed.exitCode, 0, changed.message);
  assert.equal(pane.agent.prompts.length, 1); assert.match(pane.agent.prompts[0], /The person asks for changes: Also explain why\./);
  run = f.record(); assert.equal(run.changes.length, 1); assert.equal(run.changes[0].text, 'Also explain why.'); assert.equal(run.gate.at, f.clock);

  f.tick();
  const approved = await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { HOME: f.ports.env.HOME } });
  assert.equal(approved.exitCode, 0, approved.message);
  assert.equal(f.prompts.length, 1); assert.match(f.prompts[0], /plan/); assert.match(f.prompts[0], /example\/project#17 "Use value two"/); assert.match(f.prompts[0], /\(y\/N\)/);
  run = f.record();
  assert.equal(run.area, 1); assert.equal(run.state, 'running'); assert.equal(run.chats.length, 2); assert.equal(run.gate, null);
  assert.equal(run.decisions.at(-1).decision, 'approve'); assert.equal(run.decisions.at(-1).via, 'terminal');
  const second = run.chats[1];
  assert.notEqual(second.tabId, first.tabId); assert.notEqual(second.session.id, first.session.id);
  assert.equal(second.configDir, first.configDir, 'the next chat keeps the account of the run, not of the approving terminal');
  assert.ok(f.herdr.paneOf(second).commands[0].includes(`CLAUDE_CONFIG_DIR='${first.configDir}'`));
  assert.equal(pane.agent.prompts.length, 1, 'approval never writes into the old chat');
  const buildMessage = readFileSync(join(run.runDir, 'build-start.md'), 'utf8');
  for (const part of ['Use the pdd-small-change skill', 'build', 'change', 'verify', 'Change value.mjs to 2.', 'verify.md']) assert.ok(buildMessage.includes(part), part);

  f.tick();
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'Use value two');
  const next = await stepDone({ step: 'change', summary: 'value is 2', cwd: run.root }, f.agentPorts());
  assert.match(next.message, /Next step: verify/); assert.match(next.message, /workflow done verify/);
  assert.equal(f.prs.length, 0);

  f.tick();
  writeFileSync(join(run.runDir, 'verify.md'), '$ node --test\n# pass 3\n');
  writeFileSync(join(run.root, 'notes.txt'), 'left behind\n');
  const opened = await stepDone({ step: 'verify', summary: 'tests pass', cwd: run.root }, f.agentPorts());
  assert.equal(opened.exitCode, 0, opened.message);
  assert.match(opened.message, /pdd opens the PR now/); assert.match(opened.message, /https:\/\/github\.com\/example\/project\/pull\/23/); assert.match(opened.message, /never merges/);
  assert.match(opened.message, /notes\.txt/, 'auto-commit names the files it committed');
  assert.equal(f.prs.length, 1); assert.equal(f.prs[0].title, 'Use value two'); assert.equal(f.prs[0].baseRefName, 'main');
  assert.match(f.prs[0].body, /Closes #17/); assert.match(f.prs[0].body, /# pass 3/); assert.match(f.prs[0].body, /tests pass/);
  assert.equal(f.git(run.root, 'status', '--porcelain'), '');
  run = f.record();
  assert.deepEqual(run.pr.map(pr => pr.url), ['https://github.com/example/project/pull/23']);
  assert.equal(run.stage.id, 'merge'); assert.deepEqual(run.waitingFor.decisions, []);

  f.ci = [{ conclusion: 'SUCCESS' }];
  const shown = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(shown.exitCode, 0); assert.match(shown.message, /pull\/23/); assert.match(shown.message, /CI passing/);
  f.merged = true;
  await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(f.record().state, 'completed');
  assert.ok(f.record().journalSeq > 5);
});

test('an agent session cannot approve without the person reply in the chat, and a chat reply approves', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  const requests = [];
  const refused = await approveRun({ ref: undefined, cwd: run.root }, f.agentPorts({ isTTY: true,
    readApprovalEvidence: async request => { requests.push(request); return { ok: false, code: 'user_message_missing', message: 'No user message was found after the gate question in this native session.' }; } }));
  assert.equal(refused.exitCode, 1); assert.match(refused.message, /Only the person can approve/);
  assert.equal(f.prompts.length, 0, 'an agent never gets the y/N question');
  assert.equal(f.record().area, 0); assert.equal(f.record().chats.length, 1);
  assert.equal(requests[0].stage.agent, 'claude'); assert.equal(requests[0].stage.root, run.root); assert.equal(requests[0].stage.sessionId, run.chats[0].session.id);
  assert.equal(requests[0].gateAskedAt, f.record().gate.at); assert.ok(requests[0].ignorePrefixes.some(prefix => prefix.startsWith('The person asks for changes')));
  f.tick();
  const approved = await approveRun({ ref: undefined, cwd: run.root }, f.agentPorts({
    readApprovalEvidence: async () => ({ ok: true, decision: 'approve', agent: 'claude', sessionId: run.chats[0].session.id, userMessage: 'looks right, go', userMessageAt: f.clock - 10 }) }));
  assert.equal(approved.exitCode, 0, approved.message); assert.match(approved.message, /looks right, go/); assert.match(approved.message, /Stop here/);
  const after = f.record();
  assert.equal(after.area, 1); assert.equal(after.decisions.at(-1).via, 'chat'); assert.equal(after.decisions.at(-1).text, 'looks right, go');
  assert.equal(after.approvalRecord.sessionId, run.chats[0].session.id);
});

test('real chat evidence: a Claude transcript reply after the gate approves; the change request pdd sent does not', async t => {
  const f = await fixture(t);
  f.ports.readApprovalEvidence = undefined;
  await f.run(); const run = f.record(); const chat = run.chats[0];
  f.tick(); await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); await changeRun({ ref: '17', text: 'use blue', cwd: f.source }, f.ports);
  const gateAt = f.record().gate.at;
  const dir = join(f.ports.env.CLAUDE_CONFIG_DIR, 'projects', run.root.replace(/[^a-zA-Z0-9]/g, '-'));
  mkdirSync(dir, { recursive: true });
  const row = (type, text, at) => JSON.stringify({ type, sessionId: chat.session.id, cwd: run.root, timestamp: new Date(at).toISOString(), message: { role: type, content: [{ type: 'text', text }] } });
  const file = join(dir, `${chat.session.id}.jsonl`);
  writeFileSync(file, [row('user', 'Use the pdd-small-change skill.', chat.startedAt + 1), row('assistant', 'Plan ready. Approve?', gateAt - 1),
    row('user', 'The person asks for changes: use blue. Revise in this chat.', gateAt + 1), row('assistant', 'Revised. Approve?', gateAt + 2)].join('\n') + '\n');
  f.tick();
  const agent = f.agentPorts({ readApprovalEvidence: undefined });
  const refused = await approveRun({ ref: '17', cwd: run.root }, agent);
  assert.equal(refused.exitCode, 1, refused.message); assert.equal(f.record().area, 0);
  writeFileSync(file, readFileSync(file, 'utf8') + row('user', 'ok ship it', gateAt + 3) + '\n' + row('assistant', 'Approving.', gateAt + 4) + '\n');
  const approved = await approveRun({ ref: '17', cwd: run.root }, agent);
  assert.equal(approved.exitCode, 0, approved.message); assert.equal(f.record().decisions.at(-1).text, 'ok ship it');
});

test('done warns on unknown and out-of-order steps but records them and never breaks the run', async t => {
  const f = await fixture(t, { name: 'bug' });
  await f.run(); const run = f.record();
  const unknown = await stepDone({ step: 'deploy', summary: 'x', cwd: run.root }, f.agentPorts());
  assert.equal(unknown.exitCode, 0); assert.match(unknown.message, /warning/i); assert.match(unknown.message, /Next step: reproduce/);
  const early = await stepDone({ step: 'check', cwd: run.root }, f.agentPorts());
  assert.equal(early.exitCode, 0); assert.match(early.message, /warning/i); assert.match(early.message, /reproduce, prompt-story/);
  assert.ok(f.record().done.deploy && f.record().done.check);
  const outside = await stepDone({ step: 'scope', cwd: f.source }, f.agentPorts());
  assert.equal(outside.exitCode, 1); assert.match(outside.message, /worktree/);
});

for (const [name, areas] of [['bug', [['solution', ['reproduce', 'prompt-story', 'check', 'try']], ['build', ['build', 'verify']]]],
  ['feature', [['solution', ['understand', 'visual']], ['story', ['prompt-story', 'check', 'try']], ['build', ['build', 'verify']]]]]) {
  test(`${name}: every approve gate starts a new area chat and only the last build step opens the PR`, async t => {
    const f = await fixture(t, { name, agent: 'codex' });
    assert.equal((await f.run()).exitCode, 0);
    let run = f.record();
    assert.match(f.herdr.paneOf(run.chats[0]).commands[0], /^env PDD_AGENT_SESSION=1 codex --no-daemon --dangerously-bypass-approvals-and-sandbox -c 'projects=\{".+"=\{trust_level="trusted"\}\}' "\$\(cat '.+solution-start\.md'\)"$/);
    for (const [index, [area, steps]] of areas.entries()) {
      assert.equal(f.record().area, index); assert.equal(f.record().chats.at(-1).area, area);
      const optional = await import('node:fs').then(fs => JSON.parse(fs.readFileSync(join(packageRoot, `skills/pdd-${name}/workflow.json`), 'utf8')).areas[index].optional);
      for (const step of steps) {
        if (area === 'build' && step === 'build') { writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'fix'); }
        f.tick();
        const out = await stepDone({ step, summary: optional.includes(step) ? 'skipped' : `${step} done`, cwd: run.root }, f.agentPorts());
        assert.equal(out.exitCode, 0, out.message);
        const next = steps[steps.indexOf(step) + 1];
        if (next && optional.includes(next)) assert.match(out.message, /optional/i);
      }
      if (index < areas.length - 1) {
        assert.equal(f.prs.length, 0); assert.equal(f.record().state, 'waiting');
        f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
        assert.equal(f.record().chats.length, index + 2);
      }
    }
    assert.equal(f.prs.length, 1); assert.equal(f.record().stage.id, 'merge');
    const nothing = await approveRun({ ref: '17', cwd: f.source }, f.ports);
    assert.equal(nothing.exitCode, 1); assert.match(nothing.message, /Nothing to approve/);
  });
}

test('a second run for the same issue is refused and points at the first one', async t => {
  const f = await fixture(t);
  await f.run();
  const again = await f.run();
  assert.equal(again.exitCode, 1); assert.match(again.message, /already has a run/); assert.match(again.message, /pdd workflow open 17/);
  assert.equal(f.herdr.panes.filter(p => p.commands).length, 1);
});

test('cancel closes the run tabs, keeps the worktree and branch, and done then tells the agent to stop', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record();
  const cancelled = await cancelRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(cancelled.exitCode, 0, cancelled.message);
  assert.equal(f.record().state, 'cancelled'); assert.equal(f.record().cancelled.state, 'cancelled');
  assert.equal(f.herdr.tabs.some(tab => tab.tab_id === run.chats[0].tabId), false);
  assert.equal(f.herdr.workspaces.some(w => w.workspace_id === run.chats[0].workspaceId), false);
  assert.ok(existsSync(run.root)); assert.equal(f.git(run.root, 'branch', '--show-current'), run.branch);
  const late = await stepDone({ step: 'scope', cwd: run.root }, f.agentPorts());
  assert.match(late.message, /cancelled/); assert.match(late.message, /Stop/);
});

test('open focuses a live chat, resumes an ended native session in its tab, and attaches only from a terminal outside Herdr', async t => {
  const f = await fixture(t);
  await f.run(); const chat = f.record().chats[0], pane = f.herdr.paneOf(chat);
  const attached = [];
  f.ports.attach = async () => { attached.push(true); return 0; };
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  assert.equal(f.herdr.focus, chat.tabId); assert.equal(pane.commands.length, 1); assert.equal(attached.length, 1);
  pane.agent = null;
  const resumed = await openRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' } });
  assert.equal(resumed.exitCode, 0, resumed.message); assert.match(resumed.message, /resum/i);
  assert.match(pane.commands[1], new RegExp(`claude --dangerously-skip-permissions --resume ${chat.session.id}$`));
  assert.equal(attached.length, 1, 'inside Herdr pdd only focuses the tab');
});

test('selection: no ref inside a run worktree finds that run; outside any repository a number in two repositories asks for owner/repo#N', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record();
  const shown = await runStatus({ cwd: run.root }, f.ports);
  assert.equal(shown.exitCode, 0); assert.match(shown.message, /#17/);
  const index = JSON.parse(readFileSync(join(f.state, 'runs.json'), 'utf8'));
  index.runs.push({ ...index.runs[0], repo: 'other/project', runDir: join(f.base, 'missing') });
  writeFileSync(join(f.state, 'runs.json'), JSON.stringify(index));
  const outside = join(f.base, 'home');
  const ambiguous = await openRun({ ref: '17', cwd: outside }, f.ports);
  assert.equal(ambiguous.exitCode, 1); assert.match(ambiguous.message, /example\/project#17/); assert.match(ambiguous.message, /other\/project#17/);
  const picked = await runStatus({ ref: 'example/project#17', cwd: outside }, f.ports);
  assert.equal(picked.exitCode, 0, picked.message); assert.match(picked.message, /Use value two/);
});
