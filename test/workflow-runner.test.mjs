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
  const f = { base, source, state, git, herdr: fakeHerdr(), prs: [], pushes: [], fetches: 0, clock: Date.parse('2026-10-27T17:00:00Z'), ci: [], merged: false, mergedNumbers: [] };
  async function execFile(file, args, opts) {
    if (file === 'git' && args[0] === 'push') {
      f.pushes.push(args);
      // Like a real push, keep the remote-tracking branch current.
      const [from, to] = args[2].split(':'), sha = (await exec('git', ['rev-parse', from], { cwd: opts.cwd })).stdout.trim();
      await exec('git', ['update-ref', to.replace('refs/heads/', 'refs/remotes/origin/'), sha], { cwd: opts.cwd });
      return { stdout: '' };
    }
    if (file === 'git' && args[0] === 'fetch') {
      f.fetches++;
      const merged = f.prs.find(pr => f.mergedNumbers.includes(pr.number) && pr.baseRefName === args[2]);
      if (merged) await exec('git', ['update-ref', `refs/remotes/origin/${args[2]}`, merged.headRefOid], { cwd: opts.cwd });
      return { stdout: '' };
    }
    if (file !== 'gh') return exec(file, args, { ...opts, encoding: 'utf8' });
    if (args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/example/project' }) };
    if (args[0] === 'api' && args[1] === 'repos/example/project/issues/17') return { stdout: JSON.stringify({ number: 17, html_url: issueUrl, title: 'Use value two', body: 'Value must be two.' }) };
    if (args[0] === 'pr' && args[1] === 'create') {
      const value = flag => args[args.indexOf(flag) + 1];
      const number = 23 + f.prs.length;
      const pr = { number, url: `https://github.com/example/project/pull/${number}`, state: 'OPEN', headRefName: value('--head'), baseRefName: value('--base'),
        headRefOid: (await exec('git', ['rev-parse', 'HEAD'], { cwd: opts.cwd })).stdout.trim(), body: readFileSync(value('--body-file'), 'utf8'), title: value('--title'),
        headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, isCrossRepository: false, mergeCommit: null };
      f.prs.push(pr); return { stdout: pr.url + '\n' };
    }
    if (args[0] === 'pr' && args[1] === 'list') {
      const head = args.includes('--head') ? args[args.indexOf('--head') + 1] : null, search = args.includes('--search') ? args[args.indexOf('--search') + 1].split('"')[1] : null;
      return { stdout: JSON.stringify(f.prs.filter(pr => (!head || pr.headRefName === head) && (!search || pr.body.includes(search)))) };
    }
    if (args[0] === 'pr' && args[1] === 'view') {
      const pr = f.prs.find(item => item.url === args[2]);
      return { stdout: JSON.stringify({ state: f.merged || f.mergedNumbers.includes(pr?.number) ? 'MERGED' : 'OPEN', mergedAt: null, statusCheckRollup: f.ci }) };
    }
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
  // Skills may not be installed (pdd setup installs them only when missing), so every area chat learns where the package skills are.
  for (const text of [message, buildMessage]) assert.ok(text.includes(`All PDD skills are in ${join(packageRoot, 'skills')} (use them if a skill is not installed).`), text);

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
  assert.doesNotMatch(f.prs[0].body, /expire after 7 days/, 'no report link, no expiry note');
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

// The steps come from the bundled workflow.json, so a new step (for example formal) needs no test change.
for (const name of ['bug', 'feature']) {
  const areas = JSON.parse(readFileSync(join(packageRoot, `skills/pdd-${name}/workflow.json`), 'utf8')).areas.map(area => [area.name, area.steps]);
  test(`${name}: the bundled workflow runs story, PR 1 at the code-or-stop gate, then the code area and PR 2`, async t => {
    const f = await fixture(t, { name, agent: 'codex' });
    const report = 'https://checks.example.test/r/k3y-123';
    assert.equal((await f.run()).exitCode, 0);
    let run = f.record();
    assert.deepEqual(areas.map(([area]) => area), ['story', 'prompt-pr', 'code']);
    assert.match(f.herdr.paneOf(run.chats[0]).commands[0], /^env PDD_AGENT_SESSION=1 codex --no-daemon --dangerously-bypass-approvals-and-sandbox -c 'projects=\{".+"=\{trust_level="trusted"\}\}' "\$\(cat '.+story-start\.md'\)"$/);
    for (const [index, [area, steps]] of areas.entries()) {
      assert.equal(f.record().area, index); assert.equal(f.record().chats.at(-1).area, area);
      const optional = JSON.parse(readFileSync(join(packageRoot, `skills/pdd-${name}/workflow.json`), 'utf8')).areas[index].optional;
      for (const step of steps) {
        if (step === 'prompt-story' || step === 'build') { writeFileSync(join(run.root, `${step}.txt`), `${step}\n`); f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', step); }
        f.tick();
        const summary = optional.includes(step) ? 'skipped' : step === 'check' ? `Runtime check: ✓ 3 of 3 criteria · 10/10 checks · 1 AI call ${report}` : `${step} done`;
        const out = await stepDone({ step, summary, cwd: run.root }, f.agentPorts());
        assert.equal(out.exitCode, 0, out.message);
        const next = steps[steps.indexOf(step) + 1];
        if (next && optional.includes(next)) assert.match(out.message, /optional/i);
      }
      assert.equal(f.prs.length, Math.max(0, index));
      if (index < areas.length - 1) {
        assert.equal(f.record().state, 'waiting');
        f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
        assert.equal(f.record().chats.length, index + 2);
      }
    }
    assert.equal(f.prs.length, 2); assert.equal(f.record().stage.id, 'merge');
    assert.ok(f.prs[0].body.includes(`Runtime check: ✓ 3 of 3 criteria · 10/10 checks · 1 AI call ${report}`), 'the check result stays in PR 1');
    assert.match(f.prs[0].body, /Runtime report links expire after 7 days\./);
    assert.equal(f.prs[1].baseRefName, f.prs[0].headRefName, 'PR 2 is stacked on the open PR 1');
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
  assert.match(pane.commands[1], new RegExp(`claude --dangerously-skip-permissions --resume '${chat.session.id}'$`));
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

test('a terminal approve whose input closes without an answer is a no and changes nothing', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  const { PassThrough } = await import('node:stream');
  const stdin = new PassThrough(), stderr = new PassThrough();
  setImmediate(() => stdin.end());
  const answer = await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: undefined, stdin, stderr });
  assert.equal(answer.exitCode, 1); assert.match(answer.message, /Not approved/);
  assert.equal(f.record().area, 0); assert.equal(f.record().chats.length, 1);
});

test('a workflow skill in the project wins the lookup, and the chat is told where that skill is', async t => {
  const f = await fixture(t, { name: 'docs' });
  const skill = join(f.source, '.agents', 'skills', 'pdd-docs');
  mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [{ name: 'draft', steps: ['outline', 'write'], optional: [], gate: 'approve' }, { name: 'build', steps: ['verify'], optional: [], gate: 'pr' }] }));
  const started = await f.run();
  assert.equal(started.exitCode, 0, started.message);
  const run = f.record();
  assert.deepEqual(run.areas.map(area => area.name), ['draft', 'build']); assert.equal(run.skillDir, skill);
  const message = readFileSync(join(run.runDir, 'draft-start.md'), 'utf8');
  assert.match(message, /Use the pdd-docs skill/); assert.ok(message.includes(join(skill, 'SKILL.md')));
  assert.match(message, /Steps: outline, write/);
});

test('after cancel a new run on the same issue gets a fresh worktree and branch, and the old ones stay', async t => {
  const f = await fixture(t);
  await f.run(); const old = f.record();
  writeFileSync(join(old.root, 'draft.txt'), 'old work\n'); f.git(old.root, 'add', '.'); f.git(old.root, 'commit', '-qm', 'old work');
  await cancelRun({ ref: '17', cwd: f.source }, f.ports);
  const again = await f.run();
  assert.equal(again.exitCode, 0, again.message); assert.match(again.message, /had a cancelled run/);
  const fresh = f.record();
  assert.equal(fresh.state, 'running'); assert.notEqual(fresh.runId, old.runId);
  assert.notEqual(fresh.root, old.root); assert.notEqual(fresh.branch, old.branch); assert.equal(existsSync(join(fresh.root, 'draft.txt')), false);
  assert.equal(readFileSync(join(old.root, 'draft.txt'), 'utf8'), 'old work\n'); assert.equal(f.git(old.root, 'branch', '--show-current'), old.branch);
  const archived = `${old.runDir}-cancelled-${old.runId.slice(0, 8)}`;
  assert.equal(JSON.parse(readFileSync(join(archived, 'status.json'), 'utf8')).state, 'cancelled');
  assert.deepEqual(fresh.previous.map(item => [item.root, item.branch, item.runDir]), [[old.root, old.branch, archived]]);
  const refused = await f.run();
  assert.equal(refused.exitCode, 1); assert.match(refused.message, /already has a run/);
});

const featureAreas = { version: 2, areas: [
  { name: 'story', steps: ['understand', 'visual', 'prompt-story'], optional: ['visual'], gate: 'approve' },
  { name: 'prompt-pr', steps: ['check', 'try'], optional: ['try'], gate: 'pr', then: 'ask-code' },
  { name: 'code', steps: ['build', 'verify'], optional: [], gate: 'pr' }] };
async function featureToPr1(t, promptText = 'Return two.\n') {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  const skill = join(f.source, '.agents', 'skills', 'pdd-feature');
  mkdirSync(skill, { recursive: true }); writeFileSync(join(skill, 'workflow.json'), JSON.stringify(featureAreas));
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), done = async (step, summary) => { f.tick(); const out = await stepDone({ step, summary, cwd: run.root }, f.agentPorts()); assert.equal(out.exitCode, 0, out.message); return out; };
  await done('understand', 'understood'); await done('visual', 'skipped');
  writeFileSync(join(run.root, 'feature.prompt.md'), promptText); f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'prompt and Story');
  await done('prompt-story', 'Story and cases written');
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const promptMessage = readFileSync(join(run.runDir, 'prompt-pr-start.md'), 'utf8');
  assert.match(promptMessage, /opens PR 1 \(prompt, Story and tests\)/);
  await done('check', 'Runtime check: ✓ 3 of 3 criteria · 10/10 checks · 1 AI call https://checks.example.test/r/k3y');
  const pr1 = await done('try', 'Try: https://checks.example.test/t/abc');
  return { f, run, done, pr1 };
}

test('feature: story, approve, PR 1 with prompt work only, then the person asks for code and PR 2 stacks on PR 1', async t => {
  const { f, run, done, pr1 } = await featureToPr1(t);
  assert.match(pr1.message, /pdd opens PR 1 now/); assert.match(pr1.message, /PR 1: https:\/\/github\.com\/example\/project\/pull\/23/);
  assert.match(pr1.message, /Runtime check: ✓ 3 of 3/); assert.match(pr1.message, /Try: https/);
  assert.match(pr1.message, /Do you want the code PR now, or stop here and merge PR 1 first\?/); assert.match(pr1.message, /workflow approve 17/);
  assert.equal(f.prs.length, 1);
  assert.equal(f.prs[0].title, 'Use value two (prompt, Story and tests)'); assert.equal(f.prs[0].baseRefName, 'main'); assert.equal(f.prs[0].headRefName, run.branch);
  assert.match(f.prs[0].body, /^Part of #17/); assert.doesNotMatch(f.prs[0].body, /Closes #17/);
  assert.match(f.prs[0].body, /Runtime report links expire after 7 days/); assert.doesNotMatch(f.prs[0].body, /## Verify/);
  let record = f.record();
  assert.equal(record.state, 'waiting'); assert.equal(record.gate.kind, 'ask-code'); assert.equal(record.waitingFor.what, 'Make the code PR now, or stop here and merge PR 1');
  const shown = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.match(shown.message, /PR 1 open/); assert.match(shown.message, /pdd workflow approve 17 any time to make the code PR/);

  f.tick();
  const code = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(code.exitCode, 0, code.message); assert.match(f.prompts.at(-1), /Make the code PR now/); assert.match(code.message, /stacked/);
  record = f.record();
  assert.equal(record.areas[record.area].name, 'code'); assert.equal(record.branch, `${run.branch}-code`); assert.equal(record.prBase, run.branch);
  assert.equal(f.git(run.root, 'branch', '--show-current'), `${run.branch}-code`); assert.equal(record.chats.length, 3);
  const codeMessage = readFileSync(join(run.runDir, 'code-start.md'), 'utf8');
  assert.match(codeMessage, /PR 1: https:\/\/github\.com\/example\/project\/pull\/23/); assert.match(codeMessage, /opens PR 2/);

  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'code');
  await done('build', 'value is two');
  writeFileSync(join(run.runDir, 'verify.md'), '$ node --test\n# pass 4\n');
  const pr2 = await done('verify', 'tests pass');
  assert.match(pr2.message, /pdd opens PR 2 now/); assert.match(pr2.message, /pull\/24/);
  assert.equal(f.prs.length, 2);
  assert.equal(f.prs[1].title, 'Use value two (code)'); assert.equal(f.prs[1].headRefName, `${run.branch}-code`); assert.equal(f.prs[1].baseRefName, run.branch);
  assert.match(f.prs[1].body, /^Closes #17/); assert.match(f.prs[1].body, /builds on PR 1: https:\/\/github\.com\/example\/project\/pull\/23/); assert.match(f.prs[1].body, /# pass 4/);
  assert.doesNotMatch(f.prs[1].body, /Story and cases written/, 'PR 2 lists only the code area');
  record = f.record(); assert.equal(record.stage.id, 'merge'); assert.deepEqual(record.pr.map(pr => pr.number), [23, 24]);
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /Next: Review and merge PR 1, then PR 2, on GitHub/);
  f.mergedNumbers.push(24); await runStatus({ ref: '17', cwd: f.source }, f.ports); assert.equal(f.record().state, 'completed');
});

test('feature: when PR 1 merges while the run waits, the run is done at PR 1, and approve later builds PR 2 on the default branch', async t => {
  const { f, run, done } = await featureToPr1(t);
  f.mergedNumbers.push(23);
  const shown = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.match(shown.message, /done at PR 1/); assert.equal(f.record().state, 'completed'); assert.equal(f.record().doneAt, 'PR 1');
  f.tick();
  const code = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(code.exitCode, 0, code.message); assert.match(code.message, /PR 1 is merged/);
  const record = f.record();
  assert.equal(record.state, 'running'); assert.equal(record.prBase, 'main');
  assert.equal(f.git(run.root, 'rev-parse', 'HEAD'), f.prs[0].headRefOid, 'the code branch starts from the merged prompts');
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'code');
  await done('build', 'value is two'); await done('verify', 'tests pass');
  assert.equal(f.prs[1].baseRefName, 'main'); assert.doesNotMatch(f.prs[1].body, /stacked/);
});

const runtimePrompt = status => ['# Value', '', 'Return two.', '', '<details><summary>Runtime interface</summary>', '', '```json',
  JSON.stringify({ status, prose_sha256: '', entries: [] }), '```', '</details>', ''].join('\n');

test('draft prompts in PR 1 are named in its body and status, and block the code PR until the person approves them', async t => {
  const { f, run } = await featureToPr1(t, runtimePrompt('draft'));
  assert.match(f.prs[0].body, /Draft prompts: feature\.prompt\.md\. Approve them before you merge\./);
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /Draft prompts: feature\.prompt\.md\. Approve them before you merge\./);
  f.tick();
  const refused = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(refused.exitCode, 1); assert.match(refused.message, /Approve the draft prompts first: feature\.prompt\.md/);
  assert.equal(f.prompts.length, 1, 'no y/N question while drafts remain'); assert.equal(f.record().chats.length, 2); assert.equal(f.record().area, 1);
  assert.equal(readFileSync(join(run.root, 'feature.prompt.md'), 'utf8'), runtimePrompt('draft'), 'pdd never sets approved itself');
  writeFileSync(join(run.root, 'feature.prompt.md'), runtimePrompt('approved')); f.git(run.root, 'commit', '-qam', 'person approved the prompt');
  assert.doesNotMatch((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /Draft prompts/);
  f.tick();
  const code = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(code.exitCode, 0, code.message); assert.equal(f.record().areas[f.record().area].name, 'code');
});

test('status --all lists every run on this machine across repositories, person-waiting first, and hides cancelled runs', async t => {
  const a = await fixture(t), b = await fixture(t, { name: 'bug' });
  b.ports.stateDir = a.state;
  for (const f of [a, b]) f.ports.timeZone = 'UTC';
  // Repository A: run 17 waits for approval. Repository B: run 17 works on reproduce.
  await a.run(); a.tick(); await stepDone({ step: 'scope', summary: 'plan', cwd: a.record().root }, a.agentPorts());
  b.clock += 60000; await b.run();
  // A third run that is cancelled, and a repository that is gone, are not errors.
  const index = JSON.parse(readFileSync(join(a.state, 'runs.json'), 'utf8'));
  index.runs.push({ repo: 'gone/repo', number: 5, runDir: join(a.base, 'gone', '.git', 'pdd', 'runs', '5') });
  writeFileSync(join(a.state, 'runs.json'), JSON.stringify(index));
  const outside = join(a.base, 'home');
  for (const input of [{ all: true, cwd: a.source }, { cwd: outside }]) {
    const out = await runStatus(input, a.ports);
    assert.equal(out.exitCode, 0, out.message);
    const lines = out.message.split('\n');
    assert.equal(lines.length, 3, out.message);
    assert.match(lines[0], /^example\/project#17 · small-change · plan · waiting for you: approve the plan · Oct 27, 17:00$/);
    assert.match(lines[1], /^example\/project#17 · bug · story · agent working on reproduce · Oct 27, 17:01$/);
    assert.equal(lines[2], 'Open one: pdd workflow open example/project#17');
  }
  await cancelRun({ ref: '17', cwd: b.source }, b.ports);
  const hidden = await runStatus({ all: true, cwd: outside }, a.ports);
  assert.match(hidden.message, /1 cancelled run hidden; add --cancelled to see it/); assert.doesNotMatch(hidden.message, /· bug ·/);
  const shown = await runStatus({ all: true, cancelled: true, cwd: outside }, a.ports);
  assert.match(shown.message.split('\n')[1], /^example\/project#17 · bug · story · cancelled · /);
  const json = JSON.parse((await runStatus({ all: true, json: true, cancelled: true, cwd: outside }, a.ports)).message);
  assert.deepEqual(json.runs.map(run => [run.workflow, run.group, run.words]), [['small-change', 'waiting', 'waiting for you: approve the plan'], ['bug', 'cancelled', 'cancelled']]);
  assert.equal(json.runs[0].ref, 'example/project#17'); assert.equal(typeof json.runs[0].updatedAt, 'number'); assert.ok(json.runs[0].runDir);
  // Inside a repository, plain status stays that repository's runs.
  assert.doesNotMatch((await runStatus({ cwd: a.source }, a.ports)).message, /· bug ·/);
});

test('status --all shows PR states, done runs last, and reads the Herdr registry for repositories missing from the index', async t => {
  const f = await fixture(t);
  f.ports.timeZone = 'UTC';
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'two');
  await stepDone({ step: 'change', summary: 'two', cwd: run.root }, f.agentPorts()); await stepDone({ step: 'verify', summary: 'ok', cwd: run.root }, f.agentPorts());
  rmSync(join(f.state, 'runs.json'));
  const open = await runStatus({ all: true, cwd: f.source }, f.ports);
  assert.match(open.message, /^example\/project#17 · small-change · build · PR open · PR #23 · /);
  const seq = f.record().journalSeq; f.tick(3600000);
  await runStatus({ all: true, cwd: f.source }, f.ports);
  assert.equal(f.record().journalSeq, seq, 'reading an unchanged PR does not touch the run');
  f.merged = true;
  const merged = await runStatus({ all: true, cwd: f.source }, f.ports);
  assert.match(merged.message, /^example\/project#17 · small-change · build · done · PR #23 · /);
});

test('R4: at the code gate a chat reply needs a yes-word; other words are refused', async t => {
  const { f } = await featureToPr1(t);
  const reply = text => f.agentPorts({ readApprovalEvidence: async () => ({ ok: true, decision: 'approve', agent: 'codex', sessionId: '11111111-1111-4111-8111-111111111111', userMessage: text, userMessageAt: f.clock - 1 }) });
  f.tick();
  for (const text of ['sounds good', 'hmm, let me think']) {
    const refused = await approveRun({ ref: '17', cwd: f.source }, reply(text));
    assert.equal(refused.exitCode, 1); assert.equal(refused.message, 'Not sure you approved. Run `pdd workflow approve 17` in your terminal.');
    assert.equal(f.record().areas[f.record().area].name, 'prompt-pr');
  }
  const ok = await approveRun({ ref: '17', cwd: f.source }, reply('Yes, build the code.'));
  assert.equal(ok.exitCode, 0, ok.message); assert.equal(f.record().areas[f.record().area].name, 'code');
});

test('R5: Try links (/s/<token>/) are removed from PR bodies; report links (/r/) stay', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'two');
  await stepDone({ step: 'change', summary: 'Try it: https://rt.example.test/s/AbC_123-xyz/ and https://rt.example.test/s/QqQ/?tab=call', cwd: run.root }, f.agentPorts());
  writeFileSync(join(run.runDir, 'verify.md'), 'Try: https://rt.example.test/s/TTTTTTTT/\nReport: https://rt.example.test/r/360b7197\n');
  await stepDone({ step: 'verify', summary: 'ok', cwd: run.root }, f.agentPorts());
  const body = f.prs[0].body;
  assert.doesNotMatch(body, /\/s\//); assert.equal(body.split('(Try link removed)').length - 1, 3);
  assert.match(body, /https:\/\/rt\.example\.test\/r\/360b7197/);
});

for (const state of ['unknown', 'closed']) test(`R7: when PR 1 is ${state}, approve makes no code branch and changes nothing`, async t => {
  const { f, run } = await featureToPr1(t);
  const before = f.record();
  f.tick();
  const refused = await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, readPrStatus: async () => ({ state, ci: 'unknown' }) });
  assert.equal(refused.exitCode, 1); assert.match(refused.message, new RegExp(`PR 1 is ${state}`)); assert.match(refused.message, /pdd workflow approve 17/);
  const after = f.record();
  assert.deepEqual([after.area, after.branch, after.gate, after.chats.length, after.decisions.length], [before.area, before.branch, before.gate, before.chats.length, before.decisions.length]);
  assert.equal(f.git(run.root, 'branch', '--list', `${run.branch}-code`), ''); assert.equal(f.git(run.root, 'branch', '--show-current'), run.branch);
});

test('R9: a session id that is not a UUID is never stored or put in a shell command', async t => {
  const f = await fixture(t);
  await f.run(); const chat = f.record().chats[0], pane = f.herdr.paneOf(chat);
  pane.agent.agent_session.value = "x'; touch /tmp/pwned; '";
  assert.equal((await openRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' } })).exitCode, 0);
  assert.equal(f.record().chats[0].session.id, chat.session.id);
  pane.agent = null;
  const record = JSON.parse(readFileSync(join(f.record().runDir, 'status.json'), 'utf8'));
  record.chats[0].session = { agent: 'claude', id: '$(touch /tmp/pwned)' }; writeFileSync(join(record.runDir, 'status.json'), JSON.stringify(record));
  const refused = await openRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' }, findNativeSessions: async () => [] });
  assert.equal(refused.exitCode, 1); assert.equal(pane.commands.length, 1, 'no resume command was typed');
});

test('code area build → verify → formal: a loop back to build only warns, asks for verify again, and PR 2 opens after the last step', async t => {
  const f = await fixture(t, { name: 'bug', agent: 'codex' });
  const skill = join(f.source, '.agents', 'skills', 'pdd-bug');
  mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [
    { name: 'story', steps: ['reproduce', 'prompt-story'], optional: [], gate: 'approve' },
    { name: 'prompt-pr', steps: ['check', 'try'], optional: ['try'], gate: 'pr', then: 'ask-code' },
    { name: 'code', steps: ['build', 'verify', 'formal'], optional: [], gate: 'pr' }] }));
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), done = async (step, summary) => { f.tick(); const out = await stepDone({ step, summary, cwd: run.root }, f.agentPorts()); assert.equal(out.exitCode, 0, out.message); return out; };
  await done('reproduce', 'seen'); writeFileSync(join(run.root, 'story.md'), 'Story\n'); f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'story');
  await done('prompt-story', 'Story and cases'); f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  await done('check', 'Runtime check: ✓ 1 of 1'); await done('try', 'skipped'); f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 3;\n'); f.git(run.root, 'commit', '-qam', 'first try');
  assert.match((await done('build', 'first build')).message, /Next step: verify/);
  assert.match((await done('verify', '✗ 2 vectors fail')).message, /Next step: formal/);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'second try');
  const again = await done('build', 'second build');
  assert.match(again.message, /warning: build ran again after verify/); assert.match(again.message, /Next step: verify/);
  assert.equal(f.prs.length, 1, 'no PR 2 before the last step');
  assert.equal(f.record().done.verify, undefined, 'the old verify result no longer counts');
  writeFileSync(join(run.runDir, 'verify.md'), '| case | expected | code | result |\n|---|---|---|---|\n| 1 | 2 | 2 | same |\n\n## Formal check\nProved (bounded): 0..999, planted mistake caught.\n');
  assert.match((await done('verify', '✓ 2 vectors same')).message, /Next step: formal/);
  assert.equal(f.prs.length, 1);
  const pr2 = await done('formal', 'Proved (bounded)');
  assert.match(pr2.message, /pdd opens PR 2 now/); assert.equal(f.prs.length, 2);
  assert.match(f.prs[1].body, /\| 1 \| 2 \| 2 \| same \|/); assert.match(f.prs[1].body, /Proved \(bounded\): 0\.\.999/);
  assert.match(f.prs[1].body, /\*\*formal\*\*: Proved \(bounded\)/); assert.doesNotMatch(f.prs[1].body, /first build|✗ 2 vectors fail/);
});
