import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, existsSync, realpathSync, chmodSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { startRun, stepDone, approveRun, changeRun, cancelRun, runStatus, openRun, askPerson } from '../src/workflow-runner.mjs';

const exec = promisify(callbackExec);
const packageRoot = resolve(import.meta.dirname, '..');
const issueUrl = 'https://github.com/example/project/issues/17';
// Steps after verify in the bundled small-change build area (formal since 0.1.3); the PR opens after the last one.
const smallChangeAfterVerify = JSON.parse(readFileSync(join(packageRoot, 'skills/pdd-small-change/workflow.json'), 'utf8')).areas.at(-1).steps
  .slice(JSON.parse(readFileSync(join(packageRoot, 'skills/pdd-small-change/workflow.json'), 'utf8')).areas.at(-1).steps.indexOf('verify') + 1);
async function lastSteps(f, run, out) {
  for (const step of smallChangeAfterVerify) { f.tick(); out = await stepDone({ step, summary: `${step} done`, cwd: run.root }, f.agentPorts()); }
  return out;
}

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
      return { id: 'cli:workspace:create', result: { workspace: w, tab:t, root_pane:h.panes.at(-1) } };
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
    if (group === 'agent' && verb === 'prompt') { const p = h.panes.find(p => p.pane_id === rest[0]); if (!p?.agent) fail('agent_not_found'); if (p.agent.agent_status === 'blocked') fail('agent_blocked'); p.agent.prompts.push(rest[1]); return { result: { type: 'agent_prompted' } }; }
    fail(`unexpected herdr ${args.join(' ')}`);
  };
  h.paneOf = chat => h.panes.find(p => p.pane_id === chat.paneId);
  // Every chat finished its turn (after done, the chat writes its gate message and then waits).
  h.idle = () => { for (const p of h.panes) if (p.agent) p.agent.agent_status = 'idle'; };
  return h;
}

async function fixture(t, { agent = 'claude', name = 'small-change' } = {}) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-runner-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const source = join(base, 'project'), state = join(base, 'state'), home = join(base, 'home');
  for (const dir of [source, state, home, join(home, '.claude')]) mkdirSync(dir);
  const git = (cwd, ...args) => execFileSync('git', args, { cwd, encoding: 'utf8' }).trim();
  git(source, 'init', '-q', '-b', 'main'); git(source, 'config', 'user.email', 'test@example.invalid'); git(source, 'config', 'user.name', 'Runner Test');
  git(source, 'remote', 'add', 'origin', 'https://github.com/example/project.git');
  writeFileSync(join(source, 'value.mjs'), 'export const value = 1;\n'); git(source, 'add', '.'); git(source, 'commit', '-qm', 'initial');
  git(source, 'update-ref', 'refs/remotes/origin/main', git(source, 'rev-parse', 'HEAD'));
  const f = { base, source, state, git, herdr: fakeHerdr(), prs: [], pushes: [], edits: [], fetches: 0, clock: Date.parse('2026-10-27T17:00:00Z'), ci: [], merged: false, mergedNumbers: [] };
  async function execFile(file, args, opts) {
    if (file === 'git' && args[0] === 'push') {
      f.pushes.push(args);
      // Like a real push, keep the remote-tracking branch current.
      const [from, to] = args[2].split(':'), sha = (await exec('git', ['rev-parse', from], { cwd: opts.cwd })).stdout.trim();
      await exec('git', ['update-ref', to.replace('refs/heads/', 'refs/remotes/origin/'), sha], { cwd: opts.cwd });
      return { stdout: '' };
    }
    if (file === 'git' && args[0] === 'ls-remote') {
      // The remote branch as the last push left it (pushes keep the remote-tracking branch current).
      const ref = args.at(-1), local = await exec('git', ['rev-parse', '--verify', '--quiet', ref.replace('refs/heads/', 'refs/remotes/origin/')], { cwd: opts.cwd }).catch(() => ({ stdout: '' }));
      return local.stdout.trim() ? { stdout: `${local.stdout.trim()}\t${ref}\n` } : { stdout: '', code: 2 };
    }
    if (file === 'git' && args[0] === 'fetch') {
      f.fetches++;
      const branch = args[2].replace(/^refs\/heads\//, '').split(':')[0];
      const merged = f.prs.find(pr => f.mergedNumbers.includes(pr.number) && pr.baseRefName === branch);
      if (merged) await exec('git', ['update-ref', `refs/remotes/origin/${branch}`, merged.headRefOid], { cwd: opts.cwd });
      return { stdout: '' };
    }
    if (file !== 'gh') return exec(file, args, { ...opts, encoding: 'utf8' });
    if (args[0] === 'repo' && args[1] === 'view') return { stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: 'main' }, url: 'https://github.com/example/project' }) };
    if (args[0] === 'api' && args[1] === 'repos/example/project/issues/17') return { stdout: JSON.stringify({ number: 17, html_url: issueUrl, title: 'Use value two', body: f.issueBody ?? 'Value must be two.' }) };
    if (args[0] === 'pr' && args[1] === 'create' && f.createError) { const stderr = f.createError; f.createError = null; return { stdout: '', stderr, code: 1 }; }
    if (args[0] === 'pr' && args[1] === 'create') {
      const value = flag => args[args.indexOf(flag) + 1];
      const number = 23 + f.prs.length;
      const pr = { number, url: `https://github.com/example/project/pull/${number}`, state: 'OPEN', headRefName: value('--head'), baseRefName: value('--base'),
        headRefOid: (await exec('git', ['rev-parse', 'HEAD'], { cwd: opts.cwd })).stdout.trim(), body: String(opts.input ?? ''), title: value('--title'),
        headRepository: { name: 'project' }, headRepositoryOwner: { login: 'example' }, isCrossRepository: false, mergeCommit: null };
      f.prs.push(pr); return { stdout: pr.url + '\n' };
    }
    if (args[0] === 'pr' && args[1] === 'list') {
      const head = args.includes('--head') ? args[args.indexOf('--head') + 1] : null, search = args.includes('--search') ? args[args.indexOf('--search') + 1].split('"')[1] : null;
      return { stdout: JSON.stringify(f.prs.filter(pr => (!head || pr.headRefName === head) && (!search || pr.body.includes(search)))) };
    }
    if (args[0] === 'pr' && args[1] === 'view') {
      const pr = f.prs.find(item => item.url === args[2]);
      return { stdout: JSON.stringify({ state: f.merged || f.mergedNumbers.includes(pr?.number) ? 'MERGED' : 'OPEN', mergedAt: null, statusCheckRollup: f.ci, body: pr?.body }) };
    }
    if (args[0] === 'pr' && args[1] === 'edit') {
      const pr = f.prs.find(item => item.url === args[2]) ?? assert.fail(`no PR ${args[2]}`);
      pr.body = String(opts.input ?? ''); f.edits.push(pr.number); return { stdout: '' };
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
  for (const part of [`Use the pdd-small-change skill: ${join(packageRoot, 'skills/pdd-small-change/SKILL.md')}`, '#17', 'Use value two', issueUrl, run.root, run.runDir, 'plan', 'scope', '/abs/node /abs/pdd.mjs workflow done'])
    assert.ok(message.includes(part), part);
  assert.ok(message.split('\n').length <= 14, message);
  assert.doesNotMatch(message, /Prompting guide/);
  assert.equal(f.herdr.tabs.find(tab => tab.tab_id === first.tabId).label, 'plan');
  assert.equal(f.herdr.workspaces.find(w => w.workspace_id === first.workspaceId).label, 'project#17 small-change');

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
  // Installed copies (for example from npx skills add) can be older than this pdd, so the chat reads the package's copies.
  for (const text of [message, buildMessage]) assert.ok(text.includes(`Read the PDD skills (pdd-prompting too) from ${join(packageRoot, 'skills')}: an installed copy with the same name may be older.`), text);

  f.tick();
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'Use value two');
  const next = await stepDone({ step: 'change', summary: 'value is 2', cwd: run.root }, f.agentPorts());
  assert.match(next.message, /Next step: verify/); assert.match(next.message, /workflow done verify/);
  assert.equal(f.prs.length, 0);

  f.tick();
  writeFileSync(join(run.runDir, 'verify.md'), '$ node --test\n# pass 3\n');
  writeFileSync(join(run.root, 'notes.txt'), 'left behind\n');
  const opened = await lastSteps(f, run, await stepDone({ step: 'verify', summary: 'tests pass', cwd: run.root }, f.agentPorts()));
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
  const bundled = JSON.parse(readFileSync(join(packageRoot, `skills/pdd-${name}/workflow.json`), 'utf8')).areas;
  const areas = bundled.map(area => [area.name, area.steps]);
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
      // A pr area opens its PR after its last step, unless the person approves first ("before":"approve", Try before PR 1).
      assert.equal(f.prs.length, bundled.slice(0, index + 1).filter((area, at) => area.gate === 'pr' && !(at === index && area.before === 'approve')).length);
      if (index < areas.length - 1) {
        assert.equal(f.record().state, 'waiting');
        f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
        assert.equal(f.record().chats.length, index + 2);
      }
    }
    assert.equal(f.prs.length, 2); assert.equal(f.record().stage.id, 'merge');
    assert.ok(f.prs[0].body.includes(`Runtime check: ✓ 3 of 3 criteria · 10/10 checks · 1 AI call ${report}`), 'the check result stays in PR 1');
    assert.match(f.prs[0].body, /^Runtime check: ✓ 3 of 3 criteria · 10\/10 checks · 1 AI call\nReport: https:\/\/checks\.example\.test\/r\/k3y-123 \(report links expire after 7 days\)/);
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
  assert.deepEqual(f.herdr.workspaces, [], 'the repository workspace closes too once no run uses it');
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
async function featureToPr1(t, promptText = 'Return two.\n', base, issueBody) {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  f.issueBody = issueBody;
  if (base) { topicBase(f, base); f.run = () => startRun({ name: 'feature', issue: '17', agent: 'codex', base, cwd: f.source, packageRoot }, f.ports); }
  const skill = join(f.source, '.agents', 'skills', 'pdd-feature');
  mkdirSync(skill, { recursive: true }); writeFileSync(join(skill, 'workflow.json'), JSON.stringify(featureAreas));
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), done = async (step, summary) => { f.tick(); const out = await stepDone({ step, summary, cwd: run.root }, f.agentPorts()); assert.equal(out.exitCode, 0, out.message); return out; };
  await done('understand', 'understood'); await done('visual', 'skipped');
  writeFileSync(join(run.root, 'feature.prompt.md'), promptText); mkdirSync(join(run.root, 'tests'));
  writeFileSync(join(run.root, 'tests', 'value.json'), JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', criteria: [], initial_world: {}, steps: [] }));
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'prompt, Story and tests');
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
  assert.match(f.prs[0].body, /^Runtime check: ✓ 3 of 3 criteria · 10\/10 checks · 1 AI call\nReport: https:\/\/checks\.example\.test\/r\/k3y \(report links expire after 7 days\)\n\nPart of #17/);
  assert.doesNotMatch(f.prs[0].body, /Closes #17/); assert.doesNotMatch(f.prs[0].body, /## Verify/);
  let record = f.record();
  assert.equal(record.state, 'waiting'); assert.equal(record.gate.kind, 'ask-code'); assert.equal(record.waitingFor.what, 'Make the code PR now, or stop here and merge PR 1');
  f.herdr.idle();
  const shown = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.match(shown.message, /PR 1 open/); assert.match(shown.message, /To make the code PR later, run `pdd workflow approve 17`\./);
  // The chat gets the exact sentence to say when the person stops (testers saw it dropped when it was a hint).
  assert.match(pr1.message, /If they stop, tell them exactly: "PR 1 is open: https:\/\/github\.com\/example\/project\/pull\/23\. To make the code PR later, run `pdd workflow approve 17`\."/);

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
  assert.equal(f.prs[1].body.split('\n')[0], 'Old-code proof: not run.');
  assert.ok(f.prs[1].body.includes(`Static inventory only; tests were not run.\nTest inventory commits: ${run.baseSha.slice(0,7)} → ${f.git(run.root, 'rev-parse', 'HEAD').slice(0,7)}.`));
  const inventoryAt = f.prs[1].body.indexOf('Tests vs base:'), issueAt = f.prs[1].body.indexOf('\nCloses #17\n');
  assert.ok(f.prs[1].body.indexOf('Old-code proof: not run.') < inventoryAt && inventoryAt < issueAt);
  assert.match(f.prs[1].body, /^Closes #17$/m); assert.match(f.prs[1].body, /builds on PR 1: https:\/\/github\.com\/example\/project\/pull\/23/); assert.match(f.prs[1].body, /# pass 4/);
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
  assert.equal(refused.exitCode, 1); assert.match(refused.message, /^Approve the prompt first: cd .+ && pdd approve feature\.prompt\.md\. Then run pdd workflow approve 17 to start the code PR\.$/);
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
  await a.run(); a.tick(); await stepDone({ step: 'scope', summary: 'plan', cwd: a.record().root }, a.agentPorts()); a.herdr.idle();
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
    assert.equal(lines.length, 4, out.message);
    assert.match(lines[0], /^example\/project#17 · small-change · plan · waiting for you: approve the plan · Oct 27, 17:00$/);
    assert.match(lines[1], /^example\/project#17 · bug · story · agent working on reproduce · Oct 27, 17:01$/);
    assert.equal(lines[2], 'Review without resuming: pdd workflow view example/project#17');
    assert.equal(lines[3], 'Open one: pdd workflow open example/project#17');
  }
  await cancelRun({ ref: '17', cwd: b.source }, b.ports);
  const hidden = await runStatus({ all: true, cwd: outside }, a.ports);
  assert.match(hidden.message, /1 cancelled run hidden; add --cancelled to see it/); assert.doesNotMatch(hidden.message, /· bug ·/);
  const shown = await runStatus({ all: true, cancelled: true, cwd: outside }, a.ports);
  assert.match(shown.message.split('\n')[1], /^example\/project#17 · bug · story · cancelled · /);
  const json = JSON.parse((await runStatus({ all: true, json: true, cancelled: true, cwd: outside }, a.ports)).message);
  assert.deepEqual(json.runs.map(run => [run.workflow, run.group, run.words]), [['small-change', 'waiting', 'waiting for you: approve the plan'], ['bug', 'cancelled', 'cancelled']]);
  assert.equal(json.runs[0].ref, 'example/project#17'); assert.equal(typeof json.runs[0].updatedAt, 'number'); assert.ok(json.runs[0].runDir);
  assert.equal(json.runs[0].viewCommand, 'pdd workflow view example/project#17');
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
  await stepDone({ step: 'change', summary: 'two', cwd: run.root }, f.agentPorts()); await lastSteps(f, run, await stepDone({ step: 'verify', summary: 'ok', cwd: run.root }, f.agentPorts()));
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
  await lastSteps(f, run, await stepDone({ step: 'verify', summary: 'ok', cwd: run.root }, f.agentPorts()));
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

// Seen in a real run: the person said "I approve the prompt. Yes, build the code."; the chat committed the approval
// and ran done again to push it to PR 1, which moved the gate past the person's answer.
test('pushing more commits to PR 1 at the code gate keeps the gate time, so the person need not say yes twice', async t => {
  const { f, run } = await featureToPr1(t);
  const gateAt = f.record().gate.at;
  f.tick(); writeFileSync(join(run.root, 'feature.prompt.md'), 'Return two. Approved.\n'); f.git(run.root, 'commit', '-qam', 'person approved the prompt');
  const pushed = await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  assert.match(pushed.message, /Pushed the new commits to PR 1/); assert.equal(f.record().gate.at, gateAt); assert.equal(f.prs.length, 1);
  const requests = [];
  f.tick();
  const code = await approveRun({ ref: '17', cwd: run.root }, f.agentPorts({ readApprovalEvidence: async request => { requests.push(request);
    return { ok: true, decision: 'approve', agent: 'codex', sessionId: '11111111-1111-4111-8111-111111111111', userMessage: 'I approve the prompt. Yes, build the code.', userMessageAt: gateAt + 1 }; } }));
  assert.equal(code.exitCode, 0, code.message); assert.equal(requests[0].gateAskedAt, gateAt);
});

test('a first verify.md line that starts with ✗ stays directly below the lifted evidence', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'two');
  await stepDone({ step: 'change', summary: 'two', cwd: run.root }, f.agentPorts());
  writeFileSync(join(run.runDir, 'verify.md'), '\n✗ 2 vectors fail\n\n| case | result |\n|---|---|\n| a | different |\n');
  await lastSteps(f, run, await stepDone({ step: 'verify', summary: 'two cases still fail', cwd: run.root }, f.agentPorts()));
  assert.equal(f.prs[0].body.split('\n')[0],'Old-code proof: not run.');assert.match(f.prs[0].body,/Test inventory commits: [^\n]+\n✗ 2 vectors fail/); assert.match(f.prs[0].body, /\| a \| different \|/);
});

// Seen with a CLI tester: the chat asked a question in the middle of a step, status still said "the agent works",
// and pdd workflow changes could not reach the chat while it showed a question dialog.
test('ask marks the run as waiting for the person; changes answers it in the same chat; the next done clears it', async t => {
  const f = await fixture(t);
  f.ports.timeZone = 'UTC';
  await f.run(); const run = f.record(), pane = f.herdr.paneOf(run.chats[0]); f.tick();
  const asked = await askPerson({ text: 'Should -h also print the usage?', cwd: run.root }, f.agentPorts());
  assert.equal(asked.exitCode, 0, asked.message);
  assert.match(asked.message, /plain chat message/); assert.match(asked.message, /end your turn/); assert.match(asked.message, /pdd workflow changes 17/);
  let record = f.record();
  assert.equal(record.question.text, 'Should -h also print the usage?'); assert.equal(record.state, 'waiting');
  assert.deepEqual(record.waitingFor, { decisions: ['changes'], what: 'Should -h also print the usage?' });
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /State: waiting for you: Should -h also print the usage\?/);
  assert.match((await runStatus({ all: true, cwd: f.source }, f.ports)).message, /^example\/project#17 · small-change · plan · waiting for you: Should -h also print the usage\? · /);
  f.tick();
  const answered = await changeRun({ ref: '17', text: 'Yes, the same text as --help.', cwd: f.source }, f.ports);
  assert.equal(answered.exitCode, 0, answered.message); assert.match(answered.message, /answer/);
  assert.match(pane.agent.prompts.at(-1), /^The person answers your question: Yes, the same text as --help\./);
  record = f.record(); assert.equal(record.question, null); assert.equal(record.state, 'running');
  await askPerson({ text: 'One more?', cwd: run.root }, f.agentPorts());
  f.tick(); await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  assert.equal(f.record().question, null); assert.equal(f.record().gate.kind, 'approve');
  const outside = await askPerson({ text: 'x', cwd: f.source }, f.agentPorts());
  assert.equal(outside.exitCode, 1); assert.match(outside.message, /worktree/);
});

test('a chat that shows a question dialog is waiting for the person in status, and changes says to answer in the chat', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(), pane = f.herdr.paneOf(run.chats[0]);
  pane.agent.agent_status = 'blocked';
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /State: waiting for you: the chat asks a question in its window \(pdd workflow open 17\)/);
  const refused = await changeRun({ ref: '17', text: 'yes', cwd: f.source }, f.ports);
  assert.equal(refused.exitCode, 1); assert.match(refused.message, /question dialog/); assert.match(refused.message, /pdd workflow open 17/);
  pane.agent.agent_status = 'idle';
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /State: the agent works on scope/);
});

// 0.1.4 #13: the person tries the prompt and approves before PR 1 opens.
async function featureAtTryGate(t, { prompt = 'Return two.\n', tests = false, tried = 'Try: https://rt.example.test/s/TOKEN/' } = {}) {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  const skill = join(f.source, '.agents', 'skills', 'pdd-feature');
  mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [
    { name: 'story', steps: ['understand', 'prompt-story'], optional: [], gate: 'approve' },
    { name: 'prompt-pr', steps: ['check', 'try'], optional: ['try'], gate: 'pr', before: 'approve', then: 'ask-code' },
    { name: 'code', steps: ['build', 'verify'], optional: [], gate: 'pr' }] }));
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), done = async (step, summary) => { f.tick(); const out = await stepDone({ step, summary, cwd: run.root }, f.agentPorts()); assert.equal(out.exitCode, 0, out.message); return out; };
  await done('understand', 'ok'); writeFileSync(join(run.root, 'feature.prompt.md'), prompt);
  if (tests) { mkdirSync(join(run.root, 'tests')); writeFileSync(join(run.root, 'tests', 'value.json'), JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', criteria: [], initial_world: {}, steps: [] })); }
  f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'prompt');
  await done('prompt-story', 'Story'); f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  await done('check', 'Runtime check: ✓ 2 of 2 criteria · Report: https://rt.example.test/r/abc');
  const gate = await done('try', tried);
  return { f, run, done, gate };
}

test('#13: after check and try the chat asks the person to try and approve; PR 1 opens only after approval, then the code question', async t => {
  const { f, run, gate } = await featureAtTryGate(t);
  assert.equal(f.prs.length, 0, 'no PR 1 before the person approves');
  assert.match(gate.message, /Runtime check line/); assert.match(gate.message, /Try link/); assert.match(gate.message, /approve/); assert.match(gate.message, /Stop/);
  assert.doesNotMatch(gate.message, /pdd opens PR 1 now/);
  let record = f.record();
  assert.equal(record.gate.kind, 'approve-pr'); assert.equal(record.state, 'waiting');
  f.herdr.idle();
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /waiting for you: try it, then approve to open PR 1/);
  f.tick();
  const opened = await approveRun({ ref: '17', cwd: run.root }, f.agentPorts({ readApprovalEvidence: async () => ({ ok: true, decision: 'approve', agent: 'codex', sessionId: '11111111-1111-4111-8111-111111111111', userMessage: 'Tried it, it splits right.', userMessageAt: f.clock - 1 }) }));
  assert.equal(opened.exitCode, 0, opened.message);
  assert.equal(f.prs.length, 1); assert.match(opened.message, /PR 1: https:\/\/github\.com\/example\/project\/pull\/23/);
  assert.match(opened.message, /Do you want the code PR now, or stop here and merge PR 1 first\?/);
  record = f.record();
  assert.equal(record.gate.kind, 'ask-code'); assert.equal(record.areas[record.area].name, 'prompt-pr'); assert.equal(record.chats.length, 2);
  assert.equal(record.decisions.at(-1).stage, 'prompt-pr');
  assert.doesNotMatch(f.prs[0].body, /\/s\/TOKEN/);
  f.tick();
  const code = await approveRun({ ref: '17', cwd: run.root }, f.agentPorts({ readApprovalEvidence: async () => ({ ok: true, decision: 'approve', agent: 'codex', sessionId: '11111111-1111-4111-8111-111111111111', userMessage: 'Yes, build the code.', userMessageAt: f.clock - 1 }) }));
  assert.equal(code.exitCode, 0, code.message); assert.equal(f.record().areas[f.record().area].name, 'code');
});

test('#13: from the terminal, approve opens PR 1 and asks about the code PR; no stops with the plain approve-later line', async t => {
  const { f, run } = await featureAtTryGate(t);
  const pane = f.herdr.paneOf(f.record().chats[1]);
  const answers = [true, false]; f.ports.confirm = async question => { f.prompts.push(question); return answers.shift(); };
  f.tick();
  const stopped = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(stopped.exitCode, 0, stopped.message);
  assert.match(f.prompts.at(-2), /Approve the prompt-pr area and open PR 1 for example\/project#17/); assert.match(f.prompts.at(-1), /Make the code PR now/);
  assert.equal(f.prs.length, 1); assert.match(stopped.message, /PR 1: https:\/\/github\.com\/example\/project\/pull\/23/);
  assert.match(stopped.message, /To make the code PR later, run `pdd workflow approve 17`\./);
  assert.match(pane.agent.prompts.at(-1), /pdd opened PR 1: https:\/\/github\.com\/example\/project\/pull\/23/);
  assert.match(pane.agent.prompts.at(-1), /To make the code PR later, run `pdd workflow approve 17`\./);
  assert.equal(f.record().gate.kind, 'ask-code'); assert.equal(f.record().chats.length, 2);
  f.ports.confirm = async question => { f.prompts.push(question); return true; };
  f.tick();
  const code = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(code.exitCode, 0, code.message); assert.match(f.prompts.at(-1), /Make the code PR now/); assert.equal(f.record().areas[f.record().area].name, 'code');
  assert.equal(f.git(run.root, 'branch', '--show-current'), `${run.branch}-code`);
});

// 0.1.4 #18: PR 1 starts with the Runtime check line and its report link; steps are one short line; no local paths.
test('#18: the PR body puts the Runtime check and report link on top, cuts steps to one short line, and hides local paths', async t => {
  const { f, run } = await featureAtTryGate(t);
  const local = `${run.root}/test/x.test.mjs`;
  writeFileSync(join(run.runDir, 'verify.md'), `Old notes from ${run.runDir}/check.md\n`);
  f.tick();
  const done = await stepDone({ step: 'check', summary: `Runtime check (DRAFT): ✓ 3 of 3 criteria · 18/18 checks · 12 AI calls; Report: https://rt.example.test/r/d379-42; ran from ${local} with /Users/someone/toolbox/node/bin/node and /home/ci/bin/node ${'and a very long tail of words that keeps going '.repeat(8)}`, cwd: run.root }, f.agentPorts());
  assert.equal(done.exitCode, 0, done.message);
  f.tick(); await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  f.tick(); f.ports.confirm = async () => false;
  await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  const body = f.prs[0].body, top = body.split('\n');
  assert.equal(top[0], 'Runtime check (DRAFT): ✓ 3 of 3 criteria · 18/18 checks · 12 AI calls');
  assert.equal(top[1], 'Report: https://rt.example.test/r/d379-42 (report links expire after 7 days)');
  assert.equal(top[3], 'Part of #17');
  for (const row of body.split('\n').filter(row => row.startsWith('- **'))) assert.ok(row.length <= 220, row);
  assert.doesNotMatch(body, /\/Users\/|\/home\/|\/private\/|\/var\/folders/);
  assert.doesNotMatch(body, /## Verify/, 'PR 1 has no verify step, so no verify.md');
  assert.match(body, /test\/x\.test\.mjs/, 'a worktree path stays as a repo path');
});

test('cancel keeps the repository workspace while another run of that repository is open, and a later run gets a new one', async t => {
  const f = await fixture(t);
  await f.run(); const first = f.record();
  // A second issue in the same repository.
  const execFile = f.ports.execFile;
  f.ports.execFile = async (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === 'repos/example/project/issues/18'
    ? { stdout: JSON.stringify({ number: 18, html_url: 'https://github.com/example/project/issues/18', title: 'Other', body: '' }) } : execFile(file, args, opts);
  assert.equal((await startRun({ name: 'small-change', issue: '18', agent: 'claude', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  assert.deepEqual(f.herdr.workspaces.map(w => w.label), ['project', 'project#17 small-change', 'project#18 small-change']);
  await cancelRun({ ref: '17', cwd: f.source }, f.ports);
  assert.deepEqual(f.herdr.workspaces.map(w => w.label), ['project', 'project#18 small-change']);
  await cancelRun({ ref: '18', cwd: f.source }, f.ports);
  assert.deepEqual(f.herdr.workspaces, []);
  assert.equal((await f.run()).exitCode, 0, 'a run after the repository workspace closed opens a new one');
  assert.deepEqual(f.herdr.workspaces.map(w => w.label), ['project', 'project#17 small-change']);
  assert.notEqual(f.record().chats[0].repoWorkspaceId, first.chats[0].repoWorkspaceId);
});

// Seen in the 0.1.4 real run: the prompt-story summary also had a (first) Runtime check; the check step's is the result.
test('#18: the check step\'s Runtime check wins the top of PR 1; the code question already says how to make the code PR later', async t => {
  const f = await fixture(t, { name: 'feature', agent: 'codex' });
  const skill = join(f.source, '.agents', 'skills', 'pdd-feature');
  mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [
    { name: 'story', steps: ['prompt-story'], optional: [], gate: 'approve' },
    { name: 'prompt-pr', steps: ['check'], optional: [], gate: 'pr', then: 'ask-code' },
    { name: 'code', steps: ['build'], optional: [], gate: 'pr' }] }));
  await f.run(); const run = f.record();
  writeFileSync(join(run.root, 'p.prompt.md'), 'x\n'); f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'p');
  f.tick(); await stepDone({ step: 'prompt-story', summary: 'Story; Runtime check (DRAFT): ✓ 1 of 2 criteria; Report: https://rt.example.test/r/first', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  f.tick(); const gate = await stepDone({ step: 'check', summary: 'Runtime check: ✓ 2 of 2 criteria; Report: https://rt.example.test/r/second', cwd: run.root }, f.agentPorts());
  assert.match(f.prs[0].body, /^Runtime check: ✓ 2 of 2 criteria\nReport: https:\/\/rt\.example\.test\/r\/second /);
  assert.match(gate.message, /ask exactly: "Do you want the code PR now, or stop here and merge PR 1 first\? To make the code PR later, run `pdd workflow approve 17`\."/);
});

// 0.1.6 items 6 and 7: many Stories in one run.
const storyLines = 'Runtime check (move-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call; Runtime check (merge-tiles) (DRAFT): ✗ 2 of 3 criteria · 8/10 checks · 2 AI calls; '
  + 'Runtime check (score): ✓ 2 of 2 criteria · 6/6 checks · 1 AI call; Runtime check: ✗ 7 of 8 criteria · 24/26 checks · 4 AI calls; Report: https://rt.example.test/r/batch-1';
test('0.1.6: PR 1 starts with one Runtime check line per Story, then the total pdd adds up and the report; status counts the Stories that pass', async t => {
  const { f, run } = await featureAtTryGate(t);
  f.ports.timeZone = 'UTC';
  f.tick(); await stepDone({ step: 'check', summary: storyLines, cwd: run.root }, f.agentPorts());
  let shown = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.match(shown.message, /^Stories: 2 of 3 Stories pass \(✗ merge-tiles\)$/m);
  assert.match((await runStatus({ all: true, cwd: f.source }, f.ports)).message, /· 2 of 3 Stories pass ·/);
  assert.deepEqual(JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0].stories, { pass: 2, total: 3, failing: ['merge-tiles'] });
  // The chat re-checks only merge-tiles and sends all current lines again; pdd counts only the latest summary.
  f.tick(); await stepDone({ step: 'check', summary: storyLines.replace('(DRAFT): ✗ 2 of 3 criteria · 8/10 checks', '(DRAFT): ✓ 3 of 3 criteria · 10/10 checks').replace('Runtime check: ✗ 7 of 8', 'Runtime check: ✓ 8 of 8'), cwd: run.root }, f.agentPorts());
  const gate = await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  assert.match(gate.message, /Runtime check line of each Story/);
  shown = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.match(shown.message, /^Stories: 3 of 3 Stories pass$/m);
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  const top = f.prs[0].body.split('\n');
  assert.deepEqual(top.slice(0, 6), [
    'Runtime check (move-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call',
    'Runtime check (merge-tiles) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 2 AI calls',
    'Runtime check (score): ✓ 2 of 2 criteria · 6/6 checks · 1 AI call',
    'Runtime check (all Stories) (DRAFT): ✓ 8 of 8 criteria · 26/26 checks · 4 AI calls',
    'Report: https://rt.example.test/r/batch-1 (report links expire after 7 days)', '']);
});

test('0.1.6: a single overall Runtime check line counts as one Story', async t => {
  const { f, run } = await featureAtTryGate(t);
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^Stories: 1 of 1 Stories pass$/m);
  f.tick(); await stepDone({ step: 'check', summary: 'Runtime check (DRAFT): ✗ 1 of 2 criteria · 3/5 checks · 1 AI call', cwd: run.root }, f.agentPorts());
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^Stories: 0 of 1 Stories pass$/m);
});

test('0.1.6: the skills format (one line each, with a Report line per Story) gives the same PR 1 top and count', async t => {
  const { f, run } = await featureAtTryGate(t);
  const summary = ['Runtime check (move-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call', 'Checked each Story.', 'Report: https://rt.example.test/r/one',
    'Runtime check (merge-tiles) (DRAFT): ✗ 2 of 3 criteria · 8/10 checks · 2 AI calls', 'Report (DRAFT): https://rt.example.test/r/two',
    'Runtime check: ✗ 5 of 6 criteria · 18/20 checks · 3 AI calls', 'Report: https://rt.example.test/r/one'].join('\n');
  f.tick(); await stepDone({ step: 'check', summary, cwd: run.root }, f.agentPorts());
  // The stored summary keeps the newlines; status still shows each step on one line.
  assert.equal(f.record().done.check.summary, summary);
  const shown = (await runStatus({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.match(shown, /^Stories: 1 of 2 Stories pass \(✗ merge-tiles\)$/m);
  assert.match(shown, /check done \("Runtime check \(move-tiles\): ✓ 3 of 3 criteria · 10\/10 checks · 1 AI call Checked each Story\. Report: https:/);
  await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  assert.deepEqual(f.prs[0].body.split('\n').slice(0, 6), [
    'Runtime check (move-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call',
    'Runtime check (merge-tiles) (DRAFT): ✗ 2 of 3 criteria · 8/10 checks · 2 AI calls',
    'Runtime check (all Stories) (DRAFT): ✗ 5 of 6 criteria · 18/20 checks · 3 AI calls',
    'Report: https://rt.example.test/r/one (report links expire after 7 days)',
    'Report: https://rt.example.test/r/two (report links expire after 7 days)', '']);
});

test('0.1.6: the agreed format ("; ", one "Report (<story>): <url>" per report row) keeps the Story name on each PR 1 report line', async t => {
  const { f, run } = await featureAtTryGate(t);
  const summary = 'Runtime check (move-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call; Runtime check (merge-tiles) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 2 AI calls; '
    + 'Runtime check (DRAFT): ✓ 6 of 6 criteria · 20/20 checks · 3 AI calls; Report (move-tiles): https://rt.example.test/r/one; '
    + 'Report (merge-tiles): https://rt.example.test/r/two; Report (merge-tiles): https://rt.example.test/r/three';
  f.tick(); await stepDone({ step: 'check', summary, cwd: run.root }, f.agentPorts());
  await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^Stories: 2 of 2 Stories pass$/m);
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  assert.deepEqual(f.prs[0].body.split('\n').slice(0, 7), [
    'Runtime check (move-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call',
    'Runtime check (merge-tiles) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 2 AI calls',
    'Runtime check (all Stories) (DRAFT): ✓ 6 of 6 criteria · 20/20 checks · 3 AI calls',
    'Report (move-tiles): https://rt.example.test/r/one (report links expire after 7 days)',
    'Report (merge-tiles): https://rt.example.test/r/two (report links expire after 7 days)',
    'Report (merge-tiles): https://rt.example.test/r/three (report links expire after 7 days)', '']);
});

test('0.1.6 real run (pdd-trial-2048-1027): the pasted overall line repeated one Story; pdd drops it and adds up all Stories itself', async t => {
  const { f, run } = await featureAtTryGate(t);
  // The check summary as the chat stored it in the real run (the last line copied swipe-play's run); only the runtime host is a stand-in.
  const summary = 'Runtime check (swipe-play) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 8 AI calls Report: https://rt.example.test/r/7a5cc123-32d4-434b-bc1e-43edcb1f643d '
    + 'Runtime check (game-result) (DRAFT): ✓ 3 of 3 criteria · 13/13 checks · 5 AI calls Report: https://rt.example.test/r/ddab0595-645e-47e5-9bff-74c47614d9a1 '
    + 'Runtime check (new-game) (DRAFT): ✓ 2 of 2 criteria · 12/12 checks · 4 AI calls Report: https://rt.example.test/r/5a866c47-e4d3-4746-9036-9fe86c9b8937 '
    + 'Runtime check (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 8 AI calls Report: https://rt.example.test/r/7a5cc123-32d4-434b-bc1e-43edcb1f643d';
  f.tick(); await stepDone({ step: 'check', summary, cwd: run.root }, f.agentPorts());
  await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^Stories: 3 of 3 Stories pass$/m);
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  assert.deepEqual(f.prs[0].body.split('\n').slice(0, 8), [
    'Runtime check (swipe-play) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 8 AI calls',
    'Runtime check (game-result) (DRAFT): ✓ 3 of 3 criteria · 13/13 checks · 5 AI calls',
    'Runtime check (new-game) (DRAFT): ✓ 2 of 2 criteria · 12/12 checks · 4 AI calls',
    'Runtime check (all Stories) (DRAFT): ✓ 8 of 8 criteria · 35/35 checks · 17 AI calls',
    'Report: https://rt.example.test/r/7a5cc123-32d4-434b-bc1e-43edcb1f643d (report links expire after 7 days)',
    'Report: https://rt.example.test/r/ddab0595-645e-47e5-9bff-74c47614d9a1 (report links expire after 7 days)',
    'Report: https://rt.example.test/r/5a866c47-e4d3-4746-9036-9fe86c9b8937 (report links expire after 7 days)', '']);
});

test('0.1.6: a summary with no overall line works; a Story checked again takes its latest line', async t => {
  const { f, run } = await featureAtTryGate(t);
  // skills 2f52fa3: only the Stories' current lines, then one report per report row.
  const summary = 'Runtime check (move-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call; Runtime check (merge-tiles): ✗ 2 of 3 criteria · 8/10 checks · 2 AI calls; '
    + 'Report (move-tiles): https://rt.example.test/r/one; Report (merge-tiles): https://rt.example.test/r/two';
  f.tick(); await stepDone({ step: 'check', summary, cwd: run.root }, f.agentPorts());
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^Stories: 1 of 2 Stories pass \(✗ merge-tiles\)$/m);
  // A chat that adds the re-check after the old lines: the later merge-tiles line wins and keeps its place.
  f.tick(); await stepDone({ step: 'check', summary: `${summary}; Runtime check (merge-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call; Report (merge-tiles): https://rt.example.test/r/three`, cwd: run.root }, f.agentPorts());
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^Stories: 2 of 2 Stories pass$/m);
  await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  assert.deepEqual(f.prs[0].body.split('\n').slice(0, 7), [
    'Runtime check (move-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call',
    'Runtime check (merge-tiles): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call',
    'Runtime check (all Stories): ✓ 6 of 6 criteria · 20/20 checks · 2 AI calls',
    'Report (move-tiles): https://rt.example.test/r/one (report links expire after 7 days)',
    'Report (merge-tiles): https://rt.example.test/r/two (report links expire after 7 days)',
    'Report (merge-tiles): https://rt.example.test/r/three (report links expire after 7 days)', '']);
});

// pdd check prints only the Story's own line when there is one Story (0.1.7): PR 1 lifts it and status counts it.
test('0.1.7: a summary with only one named Runtime check line lifts that line into PR 1', async t => {
  const { f, run } = await featureAtTryGate(t);
  f.tick(); await stepDone({ step: 'check', summary: 'Runtime check (unread-filter) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call; Report (unread-filter): https://rt.example.test/r/one', cwd: run.root }, f.agentPorts());
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^Stories: 1 of 1 Stories pass$/m);
  await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  assert.deepEqual(f.prs[0].body.split('\n').slice(0, 3), [
    'Runtime check (unread-filter) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call',
    'Report (unread-filter): https://rt.example.test/r/one (report links expire after 7 days)', '']);
});

test('0.1.6: one named Story gets no total line; its line is the total', async t => {
  const { f, run } = await featureAtTryGate(t);
  f.tick(); await stepDone({ step: 'check', summary: 'Runtime check (move-tiles) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call; Runtime check (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call; Report (move-tiles): https://rt.example.test/r/one', cwd: run.root }, f.agentPorts());
  await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  assert.deepEqual(f.prs[0].body.split('\n').slice(0, 3), [
    'Runtime check (move-tiles) (DRAFT): ✓ 3 of 3 criteria · 10/10 checks · 1 AI call',
    'Report (move-tiles): https://rt.example.test/r/one (report links expire after 7 days)', '']);
});

// ---- 0.1.7: a real tester run of 0.1.6 (round 2, "web", bookshelf, Oct 27) ----

// Tester B2: "env -u CLAUDE_CONFIG_DIR CODEX_HOME=~/.pdd-codex/work4 pdd workflow run feature 3". zsh does not expand "~"
// in an env argument, pdd saved the text, and Codex stopped at once ("CODEX_HOME points to … but that path does not exist").
test('0.1.7 #1: run expands a leading ~ in CODEX_HOME and CLAUDE_CONFIG_DIR and refuses a folder that does not exist before it starts anything', async t => {
  const f = await fixture(t, { agent: 'codex' });
  const home = f.ports.env.HOME, folder = join(home, '.pdd-codex', 'work4');
  f.ports.env = { HOME: home, CODEX_HOME: '~/.pdd-codex/work4' };
  const refused = await f.run();
  assert.equal(refused.exitCode, 1);
  assert.equal(refused.message, `CODEX_HOME is "${folder}", but that folder does not exist. Fix CODEX_HOME and run the command again.`);
  assert.deepEqual(f.herdr.calls, []); assert.equal(f.fetches, 0);
  assert.equal(f.git(f.source, 'worktree', 'list').split('\n').length, 1, 'no worktree');
  mkdirSync(folder, { recursive: true });
  const started = await f.run();
  assert.equal(started.exitCode, 0, started.message);
  const run = f.record();
  assert.equal(run.configDir, folder); assert.equal(run.chats[0].configDir, folder);
  assert.ok(f.herdr.paneOf(run.chats[0]).commands[0].startsWith(`env PDD_AGENT_SESSION=1 CODEX_HOME='${folder}' codex `), f.herdr.paneOf(run.chats[0]).commands[0]);

  const claude = await fixture(t), claudeHome = claude.ports.env.HOME;
  claude.ports.env = { HOME: claudeHome, CLAUDE_CONFIG_DIR: '~/missing' };
  assert.equal((await claude.run()).message, `CLAUDE_CONFIG_DIR is "${join(claudeHome, 'missing')}", but that folder does not exist. Fix CLAUDE_CONFIG_DIR and run the command again.`);
  claude.ports.env = { HOME: claudeHome, CLAUDE_CONFIG_DIR: '~' };
  assert.equal((await claude.run()).exitCode, 0);
  assert.equal(claude.record().configDir, claudeHome);
});

test('0.1.7 #1: a saved "~" config folder is expanded when pdd resumes or starts a chat; a missing one stops approve and open before they change anything', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(), dir = f.ports.env.CLAUDE_CONFIG_DIR, pane = f.herdr.paneOf(run.chats[0]);
  // A run record that an older pdd wrote with the "~" text.
  const record = JSON.parse(readFileSync(join(run.runDir, 'status.json'), 'utf8'));
  record.configDir = '~/.claude'; record.chats[0].configDir = '~/.claude'; writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(record));
  pane.agent = null;
  const inside = { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' } };
  assert.equal((await openRun({ ref: '17', cwd: f.source }, inside)).exitCode, 0);
  assert.ok(pane.commands[1].startsWith(`env PDD_AGENT_SESSION=1 CLAUDE_CONFIG_DIR='${dir}' claude `), pane.commands[1]);
  f.tick(); await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  rmSync(dir, { recursive: true });
  const missing = `This run uses CLAUDE_CONFIG_DIR "${dir}", but that folder does not exist. Make that folder, or cancel the run (pdd workflow cancel 17) and start it again with the right CLAUDE_CONFIG_DIR.`;
  f.tick();
  const refused = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(refused.exitCode, 1); assert.equal(refused.message, missing);
  assert.equal(f.prompts.length, 0); assert.equal(f.record().area, 0); assert.equal(f.record().decisions.length, 0);
  pane.agent = null;
  const notOpened = await openRun({ ref: '17', cwd: f.source }, inside);
  assert.equal(notOpened.exitCode, 1); assert.equal(notOpened.message, missing); assert.equal(pane.commands.length, 2);
  mkdirSync(dir);
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  assert.ok(f.herdr.paneOf(f.record().chats[1]).commands[0].startsWith(`env PDD_AGENT_SESSION=1 CLAUDE_CONFIG_DIR='${dir}' claude `));
});

// Tester B2–B4: the chat died at its start, and for 10 minutes status said "State: the agent works on understand".
test('0.1.7 #2: status says the chat stopped when no agent runs in its pane, and keeps its words when Herdr cannot tell', async t => {
  const f = await fixture(t);
  f.ports.timeZone = 'UTC';
  await f.run(); const run = f.record(), pane = f.herdr.paneOf(run.chats[0]);
  pane.agent = null; // The agent ended; the tab holds a plain shell.
  // Herdr sees a new chat's agent only after it starts, so a chat that just started still "works".
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^State: the agent works on scope$/m);
  f.tick(60000);
  const shown = await runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(shown.exitCode, 0);
  assert.match(shown.message, /^State: the chat stopped\. Run pdd workflow open 17 to start it again\.$/m);
  assert.match((await runStatus({ all: true, cwd: f.source }, f.ports)).message, /^example\/project#17 · small-change · plan · the chat stopped: run pdd workflow open 17 · /);
  const json = JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0];
  assert.deepEqual([json.group, json.words], ['waiting', 'the chat stopped: run pdd workflow open 17']);
  // The pdd Herdr server is down: no chat of it runs.
  const down = { ...f.ports, herdr: async args => { if (args[0] === 'agent') throw Object.assign(Error('no server'), { code: 'server_not_running' }); return f.herdr.herdr(args); } };
  assert.match((await runStatus({ ref: '17', cwd: f.source }, down)).message, /^State: the chat stopped\./m);
  // Any other Herdr failure: pdd cannot tell, so status keeps its words and still works.
  const broken = { ...f.ports, herdr: async args => { if (args[0] === 'agent') throw Object.assign(Error('odd'), { code: 'herdr_failed' }); return f.herdr.herdr(args); } };
  const unsure = await runStatus({ ref: '17', cwd: f.source }, broken);
  assert.equal(unsure.exitCode, 0); assert.match(unsure.message, /^State: the agent works on scope$/m);
  // pdd workflow open starts the chat again, and status says it works.
  assert.equal((await openRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' } })).exitCode, 0);
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^State: the agent works on scope$/m);
});

// Tester B10: "pdd workflow changes 3 "I approve. The Story and the prompt look good now."" went to the chat as a change
// request, and the chat could not approve with it.
test('0.1.7 #3: changes at a gate refuses a plain approval and says how to approve; real change requests and answers still go through', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(), pane = f.herdr.paneOf(run.chats[0]); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  const gateAt = f.record().gate.at;
  for (const text of ['I approve. The Story and the prompt look good now.', 'approve', 'Approved!', 'LGTM', 'looks good, approve', 'Yes approve', 'yes, I approve it']) {
    f.tick();
    const out = await changeRun({ ref: '17', text, cwd: f.source }, f.ports);
    assert.equal(out.exitCode, 2, text);
    assert.equal(out.message, 'This looks like an approval. To approve, run: pdd workflow approve 17\nNothing was sent to the chat.');
  }
  assert.equal(pane.agent.prompts.length, 0); assert.deepEqual(f.record().changes, []); assert.equal(f.record().gate.at, gateAt);
  for (const text of ['approve it but rename X to Y', 'I approve, but please use the exact text', 'Please use the exact text from the issue', 'looks good', "I don't approve", 'Approve after you add a test']) {
    f.tick();
    const out = await changeRun({ ref: '17', text, cwd: f.source }, f.ports);
    assert.equal(out.exitCode, 0, `${text}: ${out.message}`);
    assert.equal(pane.agent.prompts.at(-1).startsWith(`The person asks for changes: ${text}`), true, pane.agent.prompts.at(-1));
  }
  // The answer to the chat's question goes to the chat as it is, even when it says approve.
  await askPerson({ text: 'Shall I skip the Try step?', cwd: run.root }, f.agentPorts());
  f.tick();
  const answer = await changeRun({ ref: '17', text: 'Yes, approve', cwd: f.source }, f.ports);
  assert.equal(answer.exitCode, 0, answer.message); assert.match(pane.agent.prompts.at(-1), /^The person answers your question: Yes, approve/);
});

// Tester B9: "pdd workflow approve 3" in a terminal inside Claude Code (CLAUDECODE=1) got the text meant for the chat agent.
test('0.1.7 #4: approve in an agent environment tells the person how to approve; the chat-evidence rule does not change', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  const noReply = async () => ({ ok: false, code: 'user_message_missing', message: 'No user message was found after the gate question in this native session.' });
  const person = (env, extra = {}) => ({ ...f.ports, env: { HOME: f.ports.env.HOME, ...env }, readApprovalEvidence: noReply, ...extra });
  const claudeCode = await approveRun({ ref: '17', cwd: f.source }, person({ CLAUDECODE: '1' }));
  assert.equal(claudeCode.exitCode, 1);
  assert.equal(claudeCode.message, ['pdd sees an agent environment (CLAUDECODE=1), so it cannot ask you y/N here.',
    'No approval was found in the plan chat: there is no reply from you after the gate question.',
    'To approve, run pdd workflow approve 17 in a normal terminal. Or answer the gate question in the plan chat: pdd workflow open 17'].join('\n'));
  const piped = await approveRun({ ref: '17', cwd: f.source }, person({}, { isTTY: false }));
  assert.equal(piped.exitCode, 1); assert.match(piped.message, /^pdd sees an agent environment \(stdin is not a terminal\), so it cannot ask you y\/N here\./);
  assert.equal(f.prompts.length, 0, 'still no y/N question'); assert.equal(f.record().area, 0);
  // The chat agent itself keeps the words meant for it.
  assert.match((await approveRun({ ref: '17', cwd: run.root }, f.agentPorts({ readApprovalEvidence: noReply }))).message, /^Only the person can approve/);
  // A reply from the person in the chat still approves, also from that terminal.
  const replied = await approveRun({ ref: '17', cwd: f.source }, person({ CLAUDECODE: '1' }, { readApprovalEvidence: async () => ({ ok: true, decision: 'approve', agent: 'claude', sessionId: run.chats[0].session.id, userMessage: 'I approve', userMessageAt: f.clock - 1 }) }));
  assert.equal(replied.exitCode, 0, replied.message); assert.equal(f.record().area, 1);
});

// Tester B6: status said "waiting for you: approve the story area" about a minute before the chat wrote its gate message.
test('0.1.7 #6: at a gate, status says the agent writes the gate message until the chat ends its turn, then waits for the person', async t => {
  const f = await fixture(t);
  f.ports.timeZone = 'UTC';
  await f.run(); const run = f.record(), pane = f.herdr.paneOf(run.chats[0]); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  // done returned; Herdr still shows the chat working on its message.
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^State: the agent writes the gate message for the plan area$/m);
  assert.match((await runStatus({ all: true, cwd: f.source }, f.ports)).message, /^example\/project#17 · small-change · plan · agent writing the gate message · /);
  assert.equal(JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0].group, 'working');
  pane.agent.agent_status = 'idle';
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^State: waiting for you: approve the plan area or ask for changes$/m);
  // After a change request the chat works on the changes, and then asks again.
  f.tick(); await changeRun({ ref: '17', text: 'Use blue.', cwd: f.source }, f.ports); pane.agent.agent_status = 'working';
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^State: the agent works on your changes to the plan area$/m);
  pane.agent.agent_status = 'done';
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^State: waiting for you: approve the plan area or ask for changes$/m);
});

// Tester B15 and the other tester's run: "Make the code PR now? (y/N)" while PR 1's prompt was still draft; a "y" was refused.
test('0.1.7 #7: with a draft prompt in PR 1, pdd does not offer the code PR; it says how to approve the prompt, and approve then carries the approval to PR 1', async t => {
  const { f, run } = await featureAtTryGate(t, { prompt: runtimePrompt('draft') });
  const pane = f.herdr.paneOf(f.record().chats[1]);
  f.tick();
  const opened = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(opened.exitCode, 0, opened.message);
  assert.match(f.prompts.at(-1), /Approve the prompt-pr area and open PR 1/, 'no code PR question');
  const first = `Approve the prompt first: cd ${run.root} && pdd approve feature.prompt.md. Then run pdd workflow approve 17 to start the code PR.`;
  assert.ok(opened.message.includes(`PR 1: https://github.com/example/project/pull/23\n${first}`), opened.message);
  assert.ok(pane.agent.prompts.at(-1).includes(`Tell them exactly: "PR 1 is open: https://github.com/example/project/pull/23. ${first}"`), pane.agent.prompts.at(-1));
  assert.equal(f.record().gate.kind, 'ask-code'); assert.equal(f.record().area, 1);
  f.herdr.idle();
  const shown = (await runStatus({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.match(shown, /^State: PR 1 open \(https:\/\/github\.com\/example\/project\/pull\/23\); waiting for you: approve the draft prompt first, then make the code PR\.$/m);
  assert.ok(shown.includes(`\nNext: cd ${run.root} && pdd approve feature.prompt.md, then pdd workflow approve 17 (make the code PR)`), shown);
  assert.match((await runStatus({ all: true, cwd: f.source }, f.ports)).message, /· prompt-pr · waiting for you: approve the draft prompt, then the code PR \(PR 1 open\) · /);
  // The person approves the prompt in the worktree; pdd approve writes the file and commits nothing.
  writeFileSync(join(run.root, 'feature.prompt.md'), runtimePrompt('approved'));
  f.tick();
  const code = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(code.exitCode, 0, code.message);
  assert.match(code.message, /pdd committed your approval of feature\.prompt\.md and pushed it to PR 1\./);
  assert.equal(f.git(run.root, 'log', '-1', '--format=%s', run.branch), 'Approve feature.prompt.md');
  assert.match(code.message, /pdd updated the PR 1 description: no draft prompts are left\./);
  assert.doesNotMatch(f.prs[0].body, /Draft prompts/); assert.match(f.prs[0].body, /<!-- pdd-workflow:/, 'the PR marker stays');
  assert.match(f.prompts.at(-1), /Make the code PR now/);
  assert.equal(f.git(run.root, 'show', `${run.branch}:feature.prompt.md`), runtimePrompt('approved').trim());
  assert.equal(f.git(run.root, 'rev-parse', `refs/remotes/origin/${run.branch}`), f.git(run.root, 'rev-parse', run.branch), 'PR 1 has the approval');
  assert.equal(f.record().areas[f.record().area].name, 'code'); assert.equal(f.record().branch, `${run.branch}-code`);
});

test('0.1.7 #7: when done opens PR 1 with a draft prompt, the chat tells the person to approve the prompt and does not ask about the code PR', async t => {
  const { f, run, pr1 } = await featureToPr1(t, runtimePrompt('draft'));
  assert.doesNotMatch(pr1.message, /Do you want the code PR now/);
  assert.ok(pr1.message.includes(`Do not offer the code PR yet. Tell the person exactly: "PR 1 is open: https://github.com/example/project/pull/23. Approve the prompt first: cd ${run.root} && pdd approve feature.prompt.md. Then run pdd workflow approve 17 to start the code PR." Stop there.`), pr1.message);
  f.tick();
  const refused = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(refused.exitCode, 1);
  assert.equal(refused.message, `Approve the prompt first: cd ${run.root} && pdd approve feature.prompt.md. Then run pdd workflow approve 17 to start the code PR.`);
});

// Tester B14, B16: PR 1 of a page-only Story had no test file, but its title said "tests"; the chat called the draft prompt
// "approved"; status said "try it" when there was nothing to try.
test('0.1.7 #8: without a test file PR 1 is "(prompt and Story)", the gate words name the approved Story and the draft prompt, and nothing to try drops "try it"', async t => {
  const { f, gate } = await featureAtTryGate(t, { prompt: runtimePrompt('draft'), tried: 'skipped' });
  f.ports.timeZone = 'UTC';
  assert.match(gate.message, /Tell the person what PR 1 holds, in these words: "PR 1 is ready with the approved Story and the draft prompt feature\.prompt\.md\. It has no test file\."/);
  assert.match(gate.message, /There is nothing to try\. Ask them to approve or ask for changes\./); assert.doesNotMatch(gate.message, /try it/);
  f.herdr.idle();
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^State: waiting for you: approve to open PR 1 \(or ask for changes\)$/m);
  assert.match((await runStatus({ all: true, cwd: f.source }, f.ports)).message, /· prompt-pr · waiting for you: approve to open PR 1 · /);
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  assert.equal(f.prs[0].title, 'Use value two (prompt and Story)');
  assert.match(f.prs[0].body, /^PR 1 of this run: the prompt and the Story\. The code comes in PR 2 only when the person asks for it\.$/m);
});

test('0.1.7 #8: with a test file and a Try link, PR 1 keeps "(prompt, Story and tests)" and the gate says to try it', async t => {
  const { f, gate } = await featureAtTryGate(t, { tests: true });
  assert.match(gate.message, /in these words: "PR 1 is ready with the approved Story, the prompt feature\.prompt\.md and the tests\."/);
  assert.match(gate.message, /Ask them to try it, then approve or ask for changes\./);
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  assert.equal(f.prs[0].title, 'Use value two (prompt, Story and tests)');
  assert.match(f.prs[0].body, /^PR 1 of this run: the prompt, Story and test cases\./m);
});

// ---- 0.1.7: the round-2 "cli" tester (tipjar, bug workflow, Oct 27) ----

// Tester 4.18–4.20: "pdd approve" (y), then "pdd workflow approve 2" was refused again until a guessed "git commit". That
// commit then went to PR 2, and PR 1 still said "Draft prompts".
test('0.1.7 #9: a prompt approval committed by hand is pushed to PR 1 before the code area starts, and PR 1 drops its "Draft prompts" line', async t => {
  const { f, run } = await featureToPr1(t, runtimePrompt('draft'));
  assert.match(f.prs[0].body, /Draft prompts: feature\.prompt\.md\./);
  writeFileSync(join(run.root, 'feature.prompt.md'), runtimePrompt('approved')); f.git(run.root, 'commit', '-qam', 'Approve prompts/tipjar.prompt.md');
  const approval = f.git(run.root, 'rev-parse', 'HEAD');
  const capture = join(f.base, 'gh-body.txt'), gh = join(f.base, 'gh'), gitShim = join(f.base, 'git'), bodyFile = join(f.base, 'gh-pr-body.txt');
  writeFileSync(bodyFile, f.prs[0].body);
  const realGit = execFileSync('sh', ['-c', 'command -v git'], { encoding: 'utf8' }).trim();
  writeFileSync(gitShim, '#!/bin/sh\nif [ "$1" = fetch ]; then exit 0; fi\nif [ "$1" = push ]; then sha=$("' + realGit + '" rev-parse HEAD) || exit 1; ref=${3#*:}; local_ref=refs/remotes/origin/${ref#refs/heads/}; "' + realGit + '" update-ref "$local_ref" "$sha"; exit 0; fi\nexec "' + realGit + '" "$@"\n'); chmodSync(gitShim, 0o755);
  const ghScript = `#!/bin/sh
if [ "$1" = pr ] && [ "$2" = edit ]; then cat > "$GH_CAPTURE"; cp "$GH_CAPTURE" "$GH_PR_BODY_FILE"; exit 0; fi
if [ "$1" = pr ] && [ "$2" = view ]; then
  if [ "$4" = --json ] && [ "$5" = body ]; then
    node -e 'const fs=require("fs"); process.stdout.write(JSON.stringify({body:fs.readFileSync(process.env.GH_PR_BODY_FILE,"utf8")}));'
  else
    echo '{"state":"OPEN"}'
  fi
  exit 0
fi
exit 0
`;
  writeFileSync(gh, ghScript); chmodSync(gh, 0o755);
  const oldPath = process.env.PATH, oldCap=process.env.GH_CAPTURE, oldBody=process.env.GH_PR_BODY_FILE; process.env.PATH = `${f.base}:${oldPath}`; process.env.GH_CAPTURE=capture; process.env.GH_PR_BODY_FILE=bodyFile;
  f.tick();
  const testPorts = { ...f.ports }; delete testPorts.execFile;
  const code = await approveRun({ ref: '17', cwd: f.source }, testPorts);
  process.env.PATH = oldPath; if(oldCap===undefined) delete process.env.GH_CAPTURE; else process.env.GH_CAPTURE=oldCap; if(oldBody===undefined) delete process.env.GH_PR_BODY_FILE; else process.env.GH_PR_BODY_FILE=oldBody;
  f.prs[0].body = readFileSync(capture, 'utf8'); assert.equal(readFileSync(capture, 'utf8'), f.prs[0].body);
  assert.equal(code.exitCode, 0, code.message);
  assert.match(code.message, /pdd pushed 1 new commit from the worktree to PR 1\./); assert.match(code.message, /pdd updated the PR 1 description: no draft prompts are left\./);
  assert.equal(f.git(run.root, 'rev-parse', `refs/remotes/origin/${run.branch}`), approval, 'the approval is on PR 1');
  assert.doesNotMatch(f.prs[0].body, /Draft prompts/); assert.match(f.prs[0].body, /^Part of #17$/m);
  assert.equal(f.record().areas[f.record().area].name, 'code'); assert.equal(f.record().prBase, run.branch, 'PR 2 stacks on PR 1, which has the approval');
});

test('0.1.7 #9: when pdd cannot push the approval to PR 1, it changes nothing else and says the exact next commands', async t => {
  const { f, run } = await featureToPr1(t, runtimePrompt('draft'));
  writeFileSync(join(run.root, 'feature.prompt.md'), runtimePrompt('approved'));
  const execFile = f.ports.execFile;
  f.ports.execFile = async (file, args, opts) => file === 'git' && args[0] === 'push' ? Promise.reject(Object.assign(Error('rejected'), { code: 1 })) : execFile(file, args, opts);
  f.tick();
  const refused = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(refused.exitCode, 1);
  assert.equal(refused.message, `pdd could not push your approval of feature.prompt.md to PR 1. Run: cd ${run.root} && git push origin HEAD:refs/heads/${run.branch}\nThen run pdd workflow approve 17 again.`);
  assert.equal(f.record().area, 1); assert.equal(f.record().gate.kind, 'ask-code'); assert.equal(f.git(run.root, 'branch', '--show-current'), run.branch);
  assert.equal(f.prompts.length, 1, 'no code question');
  f.ports.execFile = execFile; f.tick();
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0, 'the next approve pushes and goes on');
  assert.doesNotMatch(f.prs[0].body, /Draft prompts/);
});

// Tester 4.8 (round 1 R1-5): a person's terminal tab in Herdr must be able to approve; the chat's own pane must not.
test('0.1.7 #10: a person terminal in a Herdr tab approves with y/N; the run chat pane in the pdd session and agent environments do not', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  const noReply = async () => ({ ok: false, code: 'user_message_missing', message: 'No user message was found after the gate question in this native session.' });
  const herdrTab = (pane, socket, extra = {}) => ({ ...f.ports, readApprovalEvidence: noReply,
    env: { HOME: f.ports.env.HOME, HERDR_ENV: '1', HERDR_PANE_ID: pane, HERDR_TAB_ID: 'w1:t9', HERDR_SOCKET_PATH: socket, ...extra } });
  const pddSocket = join(f.ports.env.HOME, '.config/herdr/sessions/pdd/herdr.sock'), defaultSocket = join(f.ports.env.HOME, '.config/herdr/herdr.sock');
  const chatPane = herdrTab(run.chats[0].paneId, pddSocket);
  const refused = await approveRun({ ref: '17', cwd: f.source }, chatPane);
  assert.equal(refused.exitCode, 1); assert.equal(f.prompts.length, 0);
  assert.match(refused.message, new RegExp(`^pdd sees the plan chat's own Herdr pane \\(${run.chats[0].paneId}\\), so it cannot ask you y/N here\\.\\n`));
  assert.match(refused.message, /To approve, run pdd workflow approve 17 in another terminal tab\. Or answer the gate question in the plan chat: pdd workflow open 17$/);
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, herdrTab(run.chats[0].paneId, pddSocket, { CODEX_THREAD_ID: 't' }))).exitCode, 1);
  assert.equal(f.prompts.length, 0, 'an agent environment in a Herdr tab gets no y/N');
  // The same pane id in the person's default Herdr session is another pane.
  f.tick();
  const tab = await approveRun({ ref: '17', cwd: f.source }, herdrTab(run.chats[0].paneId, defaultSocket));
  assert.equal(tab.exitCode, 0, tab.message); assert.equal(f.prompts.length, 1); assert.equal(f.record().decisions.at(-1).via, 'terminal');
});

// Tester 4.15: 10 minutes after PR 1 opened, status still showed the answered question "Do you approve this revision so
// PDD can open PR 1?".
test('0.1.7 #11: an approval clears the question that the chat asked at the gate, and status ignores a question older than the gate', async t => {
  const { f, run } = await featureAtTryGate(t);
  f.herdr.idle();
  await askPerson({ text: 'Try is skipped. Do you approve this revision so PDD can open PR 1?', cwd: run.root }, f.agentPorts());
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /^State: waiting for you: Try is skipped\. Do you approve/m);
  f.tick();
  const opened = await approveRun({ ref: '17', cwd: run.root }, f.agentPorts({ readApprovalEvidence: async () => ({ ok: true, decision: 'approve', agent: 'codex', sessionId: '11111111-1111-4111-8111-111111111111', userMessage: 'I approve, open PR 1.', userMessageAt: f.clock - 1 }) }));
  assert.equal(opened.exitCode, 0, opened.message);
  assert.equal(f.record().question, null);
  f.herdr.idle();
  let shown = (await runStatus({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.match(shown, /^State: PR 1 open \(https:\/\/github\.com\/example\/project\/pull\/23\); waiting for you: code PR now, or stop and merge PR 1\./m);
  assert.doesNotMatch(shown, /Do you approve this revision/);
  // A record from an older pdd kept the answered question.
  const record = JSON.parse(readFileSync(join(run.runDir, 'status.json'), 'utf8'));
  record.question = { text: 'Old question?', at: record.gate.at - 5, area: 'prompt-pr' }; writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(record));
  shown = (await runStatus({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.match(shown, /^State: PR 1 open/m); assert.doesNotMatch(shown, /Old question/);
  assert.doesNotMatch((await runStatus({ all: true, cwd: f.source }, f.ports)).message, /Old question/);
});

// Tester, small things: "step summaries are cut in the middle of a URL ("report https://ru")".
test('0.1.7 #12: status and PR step lines never cut a summary inside a URL', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  const url = 'https://runtime.example.test/r/da176d28-b1a3-4556-9e86-0654dc964ebe';
  await stepDone({ step: 'scope', summary: `${'word '.repeat(22)}report ${url} and some more words after it`, cwd: run.root }, f.agentPorts());
  const shown = (await runStatus({ ref: '17', cwd: f.source }, f.ports)).message;
  assert.ok(shown.includes(`report ${url} …")`), shown);
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'two');
  await stepDone({ step: 'change', summary: `${'word '.repeat(37)}see ${url} for the report`, cwd: run.root }, f.agentPorts());
  writeFileSync(join(run.runDir, 'verify.md'), 'ok\n');
  await lastSteps(f, run, await stepDone({ step: 'verify', summary: 'ok', cwd: run.root }, f.agentPorts()));
  const line = f.prs[0].body.split('\n').find(row => row.startsWith('- **change**'));
  assert.ok(line.endsWith(`see ${url} …`), line);
});

// Tester 4.13: the chat told the person "PDD rejected recording your earlier "Go on" because it requires a reply after
// the PR gate opens."
test('0.1.7 #13: a refused chat approval gives the agent plain words for the person, not pdd internals', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  const refused = await approveRun({ ref: '17', cwd: run.root }, f.agentPorts({ readApprovalEvidence: async () => ({ ok: false, code: 'user_message_missing', message: 'No user message was found after the gate question in this native session.' }) }));
  assert.equal(refused.exitCode, 1);
  assert.equal(refused.message, ['Only the person can approve, with a reply after your gate question. pdd found none: there is no reply from the person after the gate question.',
    'Do not explain this check to the person. Tell them plainly: "I still need your approval for this step. Reply "I approve" here, or run pdd workflow approve 17 in your terminal." Then stop and wait.'].join('\n'));
  assert.doesNotMatch(refused.message, /native session/);
  const unreadable = await approveRun({ ref: '17', cwd: run.root }, f.agentPorts({ readApprovalEvidence: async () => ({ ok: false, code: 'session_unreadable', message: 'Cannot verify chat approval because native session evidence could not be read.' }) }));
  assert.match(unreadable.message, /^Only the person can approve, with a reply after your gate question\. pdd found none: pdd could not read this chat\.\n/);
});

// Tester 4.22: the PR 2 body pasted verify.md as written: 100 lines of shell before the vector table and the Formal check.
const oldVerify = ['# Verify', '', 'Build commit: `d2eb2db`.', '', '## Commands and captured output', '', 'The commands:', '', '```sh',
  ...Array.from({ length: 40 }, (_, i) => `echo step ${i}`), '```', '', 'Fixed-code output:', '', '```text', ...Array.from({ length: 30 }, (_, i) => `ok ${i}`), '```', '',
  'The old-code failures:', '', '| Case | Old code got |', '|---|---|', '| `split-100` | `$33.33` |', '',
  '## Vector results', '', '| Case | Expected | Fixed code got | Result |', '|---|---|---|---|', '| `split-100` | `$33.34` | `$33.34` | Pass |', '',
  '## Coverage limits', '', 'No vector uses error checks.', '', '## Formal check', '', '**Proved (bounded)**: 1,208,412 inputs.', '', '```text', '# FORMAL checked=1208412', '# pass 1', '```', ''].join('\n');
test('0.1.7 #14: PR 2 puts the vector results and the Formal check first and folds long command output into closed <details> blocks', async t => {
  const f = await fixture(t, { name: 'bug', agent: 'codex' });
  const skill = join(f.source, '.agents', 'skills', 'pdd-bug');
  mkdirSync(skill, { recursive: true });
  writeFileSync(join(skill, 'workflow.json'), JSON.stringify({ version: 2, areas: [
    { name: 'story', steps: ['reproduce'], optional: [], gate: 'approve' },
    { name: 'prompt-pr', steps: ['check'], optional: [], gate: 'pr', then: 'ask-code' },
    { name: 'code', steps: ['build', 'verify'], optional: [], gate: 'pr' }] }));
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), done = async (step, summary) => { f.tick(); const out = await stepDone({ step, summary, cwd: run.root }, f.agentPorts()); assert.equal(out.exitCode, 0, out.message); return out; };
  writeFileSync(join(run.root, 'story.md'), 'Story\n'); f.git(run.root, 'add', '.'); f.git(run.root, 'commit', '-qm', 'story');
  await done('reproduce', 'seen'); f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  await done('check', 'Runtime check: ✓ 1 of 1'); f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'fix');
  await done('build', 'fixed');
  writeFileSync(join(run.runDir, 'verify.md'), oldVerify);
  await done('verify', '✓ 20/20 vectors');
  const verify = f.prs[1].body.slice(f.prs[1].body.indexOf('## Verify'));
  const at = text => { const index = verify.indexOf(text); assert.notEqual(index, -1, text); return index; };
  assert.doesNotMatch(verify, /^# Verify$/m, 'one Verify heading');
  assert.ok(at('### Vector results') < at('### Formal check') && at('### Formal check') < at('### Commands and captured output') && at('### Commands and captured output') < at('### Coverage limits'), verify);
  assert.ok(at('Build commit') < at('### Vector results'), 'the text before the first heading stays on top');
  assert.equal((verify.match(/<details><summary>/g) ?? []).length, 2, 'the two long blocks fold');
  assert.match(verify, /<details><summary>Commands \(40 lines\)<\/summary>\n\n```sh\necho step 0\n/);
  assert.match(verify, /<details><summary>Output \(30 lines\)<\/summary>\n\n```text\nok 0\n/);
  assert.match(verify, /### Formal check\n\n\*\*Proved \(bounded\)\*\*: 1,208,412 inputs\.\n\n```text\n# FORMAL checked=1208412/, 'a short block stays open');
  assert.match(verify, /\| `split-100` \| `\$33\.33` \|/, 'nothing is lost');
});

// The 0.1.7 verify step writes the tables first and the commands last, in a closed <details> block; pdd keeps that order.
test('0.1.7 #14: a verify.md that already folds its commands in <details> keeps its order', async t => {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'two');
  await stepDone({ step: 'change', summary: 'two', cwd: run.root }, f.agentPorts());
  const verify = ['| Case | Expected | Code got | Result |', '|---|---|---|---|', '| a | 1 | 1 | Pass |', '', '## Commands', '', 'Ran the replay.', '',
    '<details><summary>Commands and output</summary>', '', '```sh', ...Array.from({ length: 25 }, (_, i) => `echo ${i}`), '```', '', '</details>', '', '## Formal check', '', 'Proved (bounded).', ''].join('\n');
  writeFileSync(join(run.runDir, 'verify.md'), verify);
  await lastSteps(f, run, await stepDone({ step: 'verify', summary: 'ok', cwd: run.root }, f.agentPorts()));
  const body = f.prs[0].body;
  assert.ok(body.includes(verify.replaceAll('## ', '### ').trim()), body);
  assert.equal((body.match(/<details>/g) ?? []).length, 1);
});

// skills-017 7d2d7e7 (bug check step): the check summary starts with the verdict and "Before ✗ … → after ✓ …" for the top of PR 1.
const verdictSummary = ['Verdict: the bug is in the PROMPT (its check fails on the issue\'s case).',
  'Before ✗ 0 of 1 criteria https://rt.example.test/r/da176d28-b1a3 → after ✓ 5 of 5 criteria https://rt.example.test/r/526de1aa-e631',
  'Runtime check (split-cent-conservation) (DRAFT): ✓ 5 of 5 criteria · 20/20 checks · 15 AI calls',
  'Report (split-cent-conservation): https://rt.example.test/r/526de1aa-e631'];
for (const [name, summary] of [['one per line', verdictSummary.join('\n')], ['joined with "; "', verdictSummary.join('; ')]]) {
  test(`0.1.7 #15: PR 1 starts with the Verdict line and the Before → after line from the check summary (${name})`, async t => {
    const { f, run } = await featureAtTryGate(t);
    f.tick(); await stepDone({ step: 'check', summary, cwd: run.root }, f.agentPorts());
    await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
    f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
    assert.deepEqual(f.prs[0].body.split('\n').slice(0, 5), [
      'Verdict: the bug is in the PROMPT (its check fails on the issue\'s case).',
      'Before ✗ 0 of 1 criteria https://rt.example.test/r/da176d28-b1a3 → after ✓ 5 of 5 criteria https://rt.example.test/r/526de1aa-e631 (report links expire after 7 days)',
      'Runtime check (split-cent-conservation) (DRAFT): ✓ 5 of 5 criteria · 20/20 checks · 15 AI calls',
      '', 'Part of #17']);
    assert.deepEqual(f.prs[0].body.split('\n').filter(line => line.startsWith('Report')), [], 'the report links of the Before → after line are not listed again');
    assert.doesNotMatch(f.prs[0].body, /^Runtime report links expire after 7 days\.$/m, 'the top line says it already');
  });
}

test('0.1.7 #15: "Before: no prompt" is lifted too, and a check summary without a verdict keeps the 0.1.6 top', async t => {
  const { f, run } = await featureAtTryGate(t);
  f.tick(); await stepDone({ step: 'check', summary: 'Verdict: no prompt covers this yet; the bug can only be in the code.\nBefore: no prompt → after ✓ 3 of 3 criteria https://rt.example.test/r/after-3\nRuntime check: ✓ 3 of 3 criteria · 9/9 checks · 2 AI calls\nReport: https://rt.example.test/r/after-3', cwd: run.root }, f.agentPorts());
  await stepDone({ step: 'try', summary: 'skipped', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  assert.deepEqual(f.prs[0].body.split('\n').slice(0, 4), ['Verdict: no prompt covers this yet; the bug can only be in the code.',
    'Before: no prompt → after ✓ 3 of 3 criteria https://rt.example.test/r/after-3 (report links expire after 7 days)', 'Runtime check: ✓ 3 of 3 criteria · 9/9 checks · 2 AI calls', '']);
});

function topicBase(f, name = 'round3/workflow-base') {
  const main = f.git(f.source, 'rev-parse', 'refs/heads/main');
  f.git(f.source, 'switch', '-q', '-c', name);
  writeFileSync(join(f.source, 'topic-only.txt'), 'Approved prompt work for this isolated base.\n');
  f.git(f.source, 'add', '.'); f.git(f.source, 'commit', '-qm', 'Topic base');
  const sha = f.git(f.source, 'rev-parse', 'HEAD');
  f.git(f.source, 'update-ref', `refs/remotes/origin/${name}`, sha);
  f.git(f.source, 'switch', '-q', 'main');
  // A same-named local branch is deliberately different: --base always means origin's branch.
  f.git(f.source, 'branch', '-f', name, main);
  return { name, sha, main };
}

// Wrong: --base is ignored, resolves a local branch, or creates a PR against the repository default.
test('BASE1: an explicit origin topic base owns the worktree commit and PR target without a default/base push', async t => {
  const f = await fixture(t), base = topicBase(f), fetched = [], original = f.ports.execFile;
  f.ports.execFile = (file, args, opts) => { if (file === 'git' && args[0] === 'fetch') fetched.push(args); return original(file, args, opts); };
  const started = await startRun({ name: 'small-change', issue: '17', agent: 'claude', base: base.name, cwd: f.source, packageRoot }, f.ports);
  assert.equal(started.exitCode, 0, started.message);
  assert.match(started.message, /Base: origin\/round3\/workflow-base/);
  const run = f.record();
  assert.equal(run.baseBranch, base.name); assert.equal(run.baseSha, base.sha);
  assert.equal(f.git(run.root, 'rev-parse', 'HEAD'), base.sha);
  assert.ok(existsSync(join(run.root, 'topic-only.txt')));
  assert.deepEqual(fetched, [['fetch', 'origin', `refs/heads/${base.name}:refs/remotes/origin/${base.name}`]]);
  await stepDone({ step: 'scope', summary: 'Change value in the isolated topic', cwd: run.root }, f.agentPorts());
  f.tick();
  assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
  f.git(run.root, 'commit', '-qam', 'Use value two');
  for (const step of f.record().areas.at(-1).steps) {
    f.tick(); const out = await stepDone({ step, summary: `${step} done`, cwd: run.root }, f.agentPorts());
    assert.equal(out.exitCode, 0, out.message);
  }
  assert.equal(f.prs.length, 1); assert.equal(f.prs[0].baseRefName, base.name);
  assert.deepEqual(f.pushes.map(args => args[2].split(':')[1]), [`refs/heads/${run.branch}`]);
  assert.equal(f.git(f.source, 'rev-parse', 'refs/heads/main'), base.main);
  assert.equal(f.git(f.source, 'rev-parse', 'refs/remotes/origin/main'), base.main);
  assert.equal(f.git(f.source, 'rev-parse', `refs/remotes/origin/${base.name}`), base.sha);
});

// Wrong: an explicit failed/missing base silently uses a stale tracking ref, local branch or main.
test('BASE2: failed explicit fetch or missing remote commit stops before worktree, record, claim or chat effects', async t => {
  for (const mode of ['fetch-failed', 'fetch-refused', 'missing-remote']) {
    const f = await fixture(t), base = topicBase(f), original = f.ports.execFile;
    if (mode === 'missing-remote') f.git(f.source, 'update-ref', '-d', `refs/remotes/origin/${base.name}`);
    f.ports.execFile = (file, args, opts) => {
      if (mode === 'fetch-failed' && file === 'git' && args[0] === 'fetch') throw Error('unavailable');
      if (mode === 'fetch-refused' && file === 'git' && args[0] === 'fetch') return { stdout: '', code: 128 };
      return original(file, args, opts);
    };
    const result = await startRun({ name: 'small-change', issue: '17', base: base.name, cwd: f.source, packageRoot }, f.ports);
    assert.equal(result.exitCode, 1, `${mode}: ${result.message}`);
    assert.ok(result.message.includes(base.name), result.message);
    assert.equal(f.herdr.calls.length, 0); assert.deepEqual(f.pushes, []);
    assert.equal(existsSync(join(f.source, '.git/pdd/runs/17/status.json')), false);
    assert.equal(existsSync(join(f.source, '.git/pdd/worktree-assignments')), false);
    assert.equal(f.git(f.source, 'worktree', 'list', '--porcelain').split('\n').filter(line => line.startsWith('worktree ')).length, 1);
  }
});

// Wrong: a revision, option or full ref is accepted as a branch and reaches startup effects.
test('BASE3: invalid explicit branch names refuse before fetch, allocation or chat', async t => {
  const f = await fixture(t), original = f.ports.execFile;
  let gh = 0;
  f.ports.execFile = (file, args, opts) => { if (file === 'gh') gh++; return original(file, args, opts); };
  for (const base of ['', null, 42, '-topic', '../main', '/tmp/topic', 'refs/heads/main', 'HEAD', 'main~1', 'main:other', '@{-1}', 'main\nother']) {
    const result = await startRun({ name: 'small-change', issue: '17', base, cwd: f.source, packageRoot }, f.ports);
    assert.equal(result.exitCode, 1, String(base)); assert.match(result.message, /base|branch/i);
  }
  assert.equal(gh, 0); assert.equal(f.fetches, 0); assert.equal(f.herdr.calls.length, 0);
  assert.equal(existsSync(join(f.source, '.git/pdd/runs/17/status.json')), false);
});

// Wrong: choosing a base works for PR 1 but a later code area silently returns to main.
test('BASE4: PR 2 stacks on open PR 1 and returns to the saved topic base after PR 1 merges', async t => {
  for (const merged of [false, true]) {
    const base = 'round3/bookshelf-workflow-base';
    const { f, run, done } = await featureToPr1(t, undefined, base);
    const main = f.git(f.source, 'rev-parse', 'refs/heads/main');
    assert.equal(f.prs[0].baseRefName, base);
    if (merged) f.mergedNumbers.push(23);
    const code = await approveRun({ ref: '17', cwd: f.source }, f.ports);
    assert.equal(code.exitCode, 0, code.message);
    assert.equal(f.record().baseBranch, base);
    assert.equal(f.record().prBase, merged ? base : run.branch);
    assert.equal(f.git(run.root, 'rev-parse', 'HEAD'), f.prs[0].headRefOid);
    writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n');
    f.git(run.root, 'commit', '-qam', 'Code on selected base');
    await done('build', 'value is two'); await done('verify', 'tests pass');
    assert.equal(f.prs[1].baseRefName, merged ? base : run.branch);
    assert.ok(f.pushes.every(args => args[2].split(':')[1].startsWith('refs/heads/pdd/')));
    assert.equal(f.git(f.source, 'rev-parse', 'refs/heads/main'), main);
    assert.equal(f.git(f.source, 'rev-parse', 'refs/remotes/origin/main'), main);
  }
});

// Wrong: a failed replacement start frees a cancelled run's custody before its new base is usable.
test('BASE5: explicit base failure preserves a cancelled run, worktree and issue claim', async t => {
  const f = await fixture(t); await f.run();
  const old = f.record();
  assert.equal((await cancelRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const recordFile = join(old.runDir, 'status.json');
  const claimFile = join(f.source, '.git/pdd/worktree-assignments/issues/17.json');
  const record = readFileSync(recordFile), claim = readFileSync(claimFile);
  const original = f.ports.execFile;
  f.ports.execFile = (file, args, opts) => {
    if (file === 'git' && args[0] === 'fetch') throw Error('base unavailable');
    return original(file, args, opts);
  };
  const out = await startRun({ name: 'small-change', issue: '17', base: 'round3/missing', cwd: f.source, packageRoot }, f.ports);
  assert.equal(out.exitCode, 1, out.message);
  assert.ok(readFileSync(recordFile).equals(record)); assert.ok(readFileSync(claimFile).equals(claim));
  assert.ok(existsSync(old.root)); assert.equal(f.git(f.source, 'worktree', 'list', '--porcelain').split('\n').filter(line => line.startsWith('worktree ')).length, 2);
});

const closedChannel = () => Object.assign(Error('request handling failed: receiving on a closed channel'), { code: 'server_unavailable' });

// Wrong: a failed first start saves running/no chat, so public status invents agent progress.
test('CHATFAIL1: closed-channel startup and open failures stay waiting on the same explicit base and recover only after a real start', async t => {
  const f = await fixture(t, { name: 'bug', agent: 'codex' }), base = topicBase(f, 'round3/tipjar-workflow-base');
  const healthy = f.ports.herdr;
  f.ports.herdr = async () => { throw closedChannel(); };
  f.ports.spawnServer = () => assert.fail('Do not restart a server whose request failed');
  const start = await startRun({ name: 'bug', issue: '17', agent: 'codex', base: base.name, cwd: f.source, packageRoot }, f.ports);
  assert.equal(start.exitCode, 1, start.message);
  const before = f.record(), claimFile = join(f.source, '.git/pdd/worktree-assignments/issues/17.json'), claim = readFileSync(claimFile);
  assert.equal(before.state, 'waiting'); assert.equal(before.chatFailure.code, 'server_unavailable');
  assert.equal(before.chatFailure.phase, 'start'); assert.equal(before.chats.length, 0); assert.equal(before.stageAgent, null);
  assert.deepEqual(before.waitingFor.decisions, []); assert.match(before.waitingFor.what, /server_unavailable/);
  assert.equal(before.baseBranch, base.name); assert.equal(before.baseSha, base.sha);
  for (const input of [{ ref: '17' }, {}, { all: true }]) {
    const out = await runStatus({ ...input, json: true, cwd: f.source }, f.ports);
    const row = JSON.parse(out.message).runs[0];
    assert.equal(row.group, 'waiting'); assert.match(row.words, /server_unavailable/);
    assert.doesNotMatch(row.words, /agent working/); assert.match(row.words, /workflow open 17/);
  }
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /State:.*server_unavailable/);
  const again = await openRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(again.exitCode, 1); assert.equal(f.record().state, 'waiting');
  assert.equal(f.record().runId, before.runId); assert.equal(f.record().root, before.root);
  assert.ok(readFileSync(claimFile).equals(claim)); assert.equal(f.fetches, 1);
  f.ports.herdr = healthy;
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const after = f.record();
  assert.equal(after.state, 'running'); assert.equal(after.chatFailure ?? null, null); assert.equal(after.chats.length, 1);
  assert.equal(after.runId, before.runId); assert.equal(after.root, before.root); assert.equal(after.baseSha, base.sha);
  assert.equal(after.decisions.length, 0); assert.ok(readFileSync(claimFile).equals(claim)); assert.equal(f.fetches, 1);
});

// Wrong: a later-area start failure loses the approved transition or still claims work in the new area.
test('CHATFAIL2: an approved transition keeps its decision and worktree when the next chat fails, then open starts only that area', async t => {
  const f = await fixture(t); await f.run(); const before = f.record();
  await stepDone({ step: 'scope', summary: 'Scope approved by the person next', cwd: before.root }, f.agentPorts());
  const healthy = f.ports.herdr; f.ports.herdr = async () => { throw closedChannel(); };
  const approved = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(approved.exitCode, 1);
  const failed = f.record(); assert.equal(failed.area, 1); assert.equal(failed.state, 'waiting');
  assert.equal(failed.decisions.length, 1); assert.ok(failed.done.scope); assert.equal(failed.chats.length, 1);
  assert.equal(failed.chatFailure.area, 'build'); assert.equal(failed.gate, null);
  assert.equal(JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0].group, 'waiting');
  f.ports.herdr = healthy;
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const after = f.record(); assert.equal(after.chats.length, 2); assert.equal(after.chats[1].area, 'build');
  assert.equal(after.decisions.length, 1); assert.equal(after.area, 1); assert.equal(after.root, before.root);
  assert.equal(after.chatFailure ?? null, null); assert.equal(after.state, 'running');
});

// Wrong: an unavailable inspection is treated as no agent, causing a second native launch/resume.
test('CHATFAIL3: closed-channel inspection cannot resume a chat; status is unavailable until confirmed recovery', async t => {
  const f = await fixture(t); await f.run(); const run = f.record(), pane = f.herdr.paneOf(run.chats[0]);
  const healthy = f.ports.herdr;
  f.ports.herdr = async args => { if (args[0] === 'agent') throw closedChannel(); return healthy(args); };
  const unknown = JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0];
  assert.equal(unknown.group, 'waiting'); assert.match(unknown.words, /unavailable/i);
  const out = await openRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(out.exitCode, 1); assert.equal(pane.commands.length, 1); assert.equal(f.record().chatFailure.phase, 'open');
  pane.agent = null; f.ports.herdr = healthy;
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  assert.equal(pane.commands.length, 2); assert.match(pane.commands[1], /--resume/);
  assert.equal(f.record().chats.length, 1); assert.equal(f.record().chatFailure ?? null, null);
});

// Wrong: a lost launch reply discards the original pane identity and open starts another agent/tab.
test('CHATFAIL4: a lost launch reply retains the prepared chat, and open reuses its observed live agent', async t => {
  const f = await fixture(t), healthy = f.ports.herdr;
  f.ports.herdr = async args => { const reply = await healthy(args); if (args[0] === 'pane' && args[1] === 'run') throw closedChannel(); return reply; };
  assert.equal((await f.run()).exitCode, 1);
  const before = f.record(); assert.equal(before.chats.length, 1); assert.equal(before.chats[0].startUnconfirmed, true);
  const pane = f.herdr.paneOf(before.chats[0]), count = f.herdr.tabs.length;
  assert.equal(pane.commands.length, 1);
  f.ports.herdr = healthy;
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const after = f.record(); assert.equal(after.chats.length, 1); assert.equal(after.chats[0].paneId, before.chats[0].paneId);
  assert.equal(after.chats[0].startUnconfirmed ?? false, false); assert.equal(after.chatFailure ?? null, null);
  assert.equal(f.herdr.tabs.length, count); assert.equal(pane.commands.length, 1); assert.equal(after.state, 'running');
});

// Wrong: after an uncertain launch, missing agent inspection automatically sends the first prompt again.
test('CHATFAIL5: an unconfirmed launch without a live agent refuses another launch and cancellation still wins', async t => {
  const f = await fixture(t), healthy = f.ports.herdr;
  f.ports.herdr = async args => { if (args[0] === 'pane' && args[1] === 'run') throw closedChannel(); return healthy(args); };
  assert.equal((await f.run()).exitCode, 1);
  const before = f.record(); assert.equal(before.chats.length, 1);
  const tabs = f.herdr.tabs.length; f.ports.herdr = healthy;
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 1);
  assert.equal(f.record().chats.length, 1); assert.equal(f.herdr.tabs.length, tabs);
  assert.equal(f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run').length, 0);
  assert.equal((await cancelRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const row = JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0];
  assert.equal(row.group, 'cancelled'); assert.equal(row.words, 'cancelled'); assert.deepEqual(f.record().waitingFor, { decisions: [], what: null });
});

// Wrong: older failed-start records with no chat still fall through to agent-working forever.
test('CHATFAIL6: legacy no-chat active records report unconfirmed startup without attempting Herdr recovery', async t => {
  const f = await fixture(t); f.ports.herdr = async () => { throw closedChannel(); }; await f.run();
  const run = f.record(); delete run.chatFailure; run.state = 'running';
  writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
  f.ports.herdr = () => assert.fail('Status must not launch or probe a chat identity it does not have');
  const row = JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0];
  assert.equal(row.group, 'waiting'); assert.match(row.words, /startup.*not confirmed/i); assert.doesNotMatch(row.words, /agent working/);
});

// Wrong: recovering the chat accidentally approves a gate or clears a person's outstanding question.
test('CHATFAIL7: chat recovery preserves a waiting approval gate or person question', async t => {
  for (const kind of ['gate', 'question']) {
    const f = await fixture(t); await f.run(); const run = f.record();
    if (kind === 'gate') await stepDone({ step: 'scope', summary: 'Ready for review', cwd: run.root }, f.agentPorts());
    else await askPerson({ text: 'Which color?', cwd: run.root }, f.agentPorts());
    const waiting = f.record(), healthy = f.ports.herdr;
    f.ports.herdr = async () => { throw closedChannel(); };
    assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 1);
    assert.deepEqual(f.record().gate, waiting.gate); assert.deepEqual(f.record().question, waiting.question);
    f.ports.herdr = healthy;
    assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
    const recovered = f.record(); assert.equal(recovered.state, 'waiting'); assert.equal(recovered.decisions.length, 0);
    assert.deepEqual(recovered.gate, waiting.gate); assert.deepEqual(recovered.question, waiting.question);
    assert.equal(recovered.chatFailure ?? null, null);
    assert.deepEqual(recovered.waitingFor.decisions, kind === 'gate' ? ['approve', 'changes'] : ['changes']);
  }
});

// Wrong: a lost resume reply causes open to issue the resume command twice.
test('CHATFAIL8: a lost resume reply marks the existing chat unconfirmed and a later open only observes it', async t => {
  const f = await fixture(t); await f.run(); const run = f.record(), pane = f.herdr.paneOf(run.chats[0]);
  pane.agent = null; const healthy = f.ports.herdr;
  f.ports.herdr = async args => { const reply = await healthy(args); if (args[0] === 'pane' && args[1] === 'run') throw closedChannel(); return reply; };
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 1);
  assert.equal(pane.commands.length, 2); assert.equal(f.record().chats[0].startUnconfirmed, true);
  f.ports.herdr = healthy;
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  assert.equal(pane.commands.length, 2); assert.equal(f.record().chats.length, 1);
  assert.equal(f.record().chatFailure ?? null, null); assert.equal(f.record().chats[0].startUnconfirmed ?? false, false);
});

// Wrong: recovery replaces a missing unconfirmed tab and persists new IDs, losing the original launch identity.
test('CHATFAIL9: a missing tab after an unconfirmed launch preserves the original identity without creating a replacement', async t => {
  const f = await fixture(t), healthy = f.ports.herdr;
  f.ports.herdr = async args => { const reply = await healthy(args); if (args[0] === 'pane' && args[1] === 'run') throw closedChannel(); return reply; };
  assert.equal((await f.run()).exitCode, 1);
  const before = f.record(), chat = before.chats[0], pane = f.herdr.paneOf(chat);
  f.herdr.tabs = f.herdr.tabs.filter(tab => tab.tab_id !== chat.tabId);
  const tabs = f.herdr.tabs.length; f.ports.herdr = healthy;
  const out = await openRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(out.exitCode, 1); assert.match(out.message, /saved tab.*unavailable/i);
  const after = f.record(); assert.equal(after.chats.length, 1);
  assert.equal(after.chats[0].tabId, chat.tabId); assert.equal(after.chats[0].paneId, chat.paneId);
  assert.equal(after.chats[0].startUnconfirmed, true); assert.equal(after.state, 'waiting');
  assert.equal(after.root, before.root); assert.equal(after.baseSha, before.baseSha);
  assert.equal(f.herdr.tabs.length, tabs); assert.equal(pane.commands.length, 1);
});


test('RELEASE10: confirmed gone unconfirmed tab/agent offers a fresh start without losing the run', async t => {
  const f = await fixture(t), healthy = f.ports.herdr;
  f.ports.herdr = async args => { if(args[0]==='pane'&&args[1]==='run') throw closedChannel(); return healthy(args); };
  assert.equal((await f.run()).exitCode,1);
  const before=f.record(),chat=before.chats[0];
  f.herdr.tabs=f.herdr.tabs.filter(tab=>tab.tab_id!==chat.tabId);
  f.herdr.panes=f.herdr.panes.filter(pane=>pane.pane_id!==chat.paneId);
  f.ports.herdr=healthy;const tabs=f.herdr.tabs.length;
  const offered=await openRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(offered.exitCode,1);assert.match(offered.message,/pdd workflow open 17/);
  const cleared=f.record();assert.equal(cleared.chats.length,0);assert.equal(cleared.abandonedChats[0].paneId,chat.paneId);
  assert.equal(cleared.root,before.root);assert.equal(cleared.baseSha,before.baseSha);assert.equal(cleared.state,'waiting');
  assert.equal(f.herdr.tabs.length,tabs,'first open offers but never dispatches');
  assert.equal((await openRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  const after=f.record();assert.equal(after.chats.length,1);assert.equal(after.abandonedChats.length,1);
  assert.notEqual(after.chats[0].paneId,chat.paneId);assert.equal(after.root,before.root);
  assert.equal(f.herdr.paneOf(after.chats[0]).commands.length,1);
});

test('RELEASE11: PR2 refreshes its selected remote base with an explicit tracking refspec', async t => {
  const base='feature/checkout';const {f,run}=await featureToPr1(t,undefined,base);
  f.mergedNumbers.push(23);
  f.git(run.root,'commit','--allow-empty','-qm','Remote base advanced after PR1');
  const newest=f.git(run.root,'rev-parse','HEAD'),tracking='refs/remotes/origin/'+base;
  const expected='refs/heads/'+base+':'+tracking,original=f.ports.execFile;let refreshed=false;
  f.ports.execFile=async(file,args,opts)=>{
    if(file==='git'&&args[0]==='fetch'&&args[2].includes(base)){
      if(args[2]===expected){f.git(f.source,'update-ref',tracking,newest);refreshed=true;}
      return {stdout:''};
    }
    return original(file,args,opts);
  };
  const code=await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(code.exitCode,0,code.message);assert.equal(refreshed,true);
  assert.equal(f.git(run.root,'rev-parse','HEAD'),newest,'PR2 uses the newly fetched base');
});

// Greg #2442: newer verify results must beat the old check without treating UNKNOWN as a failure.
test('GREG2442-1: newest compatible verify evidence replaces 7/8 with 17/17; unknown stays unknown', async t => {
  const { f, run } = await featureAtTryGate(t);
  const old = Array.from({ length: 8 }, (_, i) => `Runtime check (story-${i}): ${i === 7 ? 'unknown · 0' : '✓ 1'} of 1 criteria · 1/1 checks · 1 AI call`).join('\n');
  f.tick(); await stepDone({ step: 'check', summary: old, cwd: run.root }, f.agentPorts());
  let data = JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0].stories;
  assert.equal(data.pass, 7); assert.deepEqual(data.failing, []); assert.deepEqual(data.unknown, ['story-7']);
  const newer = Array.from({ length: 17 }, (_, i) => `Runtime check (story-${i}): ✓ 1 of 1 criteria · 1/1 checks · 1 AI call`).join('\n');
  f.tick(); await stepDone({ step: 'verify', summary: newer, cwd: run.root }, f.agentPorts());
  data = JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0].stories;
  assert.equal(data.pass, 17); assert.equal(data.total, 17); assert.deepEqual(data.failing, []);
});

test('GREG2442-2: changed uncommitted source invalidates pass evidence, byte-identical content restores it', async t => {
  const { f, run } = await featureAtTryGate(t);
  const file = join(run.root, 'value.mjs'), original = readFileSync(file);
  writeFileSync(file, 'export const value = 999;\n');
  let out = await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports);
  let data = JSON.parse(out.message).runs[0].stories;
  assert.equal(data.pass, 0); assert.deepEqual(data.failing, []); assert.ok(data.unknown.length);
  writeFileSync(file, original);
  data = JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0].stories;
  assert.equal(data.pass, 1);
});

test('GREG2442-3: saved check JSON records only source-verified evidence and preserves all workflow/publication state', async t => {
  const { recordEvidence } = await import('../src/workflow-runner.mjs');
  assert.equal(typeof recordEvidence, 'function');
  const { captureSource } = await import('../src/runtime-preflight.mjs');
  const { f, run } = await featureAtTryGate(t);
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, { ...f.ports, confirm: async question => /open PR 1/.test(question) });
  assert.equal(f.prs.length, 1); const prBody = f.prs[0].body;
  const fixtureRoot = join(packageRoot, 'test/fixtures/harbor');
  const { cpSync } = await import('node:fs');
  for (const dir of ['prompts', 'tests', 'user_stories']) cpSync(join(fixtureRoot, dir), join(run.root, dir), { recursive: true });
  const rows = ['tests/place-order.json', 'tests/unknown-item.json'].map(test => ({ test, story: test.split('/').at(-1).replace('.json', ''), state: 'passed',
    criteria: { passed: 1, total: 1 }, checks: { passed: 1, total: 1 }, calls: 0,
    summary_line: `Runtime check (${test.split('/').at(-1).replace('.json', '')}): ✓ 1 of 1 criterion · 1/1 checks · 0 AI calls` }));
  const source = captureSource(run.root, { tests: rows.map(r => r.test), appMap: null });
  const file = join(f.base, 'evidence.json'), doc = { repo: run.root, source_sha256: source.sha256, rows, batch: 'older-byte-identical-receipt' };
  writeFileSync(file, JSON.stringify(doc));
  const before = f.record(), gitBefore = f.git(run.root, 'status', '--porcelain'), heads = f.git(run.root, 'rev-parse', 'HEAD');
  const noExternal = { ...f.ports, herdr: async () => assert.fail('Herdr'), execFile: async (cmd, args, opts) => {
    assert.equal(cmd, 'git'); assert.ok(['rev-parse', 'ls-files'].includes(args[0]), args.join(' ')); return exec(cmd, args, { ...opts, encoding: 'utf8' });
  } };
  f.tick(); const result = await recordEvidence({ ref: '17', summaryFile: file, cwd: run.root }, noExternal);
  assert.equal(result.exitCode, 0, result.message);
  const after = f.record();
  for (const key of ['done', 'state', 'gate', 'question', 'decisions', 'chats', 'pr']) assert.deepEqual(after[key], before[key], key);
  assert.equal(f.prs.length, 1); assert.equal(f.prs[0].body, prBody);
  assert.equal(after.evidence.length, 1); assert.equal(after.evidence[0].receipt.batch, doc.batch);
  assert.equal(f.git(run.root, 'rev-parse', 'HEAD'), heads); assert.equal(f.git(run.root, 'status', '--porcelain'), gitBefore);
  const data = JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0].stories;
  assert.equal(data.pass, 2); assert.equal(data.total, 2);
  for (const mutate of [d => { d.rows[0].state = 'unknown'; }, d => { d.rows[0].story = 'invented'; }, d => { delete d.source_sha256; }, d => { d.repo = f.source; }]) {
    const invalid = structuredClone(doc); mutate(invalid); writeFileSync(file, JSON.stringify(invalid));
    const beforeBad = readFileSync(join(run.runDir, 'status.json'), 'utf8');
    assert.notEqual((await recordEvidence({ ref: '17', summaryFile: file, cwd: run.root }, noExternal)).exitCode, 0);
    assert.equal(readFileSync(join(run.runDir, 'status.json'), 'utf8'), beforeBad);
  }
  writeFileSync(file, JSON.stringify(doc));
  writeFileSync(join(run.root, 'user_stories/place-order.md'), 'changed');
  const unchanged = readFileSync(join(run.runDir, 'status.json'), 'utf8');
  const stale = await recordEvidence({ ref: '17', summaryFile: file, cwd: run.root }, noExternal);
  assert.notEqual(stale.exitCode, 0); assert.match(stale.message, /source/i);
  assert.equal(readFileSync(join(run.runDir, 'status.json'), 'utf8'), unchanged);
});


test('GREG2442-4: later stale-source verify cannot override compatible older results', async t => {
  const { f, run } = await featureAtTryGate(t);
  const file = join(run.root, 'value.mjs'), original = readFileSync(file);
  writeFileSync(file, 'export const value = 999;\n');
  f.tick(); await stepDone({ step: 'verify', summary: 'Runtime check: ✗ 0 of 2 criteria', cwd: run.root }, f.agentPorts());
  writeFileSync(file, original);
  const data = JSON.parse((await runStatus({ ref: '17', json: true, cwd: f.source }, f.ports)).message).runs[0].stories;
  assert.equal(data.pass, 1); assert.deepEqual(data.failing, []);
});

// Wrong (0.1.7 tester, #2518): verify.md went whole into the PR body (105,489 characters) and GitHub refused it.
async function smallChangeAtVerify(t) {
  const f = await fixture(t);
  await f.run(); const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); await approveRun({ ref: '17', cwd: f.source }, f.ports);
  writeFileSync(join(run.root, 'value.mjs'), 'export const value = 2;\n'); f.git(run.root, 'commit', '-qam', 'two');
  await stepDone({ step: 'change', summary: 'two', cwd: run.root }, f.agentPorts());
  return { f, run };
}
test('PRBODY4: a huge verify.md keeps the PR body under 60,000 characters with its results, its failures and a note', async t => {
  const { f, run } = await smallChangeAtVerify(t);
  const log = Array.from({ length: 3000 }, (_, i) => `ok ${i} - case ${i} passed in 3 ms`).join('\n');
  const notes = Array.from({ length: 2000 }, (_, i) => i === 1500 ? 'Case 1500: expected 4, got 5 ✗ (failed)' : `Note ${i}: the value is still two, as the Story says.`).join('\n');
  const verify = `✗ 1 vectors fail\n\n## Vectors\n\n| case | expected | code | result |\n|---|---|---|---|\n| 1 | 2 | 2 | same |\n| 1500 | 4 | 5 | different ✗ |\n\n## Formal check\nProved (bounded): 0..999.\n\n## Output\n\n\`\`\`text\n${log}\n\`\`\`\n\n## Notes\n\n${notes}\n`;
  assert.ok([...verify].length > 105_000);
  writeFileSync(join(run.runDir, 'verify.md'), verify);
  await lastSteps(f, run, await stepDone({ step: 'verify', summary: 'one case fails', cwd: run.root }, f.agentPorts()));
  const body = f.prs[0].body;
  assert.ok([...body].length <= 60_000, String([...body].length));
  assert.equal(body.split('\n')[0],'Old-code proof: not run.');assert.match(body,/Test inventory commits: [^\n]+\n✗ 1 vectors fail/);
  for (const kept of ['| 1500 | 4 | 5 | different ✗ |', 'Proved (bounded): 0..999.', '- Output (3000 lines): not shown here.', 'Case 1500: expected 4, got 5 ✗ (failed)'])
    assert.ok(body.includes(kept), kept);
  assert.match(body, /_The full verify report has \d{3},\d{3} characters, more than a PR description can hold \(GitHub's limit is 65,536\)\. This is a summary: its first \d+ lines; \d+ more lines are not shown, and 1 of them reports a failure\. The PR author has the full report: verify\.md in the run folder\._/);
});

test('PRBODY5: when GitHub refuses the PR, done names the reason and the fix, and the next done opens it without a second push', async t => {
  const { f, run } = await smallChangeAtVerify(t);
  writeFileSync(join(run.runDir, 'verify.md'), '| case | result |\n|---|---|\n| 1 | same |\n');
  f.createError = 'pull request create failed: GraphQL: Body is too long (maximum is 65536 characters) (createPullRequest)\n';
  const refused = await lastSteps(f, run, await stepDone({ step: 'verify', summary: 'all cases pass', cwd: run.root }, f.agentPorts()));
  assert.equal(refused.exitCode, 1);
  assert.match(refused.message, /The PR did not open: GitHub refused to open the PR: its description is too long \(GitHub's limit is 65,536 characters\)\. The branch is pushed; no PR was opened\. Make the PR description shorter, then run done formal again\./);
  assert.doesNotMatch(refused.message, /unconfirmed/);
  assert.equal(f.pushes.length, 1); assert.equal(f.prs.length, 0);
  f.tick();
  const opened = await stepDone({ step: 'formal', summary: 'formal done', cwd: run.root }, f.agentPorts());
  assert.equal(opened.exitCode, 0, opened.message);
  assert.equal(f.prs.length, 1); assert.equal(f.pushes.length, 1, 'no second push');
});

test('PRBODY7: failures and report links inside authored details or auto-folded output survive summarization', async t => {
  for (const style of ['details', 'fence', 'details-with-notes']) {
    const { f, run } = await smallChangeAtVerify(t);
    const failure = 'Critical hidden vector failed ✗', url = 'https://rt.example.test/r/hidden-vector';
    const log = Array.from({ length: 3000 }, (_, i) => i === 2500 ? failure : i === 2501 ? `Report: ${url}` : `ok ${i} - a long successful verification output line`).join('\n');
    const block = style.startsWith('details') ? `<details><summary>Failed output</summary>\n\n${log}\n</details>` : `\`\`\`text\n${log}\n\`\`\``;
    const verify = `# Verify\n\n## Output\n\n${block}\n${style.endsWith('notes') ? '\n## Notes\n' + 'A long supplementary note with successful verification details.\n'.repeat(2000) : ''}`;
    writeFileSync(join(run.runDir, 'verify.md'), verify);
    await lastSteps(f, run, await stepDone({ step: 'verify', summary: 'verification recorded', cwd: run.root }, f.agentPorts()));
    const body = f.prs[0].body;
    assert.ok([...body].length <= 60_000); assert.ok(body.includes(failure), style); assert.ok(body.split('\n').includes(`Report: ${url} (report links expire after 7 days)`), style);
    assert.match(body, /full verify report/); assert.doesNotMatch(body, /<details\b/); assert.equal(readFileSync(join(run.runDir, 'verify.md'), 'utf8'), verify);
  }
});

// A real Git primary/linked/bare layout, with Herdr's repository-parent rule.
async function linkedSourceFixture(t,kind='linked') {
  const f=await fixture(t,{agent:'codex'});let primary=f.source,source=f.source;
  if(kind==='bare'){
    primary=join(f.base,'project.git');f.git(f.source,'clone','--bare',f.source,primary);
    f.git(primary,'remote','set-url','origin','https://github.com/example/project.git');
    f.git(primary,'update-ref','refs/remotes/origin/main',f.git(primary,'rev-parse','main'));
  }
  if(kind!=='normal'){source=join(f.base,'caller');f.git(primary,'worktree','add','-b','caller',source,'main');}
  const healthy=f.ports.herdr;
  f.ports.herdr=async args=>{
    if(args[0]==='worktree'&&args[1]==='open'){
      const parent=f.herdr.workspaces.find(w=>w.workspace_id===args[args.indexOf('--workspace')+1]);
      const pane=f.herdr.panes.find(p=>p.workspace_id===parent.workspace_id);
      if(pane.cwd!==primary||f.refuseOnce){
        f.refuseOnce=false;f.herdr.calls.push(args);
        throw Object.assign(Error('New and open worktree actions start from the repo parent workspace.'),{code:'linked_worktree_source'});
      }
    }
    return healthy(args);
  };
  const record=()=>JSON.parse(readFileSync(join(f.git(source,'rev-parse','--path-format=absolute','--git-common-dir'),'pdd/runs/17/status.json')));
  const start=()=>startRun({name:'small-change',issue:'17',agent:'codex',base:'main',cwd:source,packageRoot},f.ports);
  return {f,primary,source,record,start};
}

for(const kind of ['normal','linked','bare'])test(`2531: ${kind} source starts from verified Herdr parent and retains source/base`,async t=>{
  const {f,primary,source,record,start}=await linkedSourceFixture(t,kind);
  const before=f.git(source,'status','--porcelain=v1');const out=await start();assert.equal(out.exitCode,0,out.message);
  const run=record();assert.equal(run.sourceRoot,source);assert.notEqual(run.root,source);assert.equal(run.baseBranch,'main');
  assert.equal(f.herdr.panes.find(p=>p.workspace_id===run.chats[0].repoWorkspaceId).cwd,primary);
  assert.equal(f.git(source,'status','--porcelain=v1'),before);assert.equal(run.chats.length,1);
});

test('2531: confirmed pre-agent worktree refusal recovers the same run with open once',async t=>{
  const {f,source,record,start}=await linkedSourceFixture(t);f.refuseOnce=true;
  const first=await start();assert.equal(first.exitCode,1);assert.match(first.message,/linked_worktree_source/);
  const before=record(),worktrees=f.git(source,'worktree','list','--porcelain');
  assert.equal(before.chats.length,0);assert.equal(before.stageAgent,null);assert.equal(before.chatFailure.code,'linked_worktree_source');
  const out=await openRun({ref:'17',cwd:source,packageRoot},f.ports);assert.equal(out.exitCode,0,out.message);
  const after=record();assert.equal(after.runId,before.runId);assert.equal(after.root,before.root);assert.equal(after.branch,before.branch);
  assert.equal(f.git(source,'worktree','list','--porcelain'),worktrees);assert.equal(after.chats.length,1);assert.equal(after.chatFailure,undefined);
  assert.equal(f.herdr.panes.filter(p=>p.agent).length,1);
  assert.equal((await openRun({ref:'17',cwd:source,packageRoot},f.ports)).exitCode,0);assert.equal(record().chats.length,1);
  assert.equal(f.herdr.panes.filter(p=>p.agent).length,1);
});

test('2531: legacy linked-parent refusal and failed open recover without replacing Git allocation',async t=>{
  const {f,primary,source,record,start}=await linkedSourceFixture(t);f.refuseOnce=true;await start();
  const before=record(),path=join(f.state,'herdr-layout/registry.json'),registry=JSON.parse(readFileSync(path));
  const repo=registry.repositories[0],oldId=repo.workspaceId,row=f.herdr.workspaces.find(w=>w.workspace_id===oldId);
  // Saved shape from alpha after linked_worktree_source, then an unsuccessful open.
  repo.sourceRoot=source;delete repo.rootTabId;delete repo.rootPaneId;delete repo.rootTerminalId;
  row.worktree=null;f.herdr.panes.find(p=>p.workspace_id===oldId).cwd=source;
  registry.runs[0].phase='intent';delete registry.runs[0].refusal;
  writeFileSync(path,JSON.stringify(registry));
  before.chatFailure.code='herdr_layout_identity_changed';writeFileSync(join(before.runDir,'status.json'),JSON.stringify(before));
  const worktrees=f.git(source,'worktree','list','--porcelain');
  const out=await openRun({ref:'17',cwd:source,packageRoot},f.ports);assert.equal(out.exitCode,0,out.message);
  const after=record(),saved=JSON.parse(readFileSync(path));
  assert.equal(after.runId,before.runId);assert.equal(after.root,before.root);assert.equal(after.sourceRoot,source);assert.equal(after.branch,before.branch);
  assert.equal(f.git(source,'worktree','list','--porcelain'),worktrees);assert.equal(after.chats.length,1);
  assert.equal(saved.repositories[0].sourceRoot,primary);assert.equal(saved.archivedRepositories[0].workspaceId,oldId);
  assert.equal(f.herdr.panes.find(p=>p.workspace_id===oldId).cwd,source,'old shell remains untouched');
  assert(!f.herdr.calls.some(args=>args[0]==='workspace'&&['close','rename'].includes(args[1])));
});

test('2531: an uncertain retry reply cannot reuse an earlier confirmed refusal to launch again',async t=>{
  const {f,source,record,start}=await linkedSourceFixture(t);f.refuseOnce=true;await start();
  const healthy=f.ports.herdr;
  f.ports.herdr=async args=>{const reply=await healthy(args);if(args[0]==='worktree'&&args[1]==='open')throw closedChannel();return reply;};
  const out=await openRun({ref:'17',cwd:source,packageRoot},f.ports);assert.equal(out.exitCode,1);
  const before=record(),calls=f.herdr.calls.filter(args=>args[0]==='worktree').length;
  f.ports.herdr=healthy;
  const again=await openRun({ref:'17',cwd:source,packageRoot},f.ports);assert.equal(again.exitCode,1);assert.match(again.message,/layout_allocation_uncertain/);
  assert.equal(f.herdr.calls.filter(args=>args[0]==='worktree').length,calls);assert.equal(record().chats.length,0);
  assert.equal(record().root,before.root);assert.equal(f.herdr.panes.filter(p=>p.agent).length,0);
});

test('2531: recovery refuses a competing workspace at the assigned cwd and retains its identities',async t=>{
  const {f,source,record,start}=await linkedSourceFixture(t);f.refuseOnce=true;await start();const before=record();
  f.herdr.workspaces.push({workspace_id:'foreign',label:'person',worktree:{checkout_path:before.root,repo_key:before.commonDir,is_linked_worktree:true}});
  const out=await openRun({ref:'17',cwd:source,packageRoot},f.ports);assert.equal(out.exitCode,1);assert.match(out.message,/layout_allocation_uncertain/);
  assert.equal(record().chats.length,0);assert.equal(record().runId,before.runId);assert.equal(f.herdr.panes.filter(p=>p.agent).length,0);
});

test('2531: a refused run cannot change its saved common repository or issue/workflow binding',async t=>{
 for(const kind of ['common','label']){
  const {f,source,record,start}=await linkedSourceFixture(t);f.refuseOnce=true;await start();
  const run=record(),file=join(f.state,'herdr-layout/registry.json'),registry=JSON.parse(readFileSync(file));
  if(kind==='common')registry.runs[0].commonDir=join(f.base,'different.git');else registry.runs[0].label='other#99 feature';
  writeFileSync(file,JSON.stringify(registry));const calls=f.herdr.calls.filter(a=>a[0]==='worktree').length;
  const out=await openRun({ref:'17',cwd:source,packageRoot},f.ports);assert.equal(out.exitCode,1,out.message);
  assert.equal(f.herdr.calls.filter(a=>a[0]==='worktree').length,calls);assert.equal(record().runId,run.runId);assert.equal(record().chats.length,0);
 }
});

// #2530: a prose success cannot stand in for code replay evidence.
async function replayArea(t, { stopAtPrompt = false, extraVectorPath = null } = {}) {
  const f = await fixture(t, {name:'feature',agent:'codex'});
  const skill=join(f.source,'.agents/skills/pdd-feature');mkdirSync(skill,{recursive:true});
  writeFileSync(join(skill,'workflow.json'),JSON.stringify({version:2,areas:[
    {name:'story',steps:['scope'],optional:[],gate:'approve'},
    {name:'prompt-pr',steps:['check'],optional:[],gate:'pr',before:'approve',then:'ask-code'},
    {name:'code',steps:['verify'],optional:[],gate:'pr',replay_evidence:'pdd.replay-evidence.v1'}]}));
  assert.equal((await f.run()).exitCode,0);
  const run=f.record();mkdirSync(join(run.root,'tests'));
  const vector={schema_version:'prompt-runtime.program-scenario.v1',steps:[{step_id:'add',entry_path:'prompts/add.prompt.md',operation:'add',checks:[{criterion_id:'AC1',target:'result',path:'/total',op:'equals',value:3}]}]};
  writeFileSync(join(run.root,'tests/add.json'),JSON.stringify(vector));
  if (extraVectorPath) writeFileSync(join(run.root,extraVectorPath),JSON.stringify(vector));
  await stepDone({step:'scope',summary:'scoped',cwd:run.root},f.agentPorts());f.tick();
  assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  await stepDone({step:'check',summary:'Runtime check: ✓ 1 of 1 criteria',cwd:run.root},f.agentPorts());f.tick();
  if (stopAtPrompt) {
    assert.equal((await approveRun({ref:'17',cwd:f.source},{...f.ports,confirm:async question => /open PR 1/.test(question)})).exitCode,0);
    assert.equal(f.record().gate.kind,'ask-code');
    return {f,run,vector};
  }
  assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  assert.equal(f.record().areas[f.record().area].name,'code');
  return {f,run,vector};
}

test('2530: opted-in code publication marks missing structured evidence BLOCKED above prose pass',async t=>{
  const {f,run}=await replayArea(t);
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');
  const out=await stepDone({step:'verify',summary:'PASS: all tests and replay passed',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  assert.equal(f.prs.length,2,'a blocked evidence review can still publish');
  assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: BLOCKED/);
  assert.match(f.prs[1].body,/replay-evidence.json/);
  assert.match(f.prs[1].body,/validates structure and identity/);
  assert.ok(f.record().replayBaseline,'original vectors were anchored before code');
});

async function replayManifest(f,run,vector) {
  const {sourceFingerprint}=await import('../src/workflow-replay.mjs');
  const {createHash}=await import('node:crypto');
  const bytes=readFileSync(join(run.root,'tests/add.json'));
  const step=vector.steps[0],check=step.checks[0];
  return {schema_version:'pdd.replay-evidence.v1',run_id:run.runId,source:{kind:'git-content-v1',sha256:sourceFingerprint(run.root)},vectors:[{path:'tests/add.json',sha256:createHash('sha256').update(bytes).digest('hex')}],
    checks:[{vector:'tests/add.json',step_id:step.step_id,check_index:0,entry_path:step.entry_path,operation:step.operation,criterion_id:check.criterion_id,target:check.target,path:check.path,op:check.op,outcome:'pass'}],
    operations:[{vector:'tests/add.json',step_id:step.step_id,entry_path:step.entry_path,operation:step.operation,executed:true,outcome:'returned',boundary:{kind:'function',name:'add'},command:'node test/add.vectors.test.mjs',exit_code:0}],
    counts:{total:1,pass:1,fail:0,blocked:0,not_replayed:0},mutation:{kind:'semantic',description:'Return a wrong total',command:'node test/add.vectors.test.mjs --mutant',exit_code:1,outcome:'assertion_failure',failed_checks:[{vector:'tests/add.json',step_id:step.step_id,check_index:0}]},
    formal:{result:'not_applicable',scope:'Public wiring',reason:'No additional formal rule',control_outcome:'not_run'}};
}

test('2530: valid replay and real assertion failures both publish with canonical status',async t=>{
  for(const scenario of ['pass','fail-with-warning','fail']){
    const outcome=scenario==='pass'?'pass':'fail';
    const {f,run,vector}=await replayArea(t);writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
    if(scenario==='fail-with-warning')writeFileSync(join(run.runDir,'verify.md'),'✗ 1 vector still fails\n');
    const manifest=await replayManifest(f,run,vector);manifest.checks[0].outcome=outcome;manifest.counts.pass=outcome==='pass'?1:0;manifest.counts.fail=outcome==='fail'?1:0;
    writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(manifest));
    const out=await stepDone({step:'verify',summary:'tests ran',cwd:run.root},f.agentPorts());
    assert.equal(out.exitCode,0,out.message);assert.equal(f.prs.length,2);
    assert.match(f.prs[1].body,new RegExp(`Code replay: ${outcome.toUpperCase()}`));
    if(scenario==='fail')assert.match(f.prs[1].body,/^Old-code proof: not run\.\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\n✗ 1 replay assertions fail/);
    if(scenario==='fail-with-warning'){
      const inventory=f.prs[1].body.indexOf('Tests vs base:');
      const warning=f.prs[1].body.indexOf('✗ 1 vector still fails');
      const replay=f.prs[1].body.indexOf('Code replay: FAIL');
      assert.ok(f.prs[1].body.startsWith('Old-code proof: not run.\n')&&inventory>0&&warning>inventory&&warning<replay,
        'the evidence block stays first, then the test inventory, then the verify warning, then Code replay');
    }
  }
});

test('2530: vector edits after prompt-space approval cannot replace the saved original hashes',async t=>{
  const {f,run,vector}=await replayArea(t);const original=f.record().replayBaseline;
  vector.steps[0].checks[0].value=999;writeFileSync(join(run.root,'tests/add.json'),JSON.stringify(vector));
  writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
  const out=await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());assert.equal(out.exitCode,0,out.message);
  assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: BLOCKED/);assert.match(f.prs[1].body,/Original vectors changed/);
  assert.deepEqual(f.record().replayBaseline,original);
});

test('2530: an open code PR refreshes stale evidence and keeps its ownership marker',async t=>{
  const {f,run,vector}=await replayArea(t);writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
  await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: PASS/);
  writeFileSync(join(run.root,'value.mjs'),'export const value=3;\n');
  const out=await stepDone({step:'verify',summary:'PASS again',cwd:run.root},f.agentPorts());assert.equal(out.exitCode,0,out.message);
  assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: BLOCKED/);assert.match(f.prs[1].body,/stale/);
  assert.ok(f.prs[1].body.includes(`<!-- pdd-workflow:${run.runId}:code -->`));
  assert.equal(f.edits.filter(n=>n===f.prs[1].number).length,2);
});

test('2530: failed description downgrade prevents pushing new source with an old pass',async t=>{
  const {f,run,vector}=await replayArea(t);writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
  await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());const pushes=f.pushes.length;
  writeFileSync(join(run.root,'value.mjs'),'export const value=3;\n');
  const original=f.ports.execFile;f.ports.execFile=async(file,args,options)=>file==='gh'&&args[0]==='pr'&&args[1]==='edit'?{stdout:'',stderr:'description permission denied',code:1}:original(file,args,options);
  const out=await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,1);assert.match(out.message,/description permission denied/);
  assert.equal(f.pushes.length,pushes);assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: PASS/,'unchanged remote source still has its valid report');
});

test('2530: failed final description update leaves a pushed code PR publication-pending',async t=>{
  const {f,run,vector}=await replayArea(t);writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
  await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());
  writeFileSync(join(run.root,'value.mjs'),'export const value=3;\n');
  writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
  const original=f.ports.execFile;let edits=0;
  f.ports.execFile=async(file,args,options)=>{if(file==='gh'&&args[0]==='pr'&&args[1]==='edit'&&++edits===2)return {stdout:'',stderr:'final update rejected',code:1};return original(file,args,options);};
  const out=await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,1);assert.match(out.message,/Source was pushed/);assert.match(f.prs[1].body,/Code replay: BLOCKED.*Publication pending/);
});

test('2530: a failed push leaves an existing code PR pending and never restores pass',async t=>{
  for(const structured of [false,true]){
    const {f,run,vector}=await replayArea(t);writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
    writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
    await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());
    writeFileSync(join(run.root,'value.mjs'),'export const value=3;\n');
    writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
    const original=f.ports.execFile;
    f.ports.execFile=async(file,args,options)=>{
      if(file==='git'&&args[0]==='push'){
        if(structured)return {stdout:'',stderr:'push rejected',code:1};
        throw Object.assign(Error('push rejected'),{stderr:'push rejected',code:1});
      }
      return original(file,args,options);
    };
    const out=await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());
    assert.equal(out.exitCode,1,out.message);assert.match(out.message,/push rejected/);
    assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: BLOCKED.*Publication pending/);
  }
});

test('2530: an unopted saved area retains legacy publication without a manifest',async t=>{
  const {f,run}=await replayArea(t);const saved=f.record();delete saved.areas.find(a=>a.name==='code').replay_evidence;
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(saved));
  writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  const out=await stepDone({step:'verify',summary:'tests ran',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);assert.equal(f.prs.length,2);assert.doesNotMatch(f.prs[1].body,/Code replay:/);
});


for (const revision of ['changed', 'added']) {
  test(`2553: ${revision} scenario repins on subsequent prompt publication`, async t => {
    const {f,run,vector} = await replayArea(t,{stopAtPrompt:true});
    const original = f.record().replayBaseline;
    assert.deepEqual(original.vectors.map(v=>v.path),['tests/add.json']);
    const path = revision === 'added' ? 'tests/refund.json' : 'tests/add.json';
    vector.steps[0].checks[0].value = 7;
    writeFileSync(join(run.root,path),JSON.stringify(vector));
    f.tick();
    assert.equal((await stepDone({step:'check',summary:'Reviewed revised scenarios',cwd:run.root},f.agentPorts())).exitCode,0);
    assert.equal(f.prs.length,1,'the existing prompt PR is updated');
    const baseline = f.record().replayBaseline;
    if (revision === 'added') assert.deepEqual(baseline.vectors.map(v=>v.path).sort(),['tests/add.json','tests/refund.json']);
    else assert.notEqual(baseline.vectors[0].sha256,original.vectors[0].sha256);
    const {createHash} = await import('node:crypto');
    assert.equal(baseline.vectors.find(v=>v.path===path).sha256,createHash('sha256').update(readFileSync(join(run.root,path))).digest('hex'));
  });
}

test('2553: legacy single-vector baseline cannot publish PASS after another scenario is added', async t => {
  const {f,run,vector} = await replayArea(t);
  const original = f.record().replayBaseline;
  assert.deepEqual(original.vectors.map(v=>v.path),['tests/add.json']);
  writeFileSync(join(run.root,'tests/refund.json'),JSON.stringify(vector));
  writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  // Construct after the addition: its current fingerprint covers both files; inventory is the defect.
  const manifest = await replayManifest(f,run,vector);
  const {sourceFingerprint} = await import('../src/workflow-replay.mjs');
  assert.equal(manifest.source.sha256,sourceFingerprint(run.root));
  assert.deepEqual(manifest.vectors.map(v=>v.path),['tests/add.json']);
  writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(manifest));
  const out = await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  assert.equal(f.prs.length,2);
  assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: BLOCKED/);
  assert.doesNotMatch(f.prs[1].body,/Replay evidence is stale/);
  assert.deepEqual(f.record().replayBaseline,original,'code publication cannot repin saved originals');
});

test('2553: non-ASCII scenario filename survives prompt publication discovery', async t => {
  const {f} = await replayArea(t,{stopAtPrompt:true,extraVectorPath:'tests/café.json'});
  assert.deepEqual(f.record().replayBaseline.vectors.map(v=>v.path).sort(),['tests/add.json','tests/café.json']);
});

for (const revision of ['added','changed']) {
  test(`2553: final committed ${revision} scenario approval push refreshes the frozen anchor`, async t => {
    const {f,run,vector}=await replayArea(t,{stopAtPrompt:true});
    const original=f.record().replayBaseline;
    const path=revision==='added'?'tests/refund.json':'tests/add.json';
    vector.steps[0].checks[0].value=8;
    writeFileSync(join(run.root,path),JSON.stringify(vector));
    f.git(run.root,'add','--',path);f.git(run.root,'commit','-qm','Reviewed scenario');
    const result=await approveRun({ref:'17',cwd:f.source},f.ports);
    assert.equal(result.exitCode,0,result.message);
    assert.equal(f.record().areas[f.record().area].name,'code');
    const {createHash}=await import('node:crypto');
    const saved=f.record().replayBaseline;
    assert.equal(saved.vectors.find(v=>v.path===path).sha256,createHash('sha256').update(readFileSync(join(run.root,path))).digest('hex'));
    assert.notDeepEqual(saved,original);
  });
}

test('2553: dirty unpublished scenario edits refuse final code entry',async t=>{
  const {f,run,vector}=await replayArea(t,{stopAtPrompt:true});
  const original=f.record().replayBaseline,pushes=f.pushes.length;
  vector.steps[0].checks[0].value=99;writeFileSync(join(run.root,'tests/add.json'),JSON.stringify(vector));
  const result=await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(result.exitCode,1);assert.match(result.message,/Unpublished scenario edits.*tests\/add.json/);
  assert.equal(f.record().gate.kind,'ask-code');assert.equal(f.pushes.length,pushes);
  assert.deepEqual(f.record().replayBaseline,original);
});

test('2553: exact whitespace paths survive anchoring and code inventory checks',async t=>{
  const path='tests/ café \n.json';
  const {f,run}=await replayArea(t,{stopAtPrompt:true,extraVectorPath:path});
  assert.ok(f.record().replayBaseline.vectors.some(v=>v.path===path));
  assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  const saved=f.record();saved.replayBaseline.vectors=saved.replayBaseline.vectors.filter(v=>v.path!==path);
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(saved));
  const result=await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());
  assert.equal(result.exitCode,0,result.message);assert.match(f.record().replayEvidence.reason,/missing from the approved anchor/);
});

for(const failure of ['listing','missing','malformed']) {
  test(`2553: ${failure} current inventory cannot publish subset PASS`,async t=>{
    const {f,run,vector}=await replayArea(t);
    writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
    writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
    const original=f.ports.execFile;
    if(failure==='malformed')writeFileSync(join(run.root,'tests/broken.json'),'{"schema_version":');
    if(failure==='missing')f.ports.execFile=async(file,args,options)=>{
      const reply=await original(file,args,options);
      return file==='git'&&args[0]==='diff'&&args.includes('-z')?{...reply,stdout:reply.stdout+'tests/missing.json\0'}:reply;
    };
    if(failure==='listing')f.ports.execFile=async(file,args,options)=>file==='git'&&args[0]==='diff'&&args.includes('-z')?{stdout:'',code:1,stderr:'inventory unavailable'}:original(file,args,options);
    const manifest=JSON.parse(readFileSync(join(run.runDir,'replay-evidence.json'),'utf8'));
    const {sourceFingerprint}=await import('../src/workflow-replay.mjs');
    manifest.source.sha256=sourceFingerprint(run.root);
    assert.ok(manifest.source.sha256);
    writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(manifest));
    const result=await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());
    assert.equal(result.exitCode,0,result.message);assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: BLOCKED/);
    assert.match(f.record().replayEvidence.reason,/inventory is unavailable/);
    assert.match(result.message,/Code replay: BLOCKED/);
  });
}

test('2553: irrelevant JSON mentioning the schema never becomes a scenario',async t=>{
  const {f,run}=await replayArea(t,{stopAtPrompt:true});
  writeFileSync(join(run.root,'tests/notes.json'),JSON.stringify({description:'prompt-runtime.program-scenario.v1',schema_version:'other.v1'}));
  const result=await stepDone({step:'check',summary:'reviewed',cwd:run.root},f.agentPorts());
  assert.equal(result.exitCode,0,result.message);
  assert.deepEqual(f.record().replayBaseline.vectors.map(v=>v.path),['tests/add.json']);
});

test('2553: an open code PR update guards newly added scenarios and preserves the frozen anchor',async t=>{
  const {f,run,vector}=await replayArea(t);const saved=f.record().replayBaseline;
  writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');
  writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
  assert.equal((await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts())).exitCode,0);
  assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: PASS/);
  writeFileSync(join(run.root,'tests/refund.json'),JSON.stringify(vector));
  writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(await replayManifest(f,run,vector)));
  const result=await stepDone({step:'verify',summary:'PASS',cwd:run.root},f.agentPorts());
  assert.equal(result.exitCode,0,result.message);assert.match(f.prs[1].body,/^Old-code proof: [^\n]+\nTests vs base:[\s\S]*?Test inventory commits: [^\n]+\nCode replay: BLOCKED.*refund\.json/);
  assert.deepEqual(f.record().replayBaseline,saved);assert.equal(f.edits.filter(n=>n===f.prs[1].number).length,2);
});

test('2553: a clean final prompt head already published externally refreshes before code entry',async t=>{
  const {f,run,vector}=await replayArea(t,{stopAtPrompt:true});
  writeFileSync(join(run.root,'tests/refund.json'),JSON.stringify(vector));
  f.git(run.root,'add','.');f.git(run.root,'commit','-qm','Publish reviewed scenario');
  f.git(run.root,'update-ref',`refs/remotes/origin/${f.record().branch}`,f.git(run.root,'rev-parse','HEAD'));
  const pushes=f.pushes.length;
  const result=await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(result.exitCode,0,result.message);assert.equal(f.pushes.length,pushes);
  assert.deepEqual(f.record().replayBaseline.vectors.map(v=>v.path).sort(),['tests/add.json','tests/refund.json']);
});

test('2553: final code entry refuses a prompt branch behind its published head',async t=>{
  const {f,run,vector}=await replayArea(t,{stopAtPrompt:true});const saved=f.record().replayBaseline;
  const head=f.git(run.root,'rev-parse','HEAD');
  writeFileSync(join(run.root,'tests/refund.json'),JSON.stringify(vector));
  f.git(run.root,'add','.');f.git(run.root,'commit','-qm','Published scenario');
  f.git(run.root,'update-ref',`refs/remotes/origin/${f.record().branch}`,f.git(run.root,'rev-parse','HEAD'));
  f.git(run.root,'reset','--hard',head);
  const result=await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(result.exitCode,1);assert.match(result.message,/behind its published head/);
  assert.equal(f.record().gate.kind,'ask-code');assert.deepEqual(f.record().replayBaseline,saved);
});

test('2553: merged prompt branch retains its published anchor on final code entry',async t=>{
  const {f,run}=await replayArea(t,{stopAtPrompt:true});const saved=f.record().replayBaseline;
  f.mergedNumbers.push(f.prs[0].number);
  const result=await approveRun({ref:'17',cwd:f.source},f.ports);
  assert.equal(result.exitCode,0,result.message);assert.equal(f.record().areas[f.record().area].name,'code');
  assert.deepEqual(f.record().replayBaseline,saved);
});


test('product association: start saves one issue marker and both producer PRs preserve it independently of branch identity', async t => {
  const marker = '<!-- pdd-product: run=phone-1 -->';
  const { f, run, done } = await featureToPr1(t, undefined, undefined, `Planned handoff.\n${marker}\n${marker}`);
  assert.equal(f.record().productMarker, marker);
  f.tick(); assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n'); f.git(run.root,'commit','-qam','code');
  await done('build','value is two'); await done('verify','tests pass');
  assert.equal(f.prs.length,2);
  for (const pr of f.prs) {
    assert.equal(pr.body.split('\n').filter(line=>line===marker).length,1);
    assert.equal((pr.body.match(/<!-- pdd-workflow:/g)??[]).length,1);
    assert.ok(pr.body.includes(`<!-- pdd-workflow:${run.runId}:`));
  }
});

test('product association: conflicting markers warn and ordinary issues keep the legacy record shape', async t => {
  for (const body of ['Ordinary issue.', 'Inline <!-- pdd-product: run=one --> and <!-- pdd-product: run=two -->']) {
    const f = await fixture(t,{name:'feature',agent:'codex'}); f.issueBody=body;
    const result=await f.run(); assert.equal(result.exitCode,0,result.message);
    assert.equal(Object.hasOwn(f.record(),'productMarker'),false);
    if(body.includes('pdd-product')) assert.match(f.record().warnings.join(' '),/multiple.*marker/i);
  }
});
