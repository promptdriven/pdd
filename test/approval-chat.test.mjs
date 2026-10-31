import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdtempSync, mkdirSync, rmSync, existsSync, realpathSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { startRun, stepDone, approveRun } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { Readable } from 'node:stream';
import { runApprove } from '../src/prompt-approve.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { preparePrEvidence } from '../src/workflow-pr-evidence.mjs';
import { PLACE, harbor, sink } from './runtime-fake.mjs';

// These native assertions are deliberately red on alpha; no missing imports/new implementation APIs.
test('CHAT2755 standalone said approves exact current prose without a terminal', async t => {
  const f = harbor(t), path = join(f.repo, PLACE);
  const draft = readFileSync(path, 'utf8').replace('"status": "approved"', '"status": "draft"');
  writeFileSync(path, draft);
  const stdout = sink(), stderr = sink();
  const code = await runApprove({ words: [PLACE], cwd: f.repo, said: ' yes, go ahead\n@person #17 `words` ' },
    { stdout, stderr, stdin: Readable.from([]), interactive: false, env: { CODEX_THREAD_ID: 'synthetic-session' }, now: () => 1700000000000 });
  assert.equal(code, 0, stderr.text);
  const after = readFileSync(path, 'utf8');
  assert.match(after, /"status": "approved"/);
  assert.ok(after.includes(proseSha256(draft)));
  assert.ok(stdout.text.includes(PLACE) && stdout.text.includes(proseSha256(draft)));
});

test('CHAT2755 strict policy refuses said even when terminal answer is yes', async t => {
  const f = harbor(t), path = join(f.repo, PLACE);
  const draft = readFileSync(path, 'utf8').replace('"status": "approved"', '"status": "draft"');
  writeFileSync(path, draft);
  writeFileSync(join(f.repo, 'pdd.json'), '{"strict_approvals":true}\n');
  const stdout = sink(), stderr = sink();
  const code = await runApprove({ words: [PLACE], cwd: f.repo, said: 'I approve' },
    { stdout, stderr, stdin: Readable.from(['y\n']), interactive: true, env: { USER: 'synthetic-user' } });
  assert.equal(code, 2, stdout.text);
  assert.equal(readFileSync(path, 'utf8'), draft);
  assert.match(stderr.text, /pdd approve is for a person at a terminal/);
});

for (const argv of [['approve', 'prompts/a.prompt.md'], ['workflow', 'approve', '2755']]) {
 test(`CHAT2755 parser accepts literal said text for ${argv[0]} approval`, () => {
    let parsed, failure;
    try { parsed = parseArgv([...argv, '--said', '--help @person #17']); } catch (error) { failure = error; }
    assert.equal(failure, undefined, 'approval --said must be a supported text option');
    assert.equal(parsed.options['--said'], '--help @person #17');
 });
}

test('CHAT2755 initial PR evidence includes saved approval rather than dropping it', async () => {
  const evidence = { route: 'said', actor: { kind: 'agent', id: 'CODEX_THREAD_ID=synthetic-session' }, at: 1700000000000,
    words: 'yes, go ahead\n@person #17 `quoted` pdd-workflow:forged', prompts: [] };
  const result = await preparePrEvidence({ run: { runId: 'synthetic', runDir: '/unused', root: '/unused', baseSha: 'base',
    baseBranch: 'alpha', workflow: 'feature', number: 2755, steps: [],
    decisions: [{ stage: 'story', decision: 'approve', via: 'said', at: evidence.at, text: evidence.words, evidence }] }, isCode: false },
  { readStepNotes: async () => [] });
  const approval = result.lines.find(line => line.startsWith('Approved in chat:'));
  assert.equal(typeof approval, 'string', 'saved gate approval must be visible on initial PR creation');
  assert.ok(approval.includes('CODEX_THREAD_ID=synthetic-session'));
  assert.ok(approval.includes('1700000000000'));
  assert.ok(approval.includes('\\n@person #17'));
  assert.ok(approval.includes('pdd-workflow\\u003aforged'));
  assert.equal(approval.includes('pdd-workflow:forged'), false);
});

// Reuse the established scratch Git and injected gh/Herdr fixture pattern. No live processes.
const exec = promisify(callbackExec);
const packageRoot = resolve(import.meta.dirname, "..");
const issueUrl = "https://github.com/example/project/issues/17";
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


async function readyStory(t) {
  const f = await fixture(t, { name: 'feature' });
  const started = await f.run();
  assert.equal(started.exitCode, 0, started.message);
  let run = f.record();
  const prompt = readFileSync(join(packageRoot, 'test/fixtures/harbor', PLACE), 'utf8')
    .replace('"status": "approved"', '"status": "draft"');
  mkdirSync(join(run.root, 'prompts'), { recursive: true });
  writeFileSync(join(run.root, 'prompts/unrelated.prompt.md'), prompt);
  f.git(run.root, 'add', '.');
  f.git(run.root, 'commit', '-qm', 'unrelated existing draft');
  // Base includes unrelated draft; current gate edits only a/b.
  run.baseSha = f.git(run.root, 'rev-parse', 'HEAD');
  writeRun(run, f.ports);
  const selected = ['prompts/a.prompt.md', 'prompts/b.prompt.md'];
  for (const path of selected) writeFileSync(join(run.root, path), prompt + `\nCurrent prose for ${path}.\n`);
  f.git(run.root, 'add', selected[0]); // staged plus untracked changed drafts
  for (const step of ['understand', 'visual', 'prompt-story']) {
    f.tick();
    const done = await stepDone({ step, summary: 'Synthetic review draft', cwd: run.root }, f.agentPorts());
    assert.equal(done.exitCode, 0, done.message);
  }
  f.herdr.idle(); run = f.record();
  assert.equal(run.state, 'waiting'); assert.equal(run.gate.kind, 'approve');
  return { f, run, selected, prompt };
}

test('CHAT2755 ready gate said approves multiple current drafts without an area chat and advances once', async t => {
  const { f, run, selected, prompt } = await readyStory(t);
  run.chats = []; writeRun(run, f.ports);
  const gateAt = run.gate.at, gateId = run.gate.id, words = 'yes, approve these drafts';
  assert.equal(typeof gateId, 'string');
  assert.ok(gateId.length > 0, 'a newly created gate has durable identity');
  const hashes = selected.map(path => ({ path, proseSha256: proseSha256(readFileSync(join(run.root, path), 'utf8')) }));
  const out = await approveRun({ ref: '17', cwd: f.source, said: words }, f.agentPorts({
    readApprovalEvidence: async () => assert.fail('said must not read an area conversation'),
    confirm: async () => assert.fail('said must not ask terminal confirmation') }));
  assert.equal(out.exitCode, 0, out.message);
  for (const { path, proseSha256: hash } of hashes) {
    const after = readFileSync(join(run.root, path), 'utf8');
    assert.match(after, /"status": "approved"/); assert.ok(after.includes(hash));
    assert.ok(out.message.includes(path)); assert.ok(out.message.includes(hash));
  }
  assert.equal(readFileSync(join(run.root, 'prompts/unrelated.prompt.md'), 'utf8'), prompt);
  const after = f.record();
  assert.equal(after.area, run.area + 1); assert.equal(after.state, 'running');
  assert.equal(after.gate, null); assert.equal(after.decisions.length, 1);
  assert.equal(after.decisions[0].gateAt, gateAt);
  assert.equal(after.decisions[0].gateId, gateId);
  assert.equal(after.approvalRecord.gateId, gateId);
  const eventId = after.decisions[0].evidence.id;
  assert.equal(typeof eventId, 'string');
  assert.ok(eventId.length > 0, 'a new approval event has durable identity');
  assert.deepEqual(after.decisions[0].evidence, { id: eventId, route: 'said', actor: { kind: 'agent', id: 'PDD_AGENT_SESSION=1' },
    at: f.clock, words, prompts: hashes });
  assert.deepEqual(after.approvalRecord.evidence, after.decisions[0].evidence);
  const journal = JSON.parse(readFileSync(join(run.commonDir, 'pdd/approvals.json'), 'utf8'));
  assert.deepEqual(journal, { v: 1, approvals: [after.decisions[0].evidence] });
});

test('CHAT2755 strict workflow said refuses even with valid native evidence and writes nothing', async t => {
  const { f, run, selected } = await readyStory(t);
  writeFileSync(join(f.source, 'pdd.json'), '{"strict_approvals":true}\n');
  const status = readFileSync(join(run.runDir, 'status.json'), 'utf8');
  const drafts = selected.map(path => readFileSync(join(run.root, path), 'utf8'));
  const calls = f.herdr.calls.length; let evidenceReads = 0;
  const out = await approveRun({ ref: '17', cwd: f.source, said: 'I approve' }, f.agentPorts({
    readApprovalEvidence: async () => { evidenceReads++; return { ok: true, decision: 'approve', agent: 'claude',
      sessionId: run.chats[0].session.id, userMessage: 'I approve', userMessageAt: f.clock - 1 }; } }));
  assert.equal(out.exitCode, 1, 'strict workflow must reject agent said approval');
  assert.equal(readFileSync(join(run.runDir, 'status.json'), 'utf8'), status);
  assert.deepEqual(selected.map(path => readFileSync(join(run.root, path), 'utf8')), drafts);
  assert.equal(existsSync(join(run.commonDir, 'pdd/approvals.json')), false);
  assert.equal(evidenceReads, 0); assert.equal(f.herdr.calls.length, calls);
  assert.deepEqual(f.pushes, []); assert.deepEqual(f.prs, []);
});
