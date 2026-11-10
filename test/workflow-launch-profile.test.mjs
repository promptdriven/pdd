// Synthetic accounts and the repository's fake Herdr. No native agent or login calls.
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, readFileSync, writeFileSync, renameSync} from 'node:fs';
import {join} from 'node:path';
import {startRun, openRun, runStatus, changeRun, stepDone, approveRun} from '../src/workflow-runner.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const calls = f => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');
const quote = value => `'${value.replace(/'/g, `'\\''`)}'`;
const start = (f, options = {}) => startRun({name:'small-change', issue:'17', agent:'codex', cwd:f.source, packageRoot, ...options}, f.ports);
const open = (f, options = {}, ports = f.ports) => openRun({ref:'17', cwd:f.source, packageRoot, ...options}, ports);
const status = (f, json = true) => runStatus({ref:'17', cwd:f.source, json}, f.ports);
const folder = (f, name) => {const path = join(f.base, name); mkdirSync(path, {recursive:true}); return path;};
const bytes = f => readFileSync(join(f.record().runDir, 'status.json'));
const preserved = run => Object.fromEntries(['runId','root','branch','done','gate','question','decisions','approvalRecord','pr'].map(key => [key,run[key]]));
function commandProfile(command, {model, threads}) {
  if (model) assert.ok(command.includes(`--model ${quote(model)}`), 'Launch must pin the requested model');
  else assert.doesNotMatch(command, /--model/);
  if (threads) assert.ok(command.includes(`features.multi_agent_v2.max_concurrent_threads_per_session=${threads}`), 'Launch must pin the effective thread limit');
  else assert.doesNotMatch(command, /max_concurrent_threads_per_session/);
  assert.match(command, /dangerously-(?:bypass-approvals-and-sandbox|skip-permissions)/);
}
async function advance(f) {
  f.tick(); // Separate later-area discovery from the prior native session.
  assert.equal((await stepDone({step:'scope', summary:'Synthetic completed scope', cwd:f.record().root}, f.agentPorts())).exitCode, 0);
  // This is the fixture's fake person gate, not a prompt approval in this checkout.
  const result = await approveRun({ref:'17', cwd:f.source}, f.ports);
  assert.equal(result.exitCode, 0, result.message);
}

for (const agent of ['codex','claude']) test(`Theme D ${agent}: start, focus, resume, changes, fresh account and later area keep one profile`, async t => {
  const f = await fixture(t, {agent});
  const variable = agent === 'codex' ? 'CODEX_HOME' : 'CLAUDE_CONFIG_DIR';
  const first = folder(f, 'account-one'), second = folder(f, "account two's folder"), third = folder(f, 'unselected-account');
  f.ports.env[variable] = first;
  const settings = {agent, model:'synthetic-model-a', herdrAgentName:`theme-${agent}`, ...(agent === 'codex' ? {codexThreads:'5'} : {})};
  const result = await start(f, settings); assert.equal(result.exitCode, 0, result.message);
  const initial = f.record(), chat = initial.chats.at(-1);
  assert.equal(initial.launchProfile?.model, settings.model, 'The run must save its selected model');
  assert.equal(initial.launchProfile.configDir, first);
  assert.deepEqual(chat.launchProfile, initial.launchProfile);
  assert.match(chat.herdrAgentName, new RegExp(`^theme-${agent}-[0-9a-f]{6}$`));
  assert.equal((await f.ports.herdr(['agent','get',chat.herdrAgentName])).result.agent.pane_id, chat.paneId);
  commandProfile(calls(f).at(-1)[3], {model:settings.model, threads:agent === 'codex' ? 5 : null});
  const shown = JSON.parse((await status(f)).message).runs[0];
  assert.deepEqual(shown.launchProfile, initial.launchProfile);
  assert.deepEqual(shown.chat, {herdrAgentName:chat.herdrAgentName, paneId:chat.paneId});
  assert.ok((await status(f, false)).message.includes(settings.model));
  f.ports.env[variable] = second;
  f.herdr.calls.length = 0;
  assert.equal((await open(f)).exitCode, 0);
  assert.equal(calls(f).length, 0, 'Focus must not launch another chat');
  // A real observed agent has ended, so the ordinary open can resume its own session.
  f.herdr.paneOf(chat).agent = null;
  const resumed = await open(f); assert.equal(resumed.exitCode, 0, resumed.message);
  assert.ok(calls(f).at(-1)[3].includes(`${variable}=${quote(first)}`));
  assert.match(calls(f).at(-1)[3], /\bresume\b/);
  commandProfile(calls(f).at(-1)[3], {model:settings.model, threads:agent === 'codex' ? 5 : null});
  f.herdr.idle();
  const changed = await changeRun({ref:'17', text:'Keep the selected launch settings', cwd:f.source}, f.ports);
  assert.equal(changed.exitCode, 0, changed.message);
  assert.equal(f.record().launchProfile.configDir, first, 'Changes from another account must not select it');
  const before = preserved(f.record()), originalSession = f.record().chats.at(-1).session?.id;
  f.herdr.calls.length = 0;
  f.tick(); // Fresh native sessions have their own discovery window.
  const replaced = await open(f, {newSession:true, model:'synthetic-model-b', herdrAgentName:`next-${agent}`, ...(agent === 'codex' ? {codexThreads:'6'} : {})});
  assert.equal(replaced.exitCode, 0, replaced.message);
  const selected = f.record(), replacement = selected.chats.at(-1);
  assert.deepEqual(preserved(selected), before);
  assert.equal(selected.launchProfile.configDir, second);
  assert.equal(selected.launchProfile.model, 'synthetic-model-b');
  assert.deepEqual(selected.chatReplacement.launchProfile, selected.launchProfile);
  assert.deepEqual(replacement.launchProfile, selected.launchProfile);
  assert.ok(calls(f)[0][3].includes(`${variable}=${quote(second)}`));
  assert.doesNotMatch(calls(f)[0][3], /\bresume\b/);
  if (agent === 'claude') assert.notEqual(replacement.session.id, originalSession, 'Account changes start a fresh native session');
  commandProfile(calls(f)[0][3], {model:'synthetic-model-b', threads:agent === 'codex' ? 6 : null});
  f.ports.env[variable] = third;
  await advance(f);
  const later = f.record().chats.at(-1);
  assert.equal(later.area, 'build');
  assert.deepEqual(later.launchProfile, selected.launchProfile);
  assert.notEqual(later.herdrAgentName, replacement.herdrAgentName, 'Peer areas must have distinct names');
  commandProfile(calls(f).at(-1)[3], {model:'synthetic-model-b', threads:agent === 'codex' ? 6 : null});
  // Historical resume retains that chat's snapshot, even after the run profile changed.
  f.herdr.paneOf(replacement).agent = null;
  const historical = await open(f, {area:'plan'}); assert.equal(historical.exitCode, 0, historical.message);
  assert.ok(calls(f).at(-1)[3].includes(`${variable}=${quote(second)}`));
});

test('Theme D account-only switch retains the selected model and a higher account thread limit', async t => {
  const f = await fixture(t, {agent:'codex'}), first = folder(f,'first'), second = folder(f,'second');
  f.ports.env.CODEX_HOME = first;
  writeFileSync(join(first,'config.toml'), '[features.multi_agent_v2]\nmax_concurrent_threads_per_session = 11\nmodel = "unrelated"\n');
  const before = readFileSync(join(first,'config.toml'));
  assert.equal((await start(f, {model:'fixed-model', codexThreads:'5'})).exitCode, 0);
  assert.equal(f.record().launchProfile?.codexThreads, 11, 'A higher personal limit must survive selection');
  f.ports.env.CODEX_HOME = second;
  assert.equal((await open(f, {newSession:true})).exitCode, 0);
  commandProfile(calls(f).at(-1)[3], {model:'fixed-model', threads:11});
  assert.deepEqual(readFileSync(join(first,'config.toml')), before, 'Invocation options must not edit personal config');
});

test('Theme D closed workspace recovery resumes the saved snapshot despite another caller account', async t => {
  const f = await fixture(t, {agent:'codex'});
  f.ports.env.CODEX_HOME = folder(f,'saved');
  assert.equal((await start(f, {model:'fixed-model', codexThreads:'5'})).exitCode, 0);
  const before = f.record(), chat = before.chats.at(-1);
  // Observe the native session before closing its layout, as real status does.
  assert.equal((await status(f)).exitCode, 0);
  await f.ports.herdr(['workspace','close',chat.workspaceId]);
  f.ports.env.CODEX_HOME = folder(f,'caller'); f.herdr.calls.length = 0;
  const result = await open(f); assert.equal(result.exitCode, 0, result.message);
  commandProfile(calls(f)[0][3], {model:'fixed-model', threads:5});
  assert.ok(calls(f)[0][3].includes(`CODEX_HOME=${quote(before.configDir)}`));
  assert.match(calls(f)[0][3], /\bresume\b/);
  assert.deepEqual(f.record().launchProfile, before.launchProfile);
});

for (const phase of ['intent','prepared','launchRequested']) test(`Theme D interrupted ${phase} pins the entire profile across retries`, async t => {
  const f = await fixture(t, {agent:'codex'});
  f.ports.env.CODEX_HOME = folder(f,'first');
  assert.equal((await start(f, {model:'original-model', codexThreads:'5'})).exitCode, 0);
  f.ports.env.CODEX_HOME = folder(f,'chosen');
  let fired = false;
  const ports = {...f.ports, runFiles: {renameSync(from,to) {
    renameSync(from,to);
    if (!fired && to === join(f.record().runDir,'status.json') && JSON.parse(readFileSync(to,'utf8')).chatReplacement?.phase === phase) {
      fired = true; throw Error('Synthetic interrupted checkpoint');
    }
  }}};
  const result = await open(f, {newSession:true, model:'chosen-model', herdrAgentName:'chosen-name', codexThreads:'6'}, ports);
  assert.equal(result.exitCode, 1);
  const pending = f.record().chatReplacement;
  assert.equal(pending.launchProfile?.model, 'chosen-model', 'Intent must pin all launch settings');
  f.ports.env.CODEX_HOME = folder(f,'retry-account'); f.herdr.calls.length = 0;
  if (phase === 'launchRequested') {
    f.tick(31_000);
    f.ports.findNativeSessions = async () => [];
    const healthy = f.ports.herdr;
    f.ports.herdr = async args => args[0] === 'pane' && args[1] === 'process-info'
      ? {result:{type:'pane_process_info',process_info:{pane_id:args[3],shell_pid:91,foreground_process_group_id:91,foreground_processes:[{pid:91,name:'bash'}]}}}
      : healthy(args);
  }
  const retried = await open(f, {newSession:true, model:'ignored-model', codexThreads:'8', herdrAgentName:'ignored-name'});
  assert.equal(retried.exitCode, 0, retried.message);
  const after = f.record();
  assert.deepEqual(after.chatReplacement.launchProfile, pending.launchProfile);
  if (phase === 'intent') {
    assert.equal(after.chatReplacement.phase, 'rolledBack');
    assert.equal(after.launchProfile.model, 'original-model');
    assert.equal(calls(f).length, 0);
  } else {
    assert.deepEqual(after.launchProfile, pending.launchProfile);
    assert.equal(calls(f).length, 1);
    commandProfile(calls(f)[0][3], {model:'chosen-model', threads:6});
    assert.ok(calls(f)[0][3].includes(`CODEX_HOME=${quote(pending.configDir)}`));
  }
});

for (const options of [{model:' '},{model:'-bad'},{model:'bad\nmodel'},{herdrAgentName:'Bad Name'},{herdrAgentName:'a'.repeat(26)},{codexThreads:'3'},{codexThreads:'9'},{codexThreads:'5.5'}]) test(`Theme D invalid option ${JSON.stringify(options)} refuses before effects`, async t => {
  const f = await fixture(t, {agent:'codex'});
  f.ports.env.CODEX_HOME = folder(f,'selected');
  const refused = await start(f, options);
  assert.equal(refused.exitCode, 1, 'Invalid launch option must refuse');
  assert.equal(f.herdr.calls.length, 0);
  assert.equal(f.fetches, 0);
  assert.equal((await start(f)).exitCode, 0);
  const before = bytes(f); f.herdr.calls.length = 0;
  assert.equal((await open(f, {newSession:true, ...options})).exitCode, 1);
  assert.deepEqual(bytes(f), before);
  assert.equal(f.herdr.calls.length, 0);
});

for (const config of ['[broken', '[features.multi_agent_v2]\nmax_concurrent_threads_per_session = 0\n']) test('Theme D bad account config refuses before an account change closes the chat', async t => {
  const f = await fixture(t, {agent:'codex'});
  assert.equal((await start(f, {codexThreads:'5'})).exitCode, 0);
  const selected = folder(f,'bad-config'); writeFileSync(join(selected,'config.toml'),config);
  f.ports.env.CODEX_HOME = selected;
  const before = bytes(f); f.herdr.calls.length = 0;
  assert.equal((await open(f, {newSession:true})).exitCode, 1, 'Invalid selected thread configuration must refuse');
  assert.deepEqual(bytes(f), before);
  assert.equal(f.herdr.calls.length, 0);
});

test('Theme D profile edits require a fresh current chat and preserve caller refusal', async t => {
  const f = await fixture(t, {agent:'claude'});
  const refused = await start(f, {agent:'claude', codexThreads:'5'});
  assert.equal(refused.exitCode, 1, 'Claude must reject Codex limits');
  assert.equal((await start(f, {agent:'claude', model:'original-model'})).exitCode, 0);
  const before = bytes(f); f.herdr.calls.length = 0;
  assert.equal((await open(f, {model:'changed-model'})).exitCode, 1);
  assert.equal((await open(f, {newSession:true, model:'changed-model'}, f.agentPorts())).exitCode, 1);
  assert.deepEqual(bytes(f), before);
  assert.equal(f.herdr.calls.length, 0);
});

test('Theme D Herdr name binds after delayed native detection through status', async t => {
  const f = await fixture(t, {agent:'codex'}), native = f.ports.herdr;
  let delay = true;
  f.ports.herdr = async args => {
    if (delay && args[0] === 'agent' && args[1] === 'rename') throw Object.assign(Error('Not detected yet'), {code:'agent_not_found'});
    return native(args);
  };
  assert.equal((await start(f, {herdrAgentName:'delayed-chat'})).exitCode, 0);
  delay = false;
  const chat = f.record().chats.at(-1);
  assert.ok(chat.herdrAgentName?.startsWith('delayed-chat-'), 'The chat must save its stable name before detection');
  assert.equal((await status(f)).exitCode, 0);
  const named = await native(['agent','get',chat.herdrAgentName]);
  assert.equal(named.result.agent.pane_id, chat.paneId);
  // A saved pane can later hold another native conversation. Do not rename it.
  const saved = f.record().chats[0], occupant = f.herdr.paneOf(saved).agent;
  occupant.name = 'someone-else'; occupant.agent_session.value = 'aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa';
  f.herdr.calls.length = 0;
  assert.equal((await status(f)).exitCode, 0);
  assert.equal(f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'rename').length, 0);
  assert.equal(occupant.name, 'someone-else');
});

test('Theme D CLI forwards next-chat options and the caller environment', async () => {
  const invoked = [], output = {write(){}}, env = {HOME:'/synthetic/home', CLAUDE_CONFIG_DIR:'/synthetic/account'};
  const code = await runPdd(['workflow','open','17','--new','--model','fixed-model','--herdr-agent-name','named-chat','--codex-threads','5'], {
    cwd:'/synthetic/project', env, stdout:output, stderr:output,
    workflowRunner:{openRun:async (input,ports) => {invoked.push({input,ports}); return {exitCode:0,message:'Synthetic result'};}},
  });
  assert.equal(code,0,'The CLI must admit profile options');
  assert.equal(invoked.length,1);
  assert.equal(invoked[0].input.model,'fixed-model');
  assert.equal(invoked[0].input.herdrAgentName,'named-chat');
  assert.equal(invoked[0].input.codexThreads,'5');
  assert.equal(invoked[0].ports.env,env);
});

for (const requested of [4,5,6,7,8]) test(`Theme D Codex thread bound ${requested} reaches the native launch`, async t => {
  const f = await fixture(t, {agent:'codex'});
  assert.equal((await start(f, {codexThreads:String(requested)})).exitCode, 0);
  commandProfile(calls(f)[0][3], {model:null, threads:requested});
  assert.equal(f.record().launchProfile?.codexThreads, requested);
});

test('Theme D new Codex run supplies a small default limit without editing the account', async t => {
  const f = await fixture(t, {agent:'codex'});
  assert.equal((await start(f)).exitCode, 0);
  commandProfile(calls(f)[0][3], {model:null, threads:5});
  assert.equal(f.record().chats[0].launchProfile?.codexThreads, 5);
});

test('Theme D concurrent runs with the same requested prefix get distinct live Herdr names', async t => {
  const first = await fixture(t, {agent:'claude'}), second = await fixture(t, {agent:'claude'});
  // Both isolated Git repositories use one fake Herdr server, as on a real machine.
  second.ports.herdr = first.ports.herdr;
  const one = await start(first, {agent:'claude',herdrAgentName:'shared-prefix'});
  assert.equal(one.exitCode, 0, one.message);
  const two = await start(second, {agent:'claude',herdrAgentName:'shared-prefix'});
  assert.equal(two.exitCode, 0, two.message);
  const a = first.record().chats[0], b = second.record().chats[0];
  assert.notEqual(a.herdrAgentName, b.herdrAgentName, 'Names must include run identity even with an explicit prefix');
  assert.equal((await first.ports.herdr(['agent','get',a.herdrAgentName])).result.agent.pane_id, a.paneId);
  assert.equal((await first.ports.herdr(['agent','get',b.herdrAgentName])).result.agent.pane_id, b.paneId);
});

test('Theme D a historical area keeps its original snapshot after a later area selects another profile', async t => {
  const f = await fixture(t, {agent:'codex'});
  const first = folder(f,'first'), second = folder(f,'second');
  f.ports.env.CODEX_HOME = first;
  assert.equal((await start(f, {model:'first-model',codexThreads:'5'})).exitCode, 0);
  await status(f);
  const original = f.record().chats[0];
  await advance(f);
  f.ports.env.CODEX_HOME = second;
  const changed = await open(f, {newSession:true,model:'second-model',codexThreads:'6'});
  assert.equal(changed.exitCode, 0, changed.message);
  const current = f.record().launchProfile;
  f.herdr.paneOf(original).agent = null; f.herdr.calls.length = 0;
  const result = await open(f, {area:'plan'}); assert.equal(result.exitCode, 0, result.message);
  commandProfile(calls(f)[0][3], {model:'first-model',threads:5});
  assert.ok(calls(f)[0][3].includes(`CODEX_HOME=${quote(first)}`));
  assert.deepEqual(f.record().launchProfile, current);
});



for (const agent of ['codex','claude']) test(`Theme D ${agent} naming failure never hides an acknowledged launch or a live agent`, async t => {
  const f = await fixture(t, {agent}), healthy = f.ports.herdr, warnings = [];
  f.ports.say = text => warnings.push(text);
  f.ports.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'rename') throw Object.assign(Error('Synthetic name conflict'), {code:'agent_name_conflict'});
    return healthy(args);
  };
  const result = await start(f, {agent, herdrAgentName:'warning-test'});
  assert.equal(result.exitCode, 0, result.message);
  const chat = f.record().chats[0];
  assert.ok(warnings.some(text => text.includes('agent_name_conflict')), 'Name failures must be visible after acknowledged launch');
  assert.equal(chat.startUnconfirmed, undefined);
  assert.equal(calls(f).length, 1);
  const shown = await status(f); assert.equal(shown.exitCode, 0, shown.message);
  const item = JSON.parse(shown.message).runs[0];
  assert.equal(f.record().chats[0].state, 'running', 'Failed naming cannot erase the live observation');
  assert.equal(item.chat.namingError?.code, 'agent_name_conflict');
  f.herdr.calls.length = 0;
  const opened = await open(f); assert.equal(opened.exitCode, 0, opened.message);
  assert.ok(opened.message.includes('agent_name_conflict'));
  assert.equal(calls(f).length, 0, 'A naming failure must not cause another launch');
  f.herdr.paneOf(f.record().chats.at(-1)).agent = null;
  const resumed = await open(f); assert.equal(resumed.exitCode, 0, resumed.message);
  assert.ok(resumed.message.includes('agent_name_conflict'), 'Resume must return its post-launch naming warning');
  f.herdr.calls.length = 0;
  f.tick();
  const fresh = await open(f, {newSession:true}); assert.equal(fresh.exitCode, 0, fresh.message);
  assert.ok(fresh.message.includes('agent_name_conflict'), 'Fresh replacement must return its own naming warning');
  assert.equal(calls(f).length, 1);
  f.ports.herdr = healthy;
  const recovered = await status(f); assert.equal(recovered.exitCode, 0, recovered.message);
  assert.equal(JSON.parse(recovered.message).runs[0].chat.namingError, undefined);
  const current = f.record().chats.at(-1);
  assert.equal((await healthy(['agent','get',current.herdrAgentName])).result.agent.pane_id, current.paneId);
});

test('Theme D delayed naming requires own native evidence before assigning a null-session Codex chat name', async t => {
  const f = await fixture(t, {agent:'codex'}), healthy = f.ports.herdr;
  let delayed = true;
  f.ports.herdr = async args => {
    if (delayed && args[0] === 'agent' && args[1] === 'rename') throw Object.assign(Error('Synthetic detection delay'), {code:'agent_not_found'});
    return healthy(args);
  };
  assert.equal((await start(f, {herdrAgentName:'verified-chat'})).exitCode, 0);
  const chat = f.record().chats[0];
  assert.ok(chat.herdrAgentName, 'Startup must save a name to bind after detection');
  assert.equal(chat.session, null);
  const occupant = f.herdr.paneOf(chat).agent;
  occupant.name = 'unrelated-chat'; occupant.agent_session.value = 'bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb';
  delayed = false;
  for (let observation = 0; observation < 2; observation++) {
    f.herdr.calls.length = 0;
    const shown = await status(f); assert.equal(shown.exitCode, 0, shown.message);
    assert.equal(f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'rename').length, 0);
    assert.equal(occupant.name, 'unrelated-chat');
    assert.equal(JSON.parse(shown.message).runs[0].chat.namingError?.code, 'chat_name_unverified');
  }
});

test('Theme D immediate launch observation cannot name a foreign occupant', async t => {
  const f = await fixture(t, {agent:'codex'}), healthy = f.ports.herdr;
  f.ports.herdr = async args => {
    const reply = await healthy(args);
    if (args[0] === 'pane' && args[1] === 'run') {
      const occupant = f.herdr.panes.find(pane => pane.pane_id === args[2]).agent;
      occupant.name = 'foreign-occupant'; occupant.agent_session.value = 'cccccccc-cccc-4ccc-8ccc-cccccccccccc';
    }
    return reply;
  };
  assert.equal((await start(f, {herdrAgentName:'owned-prefix'})).exitCode, 0);
  const chat = f.record().chats[0];
  assert.ok(chat.herdrAgentName, 'The requested name must exist without assigning it to another occupant');
  assert.equal(f.herdr.paneOf(chat).agent.name, 'foreign-occupant');
  assert.equal(f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'rename').length, 0);
});

for (const agent of ['gemini','agy']) test(`Theme D ${agent} observations cannot create authority to rename a foreign native session`, async t => {
  const f = await fixture(t, {agent});
  assert.equal((await start(f, {agent,herdrAgentName:'unverified-prefix'})).exitCode, 0);
  const chat = f.record().chats[0];
  assert.ok(chat.herdrAgentName, 'The chat must retain its requested name while verification is unavailable');
  f.herdr.paneOf(chat).agent.name = 'foreign-session';
  for (let attempt = 0; attempt < 2; attempt++) {
    f.herdr.calls.length = 0;
    const shown = await status(f); assert.equal(shown.exitCode, 0, shown.message);
    assert.equal(JSON.parse(shown.message).runs[0].chat.namingError?.code, 'chat_name_unverified');
    assert.equal(f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'rename').length, 0);
    assert.equal(f.herdr.paneOf(chat).agent.name, 'foreign-session');
  }
});
