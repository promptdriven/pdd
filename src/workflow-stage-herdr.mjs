// Generated from prompts/cli/workflow-stage-herdr.prompt.md (sha256: 3e1696ef44abead80b9bcaaf9323c317ad13df0d836e1b1cbf61795c54828dd4).
import { execFile as execFileCallback, spawn } from 'node:child_process';
import { promisify } from 'node:util';
import { createHash } from 'node:crypto';
import { realpath } from 'node:fs/promises';

const execFile = promisify(execFileCallback);
const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
const STAGE = /^[a-z][a-z0-9-]{0,63}$/;
const READY = new Set(['idle', 'done']);
const clone = value => structuredClone(value);
const hash = value => createHash('sha256').update(value).digest('hex');
const sessionFor = runId => `pdd-${hash(runId.toLowerCase()).slice(0, 20)}`;
const canonical = value => JSON.stringify(value, function(key, item) {
  return item && !Array.isArray(item) && typeof item === 'object'
    ? Object.fromEntries(Object.entries(item).sort(([a], [b]) => a.localeCompare(b))) : item;
});
function issue(code) { return Object.assign(new Error(code), { code }); }
function fail(backend, reason, state = 'recovery_required') {
  return { state, backend: backend ? clone(backend) : null, evidence: clone(backend?.evidence ?? {}), reason };
}
function runtime(ports = {}) {
  const start = ports.spawn ?? spawn;
  return {
    guard: ports.withStageGuard ?? (() => { throw issue('stage_guard_required'); }),
    exec: ports.execFile ?? execFile,
    sleep: ports.sleep ?? (ms => new Promise(resolve => setTimeout(resolve, ms))),
    now: ports.now ?? Date.now,
    pollMs: ports.pollMs ?? 100,
    startupMs: ports.startupMs ?? 30000,
    activityMs: ports.activityMs ?? 5000,
    timeoutMs: ports.timeoutMs ?? 1800000,
    spawnServer: ports.spawnServer ?? ((session, cwd) => new Promise((resolve, reject) => {
      const child = start('herdr', ['--session', session, 'server'],
        { cwd, stdio: 'ignore', detached: true, shell: false });
      child.once('error', reject);
      child.once('spawn', () => { child.unref(); resolve(); });
    })),
    spawnAttach: ports.spawnAttach ?? ((session, target, cwd) => new Promise(resolve => {
      const child = start('herdr', ['--session', session, 'agent', 'attach', target],
        { cwd, stdio: 'inherit', shell: false });
      let error = false;
      child.once('error', () => { error = true; });
      child.once('close', code => resolve(error ? 1 : Number.isInteger(code) ? code : 1));
    }))
  };
}
function commandError(value, args, fallback) {
  const source = value?.error;
  const code = typeof source?.code === 'string' && /^[a-zA-Z0-9_-]{1,100}$/.test(source.code) ? source.code : fallback;
  const error = issue(code);
  error.detail = { operation: args.slice(0, 2).join('.'), code };
  if ((args[0] !== 'agent' || args[1] !== 'prompt') && typeof source?.message === 'string') error.detail.message = source.message.slice(0, 600);
  return error;
}
async function command(rt, session, args, cwd, timeout = 10000) {
  let response;
  try {
    response = await rt.exec('herdr', ['--session', session, ...args],
      { cwd, shell: false, encoding: 'utf8', maxBuffer: 1024 * 1024, timeout });
  } catch (error) {
    let structured;
    try { structured = JSON.parse(error.stderr); } catch { /* Never expose execFile's command/prompt message. */ }
    throw commandError(structured, args, typeof error.code === 'string' ? error.code : 'herdr_command_failed');
  }
  let result;
  try { result = JSON.parse(response.stdout); }
  catch { throw commandError(null, args, 'herdr_invalid_json'); }
  if (!result || Array.isArray(result) || typeof result !== 'object' || result.error) {
    throw commandError(result, args, 'invalid_herdr_reply');
  }
  return result;
}
function preNative(b) {
  const allowed = new Set(['version','runId','stageId','attemptId','agent','cwd','session','agentName',
    'promptDigest','nativeSession','phase','evidence','server']);
  return b.phase === 'server_intent' && b.nativeSession === null
    && b.evidence && !Array.isArray(b.evidence) && Object.keys(b.evidence).length === 0
    && Object.keys(b).every(key => allowed.has(key));
}

function prePrompt(b) {
  return ['start_intent', 'ready'].includes(b.phase) && b.evidence && !Array.isArray(b.evidence)
    && Object.keys(b.evidence).every(key => key === 'readySeq')
    && !['acceptanceDigest','cleanupConfirmation'].some(key => Object.hasOwn(b,key))
    && [b.workspaceId,b.tabId,b.paneId,b.terminalId].every(value => typeof value === 'string' && value);
}
function startupBlocked(b) {
  return { ...fail(b, 'native_start_person_action_required', 'blocked'),
    detail: { operation: 'agent.start', code: 'native_start_person_action_required',
      message: `Complete ordinary native startup using pdd workflow attach ${b.runId}, detach normally, then resume this same run. No PDD stage prompt has been sent.` } };
}
async function status(rt, session, cwd) {
  return command(rt, session, ['status', 'server', '--json'], cwd);
}
function compatible(value, session) {
  if (value.running !== true || value.session !== session || value.compatible !== true
    || value.endpoint_compatible !== true || !Number.isInteger(value.protocol)
    || typeof value.version !== 'string' || typeof value.socket !== 'string' || !value.socket) {
    throw issue('herdr_target_incompatible');
  }
  return { session, socket: value.socket, protocol: value.protocol, version: value.version };
}
function sameServer(actual, saved) {
  if (canonical(actual) !== canonical(saved)) throw issue('herdr_server_changed');
}
function agentFrom(response) {
  const agent = response?.result?.agent;
  if (!agent || !Number.isSafeInteger(agent.state_change_seq) || agent.state_change_seq < 0) {
    throw issue('invalid_agent_reply');
  }
  return agent;
}
function assertBackend(b) {
  if (!b || b.version !== 1 || !UUID.test(b.runId) || !UUID.test(b.attemptId) || !STAGE.test(b.stageId)
    || !['codex', 'claude'].includes(b.agent) || typeof b.cwd !== 'string'
    || ![sessionFor(b.runId), `pdd-${b.runId.toLowerCase()}`].includes(b.session)
    || (b.server ? b.server.session !== b.session : !preNative(b))) {
    throw issue('invalid_stage_backend');
  }
}
async function checkAgent(rt, b, supplied) {
  const a = supplied ?? agentFrom(await command(rt, b.session, ['agent', 'get', b.agentName], b.cwd));
  if (a.terminal_id === b.terminalId && a.pane_id === b.paneId && !a.agent) throw issue('native_agent_unavailable');
  for (const [key, expected] of Object.entries({ workspace_id: b.workspaceId, tab_id: b.tabId,
    pane_id: b.paneId, terminal_id: b.terminalId, name: b.agentName, agent: b.agent })) {
    if (!expected || a[key] !== expected) throw issue('stage_identity_changed');
  }
  if (await realpath(a.cwd ?? a.foreground_cwd ?? '') !== b.cwd) throw issue('stage_cwd_changed');
  if (b.nativeSession && canonical(a.agent_session ?? null) !== canonical(b.nativeSession)) throw issue('native_identity_changed');
  if (a.state_change_seq < (b.lastSeq ?? 0)) throw issue('stage_sequence_reversed');
  return a;
}
function recordAgent(b, a) {
  b.lastSeq = a.state_change_seq;
  if (!b.nativeSession && a.agent_session) b.nativeSession = clone(a.agent_session);
}
function isReady(a) { return READY.has(a.agent_status) && a.interactive_ready === true && !a.launch_pending; }
async function save(b, checkpoint) {
  if (typeof checkpoint !== 'function') throw issue('durable_checkpoint_required');
  await checkpoint(clone(b));
}
async function observe(rt, b, checkpoint) {
  try {
  return await rt.guard(b, async () => {
  const a = await checkAgent(rt, b);
  recordAgent(b, a);
  if (b.phase === 'candidate' && a.state_change_seq !== b.evidence.settledSeq) return fail(b, 'candidate_sequence_changed');
  if (a.agent_status === 'blocked') {
    if (checkpoint) await save(b, checkpoint);
    return fail(b, 'native_person_action_required', 'blocked');
  }
  if (a.agent_status === 'working') {
    if (b.phase !== 'prompt_intent' && b.phase !== 'submitted') return fail(b, 'unexpected_native_activity');
    b.evidence.workingSeq ??= a.state_change_seq;
    if (b.evidence.workingSeq <= b.evidence.readySeq) return fail(b, 'missing_new_prompt_activity');
    if (checkpoint) await save(b, checkpoint);
    return { state: 'active', backend: clone(b), evidence: clone(b.evidence) };
  }
  if (isReady(a) && b.evidence.workingSeq && a.state_change_seq > b.evidence.workingSeq) {
    b.evidence.settledSeq = a.state_change_seq;
    b.phase = 'candidate';
    if (checkpoint) await save(b, checkpoint);
    return { state: 'settled', backend: clone(b), evidence: clone(b.evidence) };
  }
  return fail(b, isReady(a) ? 'no_observed_prompt_activity' : 'native_state_unknown');
  });
  } catch (error) {
    if (error.code !== 'WORKFLOW_STAGE_BUSY') throw error;
    return {state:'active',reason:'stage_temporarily_guarded',backend:clone(b),evidence:clone(b.evidence)};
  }
}

export async function runHerdrStage(input, ports = {}) {
  const rt = runtime(ports);
  let b = input.backend ? clone(input.backend) : null;
  try {
    if (!UUID.test(input.runId) || !UUID.test(input.attemptId) || !STAGE.test(input.stageId)
      || !['codex', 'claude'].includes(input.agent) || typeof input.context !== 'string' || !input.context.trim()
      || typeof input.instructions !== 'string' || !input.instructions.trim() || typeof input.checkpoint !== 'function'
      || typeof ports.withStageGuard !== 'function') {
      throw issue('invalid_stage_input');
    }
    const cwd = await realpath(input.cwd);
    const prompt = `${input.context}\n\n# Current workflow stage\n${input.instructions}`;
    const promptDigest = hash(prompt);
    let priorServer, seedWorkspaceIds, recoveringBootstrap = false, continuingStartup = false;
    if (b) {
      assertBackend(b);
      if (b.runId !== input.runId || b.cwd !== cwd) throw issue('stage_binding_changed');
      if (b.stageId === input.stageId && b.attemptId === input.attemptId) {
        if (b.promptDigest !== promptDigest || b.agent !== input.agent) throw issue('stage_input_changed');
        if (prePrompt(b)) continuingStartup = true;
        else if (preNative(b)) recoveringBootstrap = true;
        else return inspectHerdrStage({ backend: b, cwd }, ports);
        priorServer = b.server ? clone(b.server) : undefined;
      } else {
        if (b.phase !== 'closed' || !b.acceptanceDigest) throw issue('previous_stage_not_released');
        priorServer = clone(b.server);
        seedWorkspaceIds = clone(b.seedWorkspaceIds);
      }
    }
    if (!continuingStartup) b = { version: 1, runId: input.runId, stageId: input.stageId, attemptId: input.attemptId,
      agent: input.agent, cwd, session: recoveringBootstrap ? b.session : priorServer?.session ?? sessionFor(input.runId),
      agentName: `pdd-${hash(input.attemptId).slice(0, 24)}`, promptDigest,
      nativeSession: null, phase: 'server_intent', evidence: {}, ...(priorServer ? {server: priorServer} : {}) };
    await save(b, input.checkpoint);
    const startupResult = await rt.guard(b, async () => {
    if (!continuingStartup) {
    if (recoveringBootstrap && b.session !== sessionFor(b.runId)) {
      const historical = await status(rt, b.session, cwd);
      if (historical.running !== false || historical.session !== b.session) throw issue('legacy_server_not_stopped');
      b.session = sessionFor(b.runId);
      delete b.server;
      priorServer = undefined;
      await save(b, input.checkpoint);
    }
    let server = await status(rt, b.session, cwd);
    if (!server.running) {
      if (priorServer && !recoveringBootstrap || server.running !== false || server.session !== b.session) throw issue('owned_server_missing');
      await rt.spawnServer(b.session, cwd);
      const until = rt.now() + rt.startupMs;
      while (rt.now() < until) {
        server = await status(rt, b.session, cwd);
        if (server.running) break;
        await rt.sleep(rt.pollMs);
      }
    } else if (!priorServer) throw issue('unowned_herdr_session');
    b.server = compatible(server, b.session);
    if (priorServer) sameServer(b.server, priorServer);
    await save(b, input.checkpoint);
    const listed = await command(rt, b.session, ['workspace', 'list'], cwd);
    const workspaces = listed.result?.workspaces;
    if (!Array.isArray(workspaces) || workspaces.some(w => typeof w.workspace_id !== 'string')) throw issue('invalid_workspace_inventory');
    const currentIds = workspaces.map(w => w.workspace_id).sort();
    if (!priorServer || recoveringBootstrap) seedWorkspaceIds = currentIds;
    if (!Array.isArray(seedWorkspaceIds) || seedWorkspaceIds.length > 1
      || canonical(currentIds) !== canonical([...seedWorkspaceIds].sort())) throw issue('active_stage_capacity_unavailable');
    b.seedWorkspaceIds = seedWorkspaceIds;
    b.maxActiveStages = 1;
    b.phase = 'workspace_intent';
    await save(b, input.checkpoint);
    const created = await command(rt, b.session, ['workspace', 'create', '--cwd', cwd,
      '--label', `PDD ${input.stageId}`, '--no-focus'], cwd);
    const { workspace, tab, root_pane: pane } = created.result ?? {};
    b.workspaceId = workspace?.workspace_id;
    b.tabId = tab?.tab_id;
    b.paneId = pane?.pane_id;
    b.terminalId = pane?.terminal_id;
    if (![b.workspaceId, b.tabId, b.paneId, b.terminalId].every(v => typeof v === 'string' && v)) throw issue('invalid_workspace_reply');
    b.phase = 'start_intent';
    await save(b, input.checkpoint);
    let started;
    try {
      started = await command(rt, b.session, ['agent', 'start', b.agentName, '--kind', b.agent,
        '--pane', b.paneId, '--timeout', String(rt.startupMs),
        ...(b.agent === 'codex' ? ['--', '--no-daemon', '--dangerously-bypass-approvals-and-sandbox', '-c', `projects={${JSON.stringify(cwd)}={trust_level="trusted"}}`] : ['--', '--dangerously-skip-permissions'])], cwd, rt.startupMs + 5000);
    } catch (error) {
      if (error.code !== 'agent_not_ready') throw error;
      const existing = await checkAgent(rt, b);
      recordAgent(b, existing);
      await save(b, input.checkpoint);
      if (existing.agent_status === 'blocked' || existing.launch_pending) return startupBlocked(b);
      throw error;
    }
    const launched = await checkAgent(rt, b, agentFrom(started));
    recordAgent(b, launched);
    await save(b, input.checkpoint);
    } else {
      sameServer(compatible(await status(rt, b.session, cwd), b.session), b.server);
    }
    // Query the live owned native, not only the launch response's earlier snapshot.
    const ready = await checkAgent(rt, b);
    recordAgent(b, ready);
    if (ready.agent_status === 'blocked' || ready.launch_pending) return startupBlocked(b);
    if (!isReady(ready)) return fail(b, 'native_start_not_ready');
    b.phase = 'ready';
    b.evidence.readySeq = ready.state_change_seq;
    await save(b, input.checkpoint);
    await rt.guard(b, async () => {
      // Identity/currentness and the durable one-submit intent share the attach/acceptance lock.
      const current = await checkAgent(rt, b);
      if (!isReady(current) || current.state_change_seq !== b.evidence.readySeq) throw issue('fresh_agent_changed_before_prompt');
      recordAgent(b, current);
      b.phase = 'prompt_intent';
      await save(b, input.checkpoint);
      const delivered = await command(rt, b.session, ['agent', 'prompt', b.agentName, prompt], cwd);
      const acknowledgement = await checkAgent(rt, b, agentFrom(delivered));
      recordAgent(b, acknowledgement);
      if (acknowledgement.agent_status === 'working' && acknowledgement.state_change_seq > b.evidence.readySeq) {
        b.evidence.workingSeq = acknowledgement.state_change_seq;
      }
      b.phase = 'submitted';
      await save(b, input.checkpoint);
    });
    });
    if (startupResult) return startupResult;
    const startedAt = rt.now(), deadline = startedAt + rt.timeoutMs;
    let activityDeadline = startedAt + rt.activityMs;
    while (rt.now() < deadline) {
      const seen = await observe(rt, b, input.checkpoint);
      b = seen.backend;
      if (seen.reason === 'stage_temporarily_guarded') {
        const pausedAt = rt.now();
        await rt.sleep(rt.pollMs);
        activityDeadline += rt.now() - pausedAt;
        continue;
      }
      if (seen.state === 'settled' || seen.state === 'blocked') return seen;
      if (seen.state === 'recovery_required' && seen.reason !== 'no_observed_prompt_activity') return seen;
      if (!b.evidence.workingSeq && rt.now() >= activityDeadline) return fail(b, 'prompt_activity_stalled');
      await rt.sleep(rt.pollMs);
    }
    return fail(b, 'stage_wait_timeout');
  } catch (error) {
    return { ...fail(b, typeof error.code === 'string' ? error.code : 'stage_transport_uncertain'),
      ...(error.detail ? { detail: error.detail } : {}) };
  }
}

export async function inspectHerdrStage({ backend, cwd }, ports = {}) {
  const rt = runtime(ports), b = clone(backend);
  try {
    assertBackend(b);
    if (await realpath(cwd ?? b.cwd) !== b.cwd) throw issue('stage_cwd_changed');
    if (b.phase === 'closed') return fail(b, 'stage_archived');
    if (b.phase === 'close_intent') return fail(b, 'stage_cleanup_unconfirmed');
    sameServer(compatible(await status(rt, b.session, b.cwd), b.session), b.server);
    const seen = await observe(rt, b);
    return seen.state === 'active' ? fail(seen.backend, 'native_stage_active') : seen;
  } catch (error) { return fail(b, error.code ?? 'stage_inspection_unavailable'); }
}

export async function attachHerdrStage({ backend }, ports = {}) {
  const rt = runtime(ports), b = clone(backend);
  try {
    assertBackend(b);
    if (b.phase === 'closed') return 2;
    return await rt.guard(b, async () => {
      sameServer(compatible(await status(rt, b.session, b.cwd), b.session), b.server);
      await checkAgent(rt, b);
      return rt.spawnAttach(b.session, b.agentName, b.cwd);
    });
  } catch { return 1; }
}

export async function closeHerdrStage({ backend, acceptance }, ports = {}) {
  const checkpoint = ports.checkpoint;
  const rt = runtime(ports), b = clone(backend);
  try {
    assertBackend(b);
    if (b.phase !== 'candidate' || !acceptance || acceptance.runId !== b.runId || acceptance.stageId !== b.stageId
      || acceptance.attemptId !== b.attemptId || acceptance.promptDigest !== b.promptDigest
      || acceptance.terminalId !== b.terminalId || !/^[0-9a-f]{64}$/.test(acceptance.evidenceDigest ?? '')) {
      throw issue('durable_stage_acceptance_required');
    }
    return await rt.guard(b, async () => {
    const seen = await inspectHerdrStage({ backend: b, cwd: b.cwd }, ports);
    if (seen.state !== 'settled' || seen.evidence.settledSeq !== b.evidence.settledSeq) throw issue('stage_not_quiescent');
    b.acceptanceDigest = hash(canonical(acceptance));
    b.phase = 'close_intent';
    await save(b, checkpoint);
    // This workspace was created for this stage only; its seed belongs to the run's server separately.
    const closed = await command(rt, b.session, ['workspace', 'close', b.workspaceId], b.cwd);
    if (Array.isArray(closed) || closed.id !== 'cli:workspace:close' || closed.result?.type !== 'ok') {
      throw issue('workspace_close_unconfirmed');
    }
    const inventory = await command(rt, b.session, ['workspace', 'list'], b.cwd);
    const workspaces = inventory.result?.workspaces;
    if (inventory.id !== 'cli:workspace:list' || inventory.result?.type !== 'workspace_list'
      || !Array.isArray(workspaces) || workspaces.some(w => !w || typeof w.workspace_id !== 'string')
      || new Set(workspaces.map(w => w.workspace_id)).size !== workspaces.length
      || workspaces.some(w => w.workspace_id === b.workspaceId)) throw issue('workspace_close_unconfirmed');
    b.cleanupConfirmation = { acknowledgement: 'ok', absentWorkspaceId: b.workspaceId };
    b.phase = 'closed';
    await save(b, checkpoint);
    return { state: 'closed', backend: b, evidence: clone(b.evidence) };
    });
  } catch (error) { return fail(b, error.code ?? 'stage_cleanup_uncertain'); }
}
