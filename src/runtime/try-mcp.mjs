// Generated from prompts/cli/try-mcp.prompt.md (sha256: f005492d96bf72699f50571513cd90416a70c422a79c079a79bb54e3ce7471f9).
import { createInterface } from 'node:readline';
import { readTryOwner, observeTryCall, runDoorCall, saveDoorCase, applyPendingCaseWithHandoff } from './runtime-client.mjs';
import { createRunJudge } from './agent-judge.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const text = x => typeof x === 'string' && x.length > 0;
const validSha256 = x => typeof x === 'string' && /^[0-9a-f]{64}$/i.test(x) ? x.toLowerCase() : null;
const validEngineSha = x => typeof x === 'string' && /^[0-9a-f]{8,40}$/i.test(x) ? x.toLowerCase() : null;
const validCommit = x => typeof x === 'string' && x.length > 0 ? x : null;
const schema = (properties, required = []) => ({
  type: 'object',
  properties: { story: { type: 'string' }, ...properties },
  ...(required.length ? { required } : {}),
  additionalProperties: false,
});
const tools = [
  ['try_open', 'Open or reuse the current repo and Story Try, or pass try_id to bind only an existing running simulation without opening or reopening one. Returns its entries, data and budget. No prompt approval.', { try_id: { type: 'string' } }, false],
  ['try_state', 'Read current Try data, entries and schemas, Story criteria, test inputs, runs, budget and progress. Opens a missing Try only when try_id is omitted.', { try_id: { type: 'string' } }, false],
  ['try_run', 'Run one action on the Try, spending its existing AI call budget. Pass try_id to require that exact running Try without opening or reopening one. Use entry and input, or exact CLI argv. Declared entry errors return structured error outcomes; every run appears on the Try page.', { try_id: { type: 'string' }, entry: { type: 'string' }, input: { type: 'object', additionalProperties: true }, argv: { type: 'array', items: { type: 'string' } } }, false],
  ['try_observe', 'Read call state and session state for run_id on try_id without opening, reopening, recovering or replaying a run. Works while the session is running, paused or stopped.', { try_id: { type: 'string' }, run_id: { type: 'string' } }, true, ['try_id', 'run_id']],
  ['try_check', 'Compare a confirmed run with the Story tests, with honest limits and first differences. No AI calls.', { try_id: { type: 'string' }, run_id: { type: 'string' } }, true],
  ['try_save_case', 'Save a confirmed run as an exact observed-result case. Or apply a retained pending_id with closed_editor_for: obtain the person’s actual confirmation that this exact original test is closed and handed over until apply finishes; generic tool approval is insufficient. Review its expectation and starting data; saving does not approve correctness.', { try_id: { type: 'string' }, run_id: { type: 'string' }, criterion_id: { type: 'string' }, name: { type: 'string' }, pending_id: { type: 'string', pattern: '^[0-9a-f]{64}\\.[0-9a-f]{64}$' }, closed_editor_for: { type: 'string', minLength: 1 } }, false],
].map(([name, description, properties, readOnlyHint, required]) => ({ name, description, inputSchema: schema(properties, required), annotations: { readOnlyHint, destructiveHint: false, idempotentHint: name !== 'try_run', openWorldHint: false } }));

function validate(name, args) {
  const tool = tools.find(tool => tool.name === name);
  if (!tool) throw new Error(`Unknown tool ${name}.`);
  if (!object(args)) throw new Error('Tool arguments must be an object.');
  for (const key of tool.inputSchema.required ?? []) {
    if (!Object.hasOwn(args, key)) throw new Error(`Missing required argument ${key}.`);
  }
  for (const [key, value] of Object.entries(args)) {
    const property = tool.inputSchema.properties[key];
    if (!property) throw new Error(`Unknown argument ${key}.`);
    if (property.type === 'string' && !text(value) || property.type === 'object' && !object(value)
      || property.type === 'array' && (!Array.isArray(value) || !value.every(x => typeof x === 'string'))) throw new Error(`Invalid ${key}.`);
  }
  if (name === 'try_run') {
    if (Object.hasOwn(args, 'argv')) {
      if (Object.hasOwn(args, 'entry') || Object.hasOwn(args, 'input')) throw new Error('Choose argv, or entry and input.');
    } else if (!text(args.entry) || !object(args.input)) throw new Error('Give entry and input, or argv.');
  }
  if(name==='try_save_case'&&(Object.hasOwn(args,'pending_id')||Object.hasOwn(args,'closed_editor_for'))){
    if(!text(args.pending_id)||!text(args.closed_editor_for))throw new Error('Give both pending_id and closed_editor_for for retained-case application.');
    if(!/^[a-f0-9]{64}\.[a-f0-9]{64}$/.test(args.pending_id))throw new Error('Invalid pending_id.');
    if(['story','try_id','run_id','criterion_id','name'].some(key=>Object.hasOwn(args,key)))throw new Error('Pending application accepts only pending_id and closed_editor_for.');
  }
}

function recordedCaseNote({scope,covered,total}){
  const prefix=scope==='original-story'?`Recorded case; covers ${covered} of ${total} Story criteria.${total>1?' Complete coverage before pdd test.':''}`
    :scope==='retained-scenario'?`Recorded case; references ${covered} of ${total} retained scenario criteria. Whole-Story coverage is unavailable. Complete coverage before pdd test.`
      :'Recorded case; criterion coverage is unavailable. Complete coverage before pdd test.';
  return prefix+' This records observed output; review its expectation and saved-data setup before replaying.';
}

export function createTryTools({ cwd = process.cwd(), words = [], env } = {}, ports = {}) {
  const dependencies = {
    ...ports,
    readTryOwner: ports.readTryOwner ?? readTryOwner,
    observeTryCall: ports.observeTryCall ?? observeTryCall,
    runDoorCall: ports.runDoorCall ?? runDoorCall,
    saveDoorCase: ports.saveDoorCase ?? saveDoorCase,
    applyPendingCaseWithHandoff: ports.applyPendingCaseWithHandoff ?? applyPendingCaseWithHandoff,
  };
  const runtimePorts = { ...ports, env: env ?? ports.env ?? process.env, stdout: ports.stderr ?? process.stderr, stderr: ports.stderr ?? process.stderr };
  const sessions = new Map();
  let queue = Promise.resolve();
  async function invoke(name, args) {
    validate(name, args);
    if(name==='try_save_case'&&Object.hasOwn(args,'pending_id')){
      const outcome=await dependencies.applyPendingCaseWithHandoff({cwd,pendingId:args.pending_id,handoff:{kind:'closed-editor',testPath:args.closed_editor_for},signal:runtimePorts.signal},runtimePorts);
      if(outcome.kind!=='case'||outcome.result.state!=='committed')throw new Error(outcome.message);
      return{pending_id:args.pending_id,result:outcome.message,note:recordedCaseNote(outcome.coverage)};
    }
    if (name === 'try_observe') {
      return await dependencies.observeTryCall({ cwd, story: args.story ?? words[0], tryId: args.try_id, runId: args.run_id }, runtimePorts);
    }
    const owner = await dependencies.readTryOwner({ cwd, story: args.story ?? words[0], ...(args.try_id ? { tryId: args.try_id } : {}) }, runtimePorts);
    const key = `${owner.root}:${owner.record.id}`;
    let session = sessions.get(key);
    if (!session) {
      session = { judge: createRunJudge({ scenario: owner.test.doc }), runs: [], unknown: false };
      sessions.set(key, session);
    }
    const { judge, runs } = session;
    if (name === 'try_open' || name === 'try_state') return {
      story: owner.test.title, story_path: owner.test.storyPath, try_id: owner.record.id,
      source_sha256: validSha256(owner.model?.source_sha256) ?? validSha256(owner.source_sha256) ?? validSha256(owner.record?.source_sha256) ?? null,
      engine_sha: validEngineSha(owner.model?.engine_sha) ?? validEngineSha(owner.engine_sha) ?? validEngineSha(owner.record?.engine_sha) ?? null,
      server_commit: validCommit(owner.model?.server_commit) ?? validCommit(owner.server_commit) ?? validCommit(owner.record?.server_commit) ?? null,
      criteria: owner.test.doc.criteria, test_inputs: judge.bindings(),
      entries: owner.model.entries.map(e => ({ ...e, entry: `${e.entry_path}#${e.operation}` })),
      data_now: owner.data ?? null, ...(owner.data_error ? { data_error: owner.data_error } : {}),
      runs: runs.map(({ saved, ...run }) => run), calls: owner.model.calls ?? null, actions: owner.actions ?? null,
      progress: judge.snapshot(), ...(session.unknown ? { warning: 'A run has an unknown outcome. Do not repeat it automatically.' } : {}),
    };
    if (name === 'try_run') {
      if (session.unknown) throw new Error('A prior run has an unknown outcome. Inspect the Try page before starting another run; do not repeat it automatically.');
      let entry, input;
      if (Object.hasOwn(args, 'argv')) {
        const cli = owner.model.entries.filter(e => e.cli === true);
        if (cli.length !== 1) throw new Error('This Try needs exactly one CLI entry for argv. Choose an explicit entry and input from try_state.');
        entry = cli[0]; input = { argv: args.argv };
      } else {
        entry = owner.model.entries.find(e => `${e.entry_path}#${e.operation}` === args.entry);
        input = args.input;
      }
      if (!entry) throw new Error('Unknown entry. Read try_state for admitted entries.');
      const started = Date.now();
      let answer;
      try {
        answer = await dependencies.runDoorCall({ root: owner.root, originalPath:owner.test.path, origin: owner.record.origin, sessionId: owner.record.id,
          login: owner.record.login, prompt: entry.entry_path, operation: entry.operation, callCap: owner.model.calls?.cap ?? null,
          existingOnly: Boolean(args.try_id), declaredErrors: Array.isArray(entry.errors) ? entry.errors : [] }, input, runtimePorts);
      } catch (error) {
        // The door owns dispatch/recovery. Conservatively block a second mutation when its outcome is unconfirmed.
        if (error.unknownOutcome === true) session.unknown = true;
        throw error;
      }
      const isProgramError = answer.error !== undefined && answer.error !== null;
      const run = { id: answer.id, ...(answer.actionId !== undefined ? { action_id: answer.actionId } : {}),
        ...(answer.replayed !== undefined ? { replayed: Boolean(answer.replayed) } : {}),
        entry: `${entry.entry_path}#${entry.operation}`, input,
        ...(answer.inputWorld !== undefined ? { world_before: answer.inputWorld } : {}),
        ...(isProgramError ? { error: answer.error } : { result: answer.result, error: null }),
        ...(answer.world !== undefined ? { world_after: answer.world } : {}), lossless: true };
      runs.push(run);
      return { run_id: run.id, action_id: answer.actionId ?? null, replayed: Boolean(answer.replayed),
        result: isProgramError ? null : run.result, error: isProgramError ? run.error : null,
        data_before: run.world_before ?? null, data_after: run.world_after ?? null,
        ...(answer.inputWorld === undefined || answer.world === undefined ? { data_warning: 'The interpreter did not supply both run world snapshots; world checks may be unavailable.' } : {}),
        usage: answer.usage ?? null, seconds: Math.round((Date.now() - started) / 100) / 10 };
    }
    const run = args.run_id ? runs.find(run => run.id === args.run_id) : runs.at(-1);
    if (!run) throw new Error('No matching confirmed run. Use try_run first.');
    if (name === 'try_check') return { run_id: run.id, verdict: judge.record(run), progress: judge.snapshot() };
    if (run.saved) return { run_id: run.id, already_saved: true, result: run.saved };
    const criteria = owner.test.doc.criteria ?? [];
    const tied = [...new Set(owner.test.doc.steps.filter(step => `${step.entry_path}#${step.operation}` === run.entry).flatMap(step => (step.checks ?? []).map(check => check.criterion_id)))];
    const criterion = args.criterion_id ?? (tied.length === 1 ? tied[0] : undefined);
    if (!criteria.some(item => item.id === criterion)) throw new Error(`Choose criterion_id from: ${criteria.map(item => item.id).join(', ')}.`);
    if (!object(run.world_before)) throw new Error('The interpreter did not provide a confirmed starting world. This run cannot be saved safely.');
    const separator = run.entry.lastIndexOf('#');
    const step = run.error && typeof run.error.code === 'string'
      ? { step_id: `try-${run.id}`, entry_path: run.entry.slice(0, separator), operation: run.entry.slice(separator + 1), input: run.input,
          expected_error: run.error.code, checks: [{ criterion_id: criterion, target: 'error', path: '/code', op: 'equals', value: run.error.code }] }
      : { step_id: `try-${run.id}`, entry_path: run.entry.slice(0, separator), operation: run.entry.slice(separator + 1), input: run.input,
          checks: [{ criterion_id: criterion, target: 'result', path: '', op: 'equals', value: run.result }] };
    const result = dependencies.saveDoorCase(owner.root, { id: run.id, name: args.name ?? 'Recorded Try tool run', story_path: owner.test.storyPath, original_path: owner.test.path,
      test: { schema_version: 'prompt-runtime.program-scenario.v1', story_path: owner.test.storyPath, criteria, initial_world: run.world_before, simulation: owner.test.doc.simulation ?? {}, context: owner.test.doc.context ?? [],
        steps: [step] } }, { ...runtimePorts, ports: runtimePorts, isolated: true });
    if (!result.startsWith('added ') && !result.startsWith('already saved ')) throw new Error(result);
    run.saved = result;
    return { run_id: run.id, result, note: recordedCaseNote({scope:'original-story',covered:1,total:criteria.length}) };
  }
  return { call(name, args = {}) { const result = queue.then(() => invoke(name, args)); queue = result.catch(() => {}); return result; } };
}

export async function runMcp({ cwd = process.cwd(), words = [], env, client } = {}, ports = {}) {
  const serverVersion = typeof client?.version === 'string' && client.version ? client.version : typeof ports.clientVersion === 'string' && ports.clientVersion ? ports.clientVersion : '0.0.0';
  const stdin = ports.stdin ?? process.stdin, stdout = ports.stdout ?? process.stdout, stderr = ports.stderr ?? process.stderr;
  const service = createTryTools({ cwd, words, env }, ports), replay = new Map();
  const send = message => stdout.write(`${JSON.stringify(message)}\n`);
  const error = (id, code, message) => ({ jsonrpc: '2.0', id, error: { code, message } });
  const validId = id => id === null || typeof id === 'string' || typeof id === 'number' && Number.isFinite(id);
  async function respond(msg) {
    const id = msg.id;
    if (msg.method === 'initialize') {
      if (!object(msg.params) || typeof msg.params.protocolVersion !== 'string' || !object(msg.params.capabilities) || !object(msg.params.clientInfo)) return error(id, -32602, 'Invalid initialize parameters');
      const versions = ['2025-06-18', '2025-03-26', '2024-11-05'];
      return { jsonrpc: '2.0', id, result: { protocolVersion: versions.includes(msg.params.protocolVersion) ? msg.params.protocolVersion : versions[0], capabilities: { tools: {} }, serverInfo: { name: 'pdd-try', version: serverVersion } } };
    }
    if (msg.method === 'ping' || msg.method === 'tools/list') {
      if (msg.params !== undefined && !object(msg.params)) return error(id, -32602, 'Parameters must be an object');
      return { jsonrpc: '2.0', id, result: msg.method === 'ping' ? {} : { tools } };
    }
    if (msg.method !== 'tools/call') return error(id, -32601, 'Method not found');
    if (!object(msg.params) || !text(msg.params.name) || msg.params.arguments !== undefined && !object(msg.params.arguments)) return error(id, -32602, 'Invalid tools/call parameters');
    const token = msg.params._meta?.progressToken;
    let progress = 0;
    const tick = () => {
      stderr.write(`pdd mcp: ${msg.params.name} is still working…\n`);
      if (typeof token === 'string' || typeof token === 'number') send({ jsonrpc: '2.0', method: 'notifications/progress', params: { progressToken: token, progress: ++progress, message: `${msg.params.name} is still working` } });
    };
    const timer = setInterval(tick, ports.progressMs ?? 10_000);
    timer.unref?.();
    try {
      const value = await service.call(msg.params.name, msg.params.arguments ?? {});
      return { jsonrpc: '2.0', id, result: { content: [{ type: 'text', text: JSON.stringify(value) }], structuredContent: value } };
    } catch (e) {
      return { jsonrpc: '2.0', id, result: { content: [{ type: 'text', text: String(e.message || 'The Try tool failed.') }], isError: true } };
    } finally { clearInterval(timer); }
  }
  const pending = new Set();
  const input = createInterface({ input: stdin, crlfDelay: Infinity });
  for await (const line of input) {
    if (Buffer.byteLength(line) > 1_048_576) { send(error(null, -32600, 'Request exceeds 1 MiB')); continue; }
    let msg;
    try { msg = JSON.parse(line); } catch { send(error(null, -32700, 'Parse error')); continue; }
    if (!object(msg) || msg.jsonrpc !== '2.0' || typeof msg.method !== 'string' || Object.hasOwn(msg, 'id') && !validId(msg.id)) { send(error(null, -32600, 'Invalid Request')); continue; }
    if (!Object.hasOwn(msg, 'id')) continue;
    const key = `${typeof msg.id}:${msg.id}`, signature = JSON.stringify(msg);
    const prior = replay.get(key);
    if (prior) {
      if (prior.signature !== signature) send(error(msg.id, -32600, 'Request ID already used for a different request'));
      else { const task = prior.answer.then(send); pending.add(task); task.finally(() => pending.delete(task)); }
      continue;
    }
    const answer = respond(msg).catch(() => error(msg.id, -32603, 'Internal error'));
    const record = { signature, answer, settled: false };
    replay.set(key, record);
    // Keep pending IDs until completion and a bounded recent replay window afterwards.
    const task = answer.then(send).finally(() => {
      pending.delete(task); record.settled = true;
      if (replay.size > 1024) for (const [old, cached] of replay) { if (old !== key && cached.settled) { replay.delete(old); break; } }
    });
    pending.add(task);
  }
  await Promise.all(pending);
  return 0;
}
