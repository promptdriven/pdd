// Generated from prompts/cli/workflow-runner.prompt.md (sha256: 8e29afeaa6ba3268dc6d6328acb9b0f95dc0f0b111fe86b508679d6607a757bd).
import { execFile as execFileCallback } from 'node:child_process';
import { promisify, isDeepStrictEqual } from 'node:util';
import { createHash, randomUUID } from 'node:crypto';
import { constants, fstatSync, openSync, closeSync, writeSync, readSync, fsyncSync, mkdirSync, readFileSync, readdirSync,
  lstatSync, realpathSync, unlinkSync, readlinkSync, existsSync } from 'node:fs';
import { join, resolve, relative, isAbsolute, sep, basename, dirname } from 'node:path';
import { AsyncLocalStorage } from 'node:async_hooks';
import { WORKFLOW_STAGES } from './workflow-definitions.mjs';
import { loadWorkflowDefinition } from './workflow-definition-loader.mjs';
import { resolveWorkflowIssue, prepareWorkflowPr, publishWorkflowPr, reconcileWorkflowPr } from './workflow-github.mjs';
import { readWorkflowHandoff, assertWorkflowArtifacts, runWorkflowTestCommands } from './workflow-artifacts.mjs';
export { WORKFLOW_STAGES } from './workflow-definitions.mjs';

const ordinaryExec = promisify(execFileCallback);
const defaultExec = (file, args, { cwd }) => ordinaryExec(file, args, { cwd, encoding: 'utf8', shell: false, maxBuffer: 16 * 1024 * 1024 });
const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
const digest = value => createHash('sha256').update(value).digest('hex');
const text = value => typeof value === 'string' && value.trim().length > 0;
const fail = message => { throw Error(message); };

function dependencies(ports = {}) {
  return { ...ports, execFile: ports.execFile ?? defaultExec, commandPorts: ports.execFile ? { execFile: ports.execFile } : {},
    stdout: ports.stdout ?? process.stdout, stderr: ports.stderr ?? process.stderr };
}
async function command(p, cwd, executable, args, raw = false) {
  const result = await p.execFile(executable, args, { cwd });
  if (Number.isInteger(result?.code) && result.code !== 0) fail(`${executable} command failed (${result.code}).`);
  const output = String(result?.stdout ?? '');
  return raw ? output : output.replace(/\r?\n$/, '');
}
const git = (p, cwd, ...args) => command(p, cwd, 'git', args);
const json = value => { try { return JSON.parse(value); } catch { fail('A tool or saved artifact returned invalid JSON.'); } };

async function repository(cwd, p) {
  if (!text(cwd)) fail('A current project directory is required.');
  const root = realpathSync(await git(p, cwd, 'rev-parse', '--show-toplevel'));
  if (lstatSync(join(root, '.git')).isSymbolicLink()) fail('Git metadata cannot be a symlink.');
  const gitDir = realpathSync(await git(p, root, 'rev-parse', '--absolute-git-dir'));
  const commonDir = realpathSync(await git(p, root, 'rev-parse', '--path-format=absolute', '--git-common-dir'));
  return { root, gitDir, commonDir };
}
async function fingerprint(r, p) {
  const head = await git(p, r.root, 'rev-parse', 'HEAD');
  const branch = await git(p, r.root, 'symbolic-ref', '--quiet', '--short', 'HEAD').catch(() => '(detached)');
  const staged = await command(p, r.root, 'git', ['diff', '--cached', '--binary', 'HEAD', '--'], true);
  const diff = await command(p, r.root, 'git', ['diff', '--binary', 'HEAD', '--'], true);
  const names = (await command(p, r.root, 'git', ['ls-files', '--others', '--exclude-standard', '-z'], true)).split('\0').filter(Boolean).sort();
  const untracked = names.map(name => {
    const path = resolve(r.root, name), info = lstatSync(path);
    if (!contained(r.root, path)) fail('A project path escaped its root.');
    return [name, digest(info.isSymbolicLink() ? readlinkSync(path) : readFileSync(path))];
  });
  return { head, hash: digest(JSON.stringify({ head, branch, staged, diff, untracked })) };
}
function contained(root, path) { const part = relative(root, path); return part && part !== '..' && !part.startsWith(`..${sep}`) && !isAbsolute(part); }
function requireDirectory(path) {
  const stat = lstatSync(path);
  if (!stat.isDirectory() || stat.isSymbolicLink() || realpathSync(path) !== path) fail('Workflow metadata directories must not follow aliases.');
}
function ensureDirectory(path) {
  if (!existsSync(path)) {
    try { mkdirSync(path, { mode: 0o700 }); }
    catch (error) { if (error.code !== 'EEXIST') throw error; }
  }
  requireDirectory(path);
}
function journalFile(path) {
  const stat = lstatSync(path);
  if (!stat.isFile() || stat.isSymbolicLink() || stat.nlink !== 1 || realpathSync(path) !== path)
    fail('Workflow journal must be a single ordinary metadata file.');
}
function syncDirectory(path) {
  const fd = openSync(path, 'r');
  try { fsyncSync(fd); } finally { closeSync(fd); }
}
function durable(path, value) {
  const fd = openSync(path, constants.O_WRONLY | constants.O_APPEND | constants.O_CREAT | (constants.O_NOFOLLOW ?? 0), 0o600);
  const bytes = Buffer.from(JSON.stringify(value) + '\n');
  try {
    const stat = fstatSync(fd);
    if (!stat.isFile() || stat.nlink !== 1) fail('Workflow journal cannot alias another file.');
    let written = 0;
    while (written < bytes.length) {
      const count = writeSync(fd, bytes, written, bytes.length - written);
      if (count < 1) fail('Workflow journal could not be completely persisted.');
      written += count;
    }
    fsyncSync(fd);
  } finally { closeSync(fd); }
  syncDirectory(dirname(path));
}

function readSaved(directory) {
  requireDirectory(directory);
  const path = join(directory, 'journal.jsonl'); journalFile(path);
  const fd = openSync(path, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
  let saved, sequence = 0, fragments = [], length = 0, padding = false, terminated = false;
  const consume = line => {
    if (!line.trim()) { padding = true; return; }
    if (padding) fail('Saved workflow journal is invalid.');
    const row = json(line);
    if (row.seq !== ++sequence || row.state?.seq !== row.seq || !row.state
      || saved && row.state.runId !== saved.runId) fail('Saved workflow journal is invalid.');
    saved = row.state;
  };
  try {
    const info = fstatSync(fd);
    if (!info.isFile() || info.nlink !== 1) fail('Workflow journal cannot alias another file.');
    const chunk = Buffer.allocUnsafe(64 * 1024);
    let count;
    while ((count = readSync(fd, chunk, 0, chunk.length, null)) > 0) {
      let start = 0, newline;
      while ((newline = chunk.indexOf(10, start)) !== -1 && newline < count) {
        if (fragments.length) {
          fragments.push(chunk.subarray(start, newline));
          consume(Buffer.concat(fragments, length + newline - start).toString('utf8'));
          fragments = []; length = 0;
        } else consume(chunk.toString('utf8', start, newline));
        start = newline + 1;
      }
      if (start < count) {
        const fragment = Buffer.from(chunk.subarray(start, count));
        fragments.push(fragment); length += fragment.length;
      }
      terminated = chunk[count - 1] === 10;
    }
    if (!terminated) fail('Saved workflow journal is incomplete; inspect it without replaying effects.');
  } finally { closeSync(fd); }
  if (!saved || !UUID.test(saved.runId) || saved.runId !== basename(directory)
    || !Number.isInteger(saved.index) || saved.index < 0 || saved.index > saved.definitions?.length
    || saved.version !== 2 || !Array.isArray(saved.completed) || !saved.definition || !saved.assignment
    || !['codex', 'claude'].includes(saved.agent) || !isDeepStrictEqual(saved.definitions, saved.definition.stages)
    || saved.name !== saved.definition.name || saved.assignment.runId !== saved.runId) fail('Saved workflow identity or definitions changed.');
  return saved;
}
const progressScope = new AsyncLocalStorage();
function progress(s, event, state) {
  const observe = progressScope.getStore();
  if (typeof observe !== 'function' || !s) return;
  const stage = s.definitions?.[s.index];
  const directory = s.gitDir ? join(s.gitDir, 'pdd', 'workflows', s.runId) : null;
  const last = s.completed?.at(-1);
  const handoff = s.completed?.findLast(step => step.handoff)?.handoff;
  const proposal = s.proposal ? s.completed?.findLast(step => s.definitions?.find(def => def.id === step.id)?.protocol === 'proposal')?.handoff : null;
  const backend = s.pending?.backend;
  try { observe(structuredClone({ event, state, runId: s.runId, name: s.name, issue: s.issue?.number,
    stage: stage ? { id: stage.id, kind: stage.kind, optional: !!stage.optional } : null,
    ordinal: s.index + 1, total: s.definitions?.length, root: s.root, branch: s.assignment?.branch,
    journal: directory ? join(directory, 'journal.jsonl') : null, pending: s.pending?.kind,
    ended: last?.id, backend: backend ? { session: backend.session, workspaceId: backend.workspaceId } : null,
    summary: handoff?.summary, files: directory ? [...new Set([handoff, proposal].filter(Boolean).flatMap(item => [join(directory, item.path),
      ...item.files.map(file => resolve(s.root, file.path))]))] : [],
    prs: (s.completed ?? []).filter(step => step.pr).map(step => step.pr.url)
  })); } catch { /* Observation cannot change workflow authority or progress. */ }
}
function record(s, directory, event) {
  s.seq = (s.seq ?? 0) + 1;
  durable(join(directory, 'journal.jsonl'), { seq: s.seq, event, state: s });
  progress(s, event);
}
function lock(root) {
  ensureDirectory(dirname(root)); ensureDirectory(root);
  syncDirectory(root); syncDirectory(dirname(root)); syncDirectory(dirname(dirname(root)));
  const path = join(root, '.lock'), claim = join(root, '.lock-claim');
  let claiming;
  try { claiming = openSync(claim, 'wx', 0o600); }
  catch (error) {
    if (error.code === 'EEXIST') fail('Another workflow command is acquiring its lock; an interrupted claim requires inspection.');
    throw error;
  }
  try {
    if (existsSync(path)) {
      const pid = Number(readFileSync(path, 'utf8'));
      if (!Number.isSafeInteger(pid) || pid < 1) fail('Workflow lock is invalid; inspect the saved run.');
      try { process.kill(pid, 0); fail('Another workflow command is active in this project.'); }
      catch (error) { if (error.code !== 'ESRCH') throw error; }
      unlinkSync(path);
    }
    const fd = openSync(path, 'wx', 0o600);
    try { writeSync(fd, String(process.pid)); fsyncSync(fd); } finally { closeSync(fd); }
  } finally { closeSync(claiming); unlinkSync(claim); }
  return () => unlinkSync(path);
}
function result(s, state, message) {
  progress(s, 'result', state);
  const runId = s?.runId ?? null, stage = s?.definitions?.[s.index]?.id ?? null;
  return { exitCode: ['failed', 'recovery_required'].includes(state) ? 1 : state === 'waiting' ? 2 : 0,
    state, runId, stage, message: `${state}: run ${runId ?? '(not started)'}${stage ? ` / ${stage}` : ''}. ${message}` };
}
const stageGuardOwner = new AsyncLocalStorage();
function stageGuard(s) {
  const commonDir = s.assignment?.commonDir;
  if (!commonDir || !UUID.test(s.runId)) fail('A verified issue assignment is required for the stage guard.');
  const parent = join(commonDir, 'pdd', 'workflow-stage-guards');
  ensureDirectory(parent);
  const root = join(parent, s.runId);
  return async function withStageGuard(backend, action) {
    if (!backend || backend.runId !== s.runId || backend.cwd !== s.root || typeof action !== 'function')
      fail('The shared stage guard does not match this assigned run.');
    if (stageGuardOwner.getStore()?.root === root && stageGuardOwner.getStore().active) return action();
    let release;
    try { release = lock(root); }
    catch (error) { throw Object.assign(Error(error.message), { code: 'WORKFLOW_STAGE_BUSY' }); }
    const owner = { root, active: true };
    try { return await stageGuardOwner.run(owner, action); }
    finally { owner.active = false; release(); }
  };
}
function attachmentEpoch(s, increment = false) {
  const root = join(s.assignment.commonDir, 'pdd', 'workflow-stage-guards', s.runId);
  if (stageGuardOwner.getStore()?.root !== root || !stageGuardOwner.getStore().active) fail('Attachment epoch requires the shared stage guard.');
  const path = join(root, 'attachments.jsonl');
  let epoch = 0;
  if (existsSync(path)) {
    journalFile(path);
    const bytes = readFileSync(path, 'utf8');
    if (!bytes.endsWith('\n')) fail('Attachment epoch is incomplete; inspect without accepting an older candidate.');
    for (const line of bytes.trimEnd().split('\n')) {
      const entry = json(line);
      if (entry.runId !== s.runId || entry.epoch !== epoch + 1) fail('Attachment epoch is invalid.');
      epoch = entry.epoch;
    }
  }
  if (increment) { epoch++; durable(path, { runId: s.runId, epoch }); }
  return epoch;
}
async function sourceValid(s, r) { await assertWorkflowArtifacts({ cwd: r.root, files: s.accepted?.files ?? [] }); }
function authority(s, r) {
  if (s.root !== r.root || s.gitDir !== r.gitDir || s.repo !== r.repo || s.base !== r.base) fail('The saved run belongs to a different project or repository.');
}
async function current(s, r, p) {
  authority(s, r);
  await assignedRepository(s.assignment, p);
  if (!isDeepStrictEqual(s.expected, await fingerprint(r, p))) fail('Project HEAD or worktree changed since the saved input; inspect before advancing.');
  await sourceValid(s, r);
}
async function handoff(s, stage, r, directory) {
  const roles = stage.requiredRoles ?? [];
  const h = await readWorkflowHandoff({ handoffPath: s.pending.handoffPath, cwd: r.root,
    expected: { runId: s.runId, stageId: stage.id, issueUrl: s.issue.url, inputRevision: s.pending.input.head },
    requiredRoles: roles });
  const reportOnly = stage.protocol === 'report';
  if (!h.files.length && !reportOnly) fail('This work stage requires concrete project artifacts.');
  if (stage.protocol === 'proposal' && !h.testCommands?.length) fail('Independent expectations and a native test argv plan are required.');
  return { summary: h.summary, files: h.files, testCommands: h.testCommands ?? [], reportOnly: !h.files.length,
    path: relative(directory, s.pending.handoffPath) };
}
function nativePorts(s, directory, r, options, p) {
  const guard = stageGuard(s);
  return {
    withStageGuard: (backend, action) => guard(backend, async () => {
      await validateInput(s, options, p);
      if (['ready', 'prompt_intent'].includes(backend.phase)) await current(s, r, p);
      return action();
    }),
    checkpoint: async backend => {
      const pending = s.pending;
      if (!pending || backend.runId !== s.runId || backend.stageId !== pending.stage
        || backend.attemptId !== pending.attemptId || backend.cwd !== r.root || backend.agent !== s.agent)
        fail('Native checkpoint is not bound to the original assigned stage attempt.');
      for (const field of ['session', 'server', 'workspaceId', 'tabId', 'paneId', 'terminalId', 'agentName', 'nativeSession']) {
        if (pending.backend?.[field] != null && !isDeepStrictEqual(pending.backend[field], backend[field]))
          fail('An established native backend identity changed.');
      }
      pending.backend = structuredClone(backend);
      record(s, directory, 'agent.backend');
    }
  };
}
function candidateIdentity(s, stage, outcome) {
  const b = outcome?.backend, pending = s.pending;
  if (!b || b.runId !== s.runId || b.stageId !== stage.id || b.attemptId !== pending.attemptId
    || b.cwd !== s.root || b.agent !== s.agent || b.promptDigest !== pending.promptDigest)
    fail('The returned native candidate does not match this original stage attempt.');
  const e = outcome.evidence;
  if (outcome.state === 'settled' && (!Number.isSafeInteger(e?.readySeq) || !Number.isSafeInteger(e.workingSeq)
    || !Number.isSafeInteger(e.settledSeq) || e.workingSeq <= e.readySeq || e.settledSeq <= e.workingSeq
    || !isDeepStrictEqual(e, b.evidence))) fail('Same-agent working to settled evidence is incomplete.');
}
function agentInstructions(s, stage, directory, attemptId, handoffPath, inputRevision) {
  const input = { runId: s.runId, stageId: stage.id, attemptId, protocol: stage.protocol, requiredRoles: stage.requiredRoles,
    issue: s.issue, inputRevision: inputRevision.head,
    inputFingerprint: inputRevision.hash, handoffPath, priorArtifacts: s.completed.flatMap(step => step.handoff?.files ?? []),
    priorReports: s.completed.filter(step => step.handoff).map(step => ({ stageId: step.id, summary: step.handoff.summary, handoffPath: join(directory, step.handoff.path), revision: step.revision })),
    accepted: s.accepted ?? null };
  return `Execute ONLY the current ${stage.id} stage of ${s.name}, then stop. Never perform a future stage, push, create/merge a PR or change native login, permissions or global configuration. Read the ENTIRE supplied Prompting guide FIRST and summarize its relevant method before any Story. Existing project instructions/permissions apply. Work in the assigned issue topic branch and commit requested work when appropriate; do not switch to a different branch; never force checkout, reset, stash or overwrite unrelated work.\nPDD_STAGE_INPUT_JSON\n${JSON.stringify(input)}\nPDD_STAGE_INPUT_END\nUse the .pdd/workflows/${s.name}/${stage.file} Markdown supplied in the saved context for this stage; do not replace it by reloading a mutable recipe file. Agent protocol ${stage.protocol}; required roles ${JSON.stringify(stage.requiredRoles)}. Write your handoff at handoffPath as JSON with exactly version:1,runId,stageId,issueUrl,inputRevision,summary,files:[{path,sha256,role}], optional testCommands:[[executable,...args]]. Use the exact supplied identities. Project files must exist, be ordinary contained files and match sha256. Roles: prompt,story,cases,implementation,tests,evidence,notes. A report protocol may use a substantive summary without project files; proposal/work/verify need real files. A proposal requires its declared roles and independent native project testCommands. A verify protocol must preserve the accepted expectations and use the accepted argv plan; the runner executes those tests itself. Do not claim PASS from native exit or prose. Complete the real files required for this stage, write the closed handoff, and report the stage result. PDD observes this owned background conversation and independently validates the exact handoff, current files and required tests. Report the stage result and stop; no manual native exit is required. A model turn, idle state or handoff write alone does not advance the workflow. Do not launch the next stage or terminate PDD/the parent process. Current and prior artifacts remain inspectable. Canonical issue URL: ${s.issue.url}.`;
}
async function runAgent(s, stage, r, directory, options, p) {
  if (typeof p.runHerdrStage !== 'function' || typeof p.inspectHerdrStage !== 'function' || typeof p.closeHerdrStage !== 'function')
    fail('Background native run, inspection and cleanup ports are required.');
  await validateInput(s, options, p);
  const context = s.context;
  await current(s, r, p);
  const handoffPath = join(directory, 'artifacts', `${stage.id}-${randomUUID()}.json`);
  const attemptId = randomUUID();
  const instructions = agentInstructions(s, stage, directory, attemptId, handoffPath, s.expected);
  s.pending = { kind: 'agent', stage: stage.id, attemptId, input: s.expected, handoffPath, backend: null, instructions,
    promptDigest: digest(`${context}\n\n# Current workflow stage\n${instructions}`), transport: null };
  const guard = stageGuard(s), portOptions = nativePorts(s, directory, r, options, p);
  await guard({ runId: s.runId, cwd: s.root }, async () => { s.pending.attachmentEpoch = attachmentEpoch(s); });
  record(s, directory, 'agent.intent');
  const previous = s.completed.filter(entry => entry.backend?.phase === 'closed').at(-1)?.backend;
  let outcome;
  try {
    outcome = await p.runHerdrStage({ runId: s.runId, stageId: stage.id, attemptId, agent: s.agent, cwd: r.root,
      context, instructions, backend: previous, checkpoint: portOptions.checkpoint }, portOptions);
    candidateIdentity(s, stage, outcome);
  } catch { return result(s, 'recovery_required', 'Background launch or delivery is uncertain; no automatic relaunch. Inspect the saved attempt.'); }
  s.pending.backend = structuredClone(outcome.backend); s.pending.transport = outcome;
  record(s, directory, 'agent.transport');
  if (outcome.state !== 'settled') return result(s, outcome.state === 'blocked' ? 'waiting' : 'recovery_required', outcome.reason || 'The original background stage needs inspection; no resend.');
  return acceptAgent(s, stage, r, directory, options, p, outcome);
}
async function acceptAgent(s, stage, r, directory, options, p, outcome) {
  const portOptions = nativePorts(s, directory, r, options, p);
  return portOptions.withStageGuard(outcome.backend, async () => {
    if (s.pending.attachmentEpoch !== attachmentEpoch(s)) {
      s.pending.attachmentEpoch = attachmentEpoch(s); s.pending.transport = null;
      record(s, directory, 'agent.candidate.invalidated_by_attach');
      return result(s, 'waiting', 'Attachment invalidated the earlier candidate. Resume with approve to inspect and validate the same original attempt afresh.');
    }
    const observed = await p.inspectHerdrStage({ backend: outcome.backend, cwd: r.root }, portOptions);
    candidateIdentity(s, stage, observed);
    if (observed.state !== 'settled' || !isDeepStrictEqual(observed.evidence, outcome.evidence))
      return result(s, 'recovery_required', 'Native activity or identity changed before validation; the earlier candidate was not accepted.');
    await validateInput(s, options, p);
    await assignedRepository(s.assignment, p);
    const outputInput = await fingerprint(r, p);
  let h;
  try { h = await handoff(s, stage, r, directory); await sourceValid(s, r);
    await git(p, r.root, 'merge-base', '--is-ancestor', s.pending.input.head, 'HEAD'); }
  catch (error) { return result(s, 'failed', error.message); }
  if (stage.protocol === 'verify') {
    const plan = s.accepted?.testCommands;
    if (!plan?.length || h.testCommands.length && !isDeepStrictEqual(plan, h.testCommands)) return result(s, 'failed', 'Verification must execute the actual accepted native test plan.');
    s.pending.testCommands = plan; s.pending.executionInput = await fingerprint(r, p);
    record(s, directory, 'test.intent');
    const checked = await runWorkflowTestCommands({ cwd: r.root, testCommands: plan }, p.commandPorts);
    h.checks = checked.results;
    s.pending.checks = checked.results;
    for (const check of checked.results) {
      p.stdout.write(String(check.stdout ?? '')); p.stderr.write(String(check.stderr ?? ''));
    }
    record(s, directory, checked.passed ? 'test.completed' : 'test.failed');
    if (!checked.passed) return result(s, 'failed', 'A real native project check failed or could not run.');
    if (!isDeepStrictEqual(s.pending.executionInput, await fingerprint(r, p)))
      fail('Native checks changed their execution input; the changed result is not verified.');
  }
  const { checks, ...originalHandoff } = h;
  if (!isDeepStrictEqual(originalHandoff, await handoff(s, stage, r, directory))) fail('The exact workflow handoff changed during validation or native checks.');
  await git(p, r.root, 'merge-base', '--is-ancestor', s.pending.input.head, 'HEAD');
  await sourceValid(s, r);
  await assertWorkflowArtifacts({ cwd: r.root, files: h.files });
  await assignedRepository(s.assignment, p);
  s.expected = await fingerprint(r, p);
  if (stage.protocol === 'proposal') s.proposal = { approval: stage.approval, files: h.files.filter(f => stage.requiredRoles.includes(f.role)), testCommands: h.testCommands };
  if (!isDeepStrictEqual(outputInput, await fingerprint(r, p))) fail('Stage output changed during validation; the changed result is not accepted.');
  const finalObservation = await p.inspectHerdrStage({ backend: observed.backend, cwd: r.root }, portOptions);
  candidateIdentity(s, stage, finalObservation);
  if (finalObservation.state !== 'settled' || !isDeepStrictEqual(finalObservation.evidence, observed.evidence))
    fail('Native state changed during validation; no acceptance or cleanup.');
  const evidenceRecord = { runId: s.runId, stageId: stage.id, attemptId: s.pending.attemptId,
    backend: finalObservation.backend, handoff: h, handoffSha256: digest(readFileSync(s.pending.handoffPath)),
    output: s.expected, accepted: s.accepted ?? null, checks: h.checks ?? [] };
  const acceptance = { runId: s.runId, stageId: stage.id, attemptId: s.pending.attemptId,
    promptDigest: s.pending.promptDigest, terminalId: finalObservation.backend.terminalId,
    evidenceDigest: digest(JSON.stringify(evidenceRecord)) };
  const verification = stage.protocol === 'verify' ? { output: s.expected, testCommands: s.accepted.testCommands,
    evidenceDigest: acceptance.evidenceDigest } : null;
  s.pending = { ...s.pending, kind: 'cleanup', backend: finalObservation.backend, handoff: h, acceptance, evidenceRecord, verification };
  record(s, directory, 'agent.accepted');
  return cleanupAgent(s, stage, r, directory, options, p, true);
  });
}
async function cleanupAgent(s, stage, r, directory, options, p, advance) {
  if (!advance) return result(s, 'waiting', 'The stage is accepted; resume with approve for its original owned cleanup.');
  const portOptions = nativePorts(s, directory, r, options, p);
  return portOptions.withStageGuard(s.pending.backend, async () => {
    await current(s, r, p);
    await assertWorkflowArtifacts({ cwd: r.root, files: s.pending.handoff.files });
    if (digest(JSON.stringify(s.pending.evidenceRecord)) !== s.pending.acceptance.evidenceDigest
      || digest(readFileSync(s.pending.handoffPath)) !== s.pending.evidenceRecord.handoffSha256)
      fail('The accepted stage evidence or closed handoff changed before cleanup.');
    if (s.pending.backend.phase !== 'closed') {
      if (s.pending.backend.phase !== 'candidate') return result(s, 'recovery_required', 'Original cleanup may already have happened. Inspect it; no blind repeat.');
      const closed = await p.closeHerdrStage({ backend: s.pending.backend, acceptance: s.pending.acceptance }, portOptions);
      if (closed.state !== 'closed' || closed.backend?.phase !== 'closed') return result(s, 'recovery_required', closed.reason || 'Owned cleanup is uncertain; no stage was resent.');
      if (!isDeepStrictEqual(closed.backend, s.pending.backend)) fail('Owned closure was not checkpointed with its exact actual identity.');
    }
    s.completed.push({ id: stage.id, kind: stage.kind, handoff: s.pending.handoff,
      revision: s.expected.head, backend: s.pending.backend, acceptance: s.pending.acceptance, verification: s.pending.verification });
    s.pending = null; s.index++; record(s, directory, 'agent.completed');
    return null;
  });
}

async function completePr(s, stage, intent, pr, directory) {
  s.completed.push({ id: stage.id, kind: stage.kind, pr, intent });
  s.pending = null; s.index++; record(s, directory, 'pr.completed');
}
async function makePr(s, stage, r, directory, p) {
  await current(s, r, p);
  if (stage.publication === 'verified') {
    const checked = s.completed.findLast(entry => s.definitions.find(definition => definition.id === entry.id)?.protocol === 'verify');
    const verification = checked?.verification, plan = s.accepted?.testCommands;
    if (!verification || !isDeepStrictEqual(verification.output, s.expected)
      || !isDeepStrictEqual(verification.testCommands, plan) || !plan?.length
      || checked.handoff?.checks?.length !== plan.length || checked.handoff.checks.some(check => check.exitCode !== 0)
      || verification.evidenceDigest !== checked.acceptance?.evidenceDigest)
      fail('Verified publication requires successful accepted checks for this exact current source revision and worktree.');
  }
  for (const merged of s.completed.filter(entry => entry.mergeCommit && (!stage.requiresMerge || entry.id === stage.requiresMerge)))
    await git(p, r.root, 'merge-base', '--is-ancestor', merged.mergeCommit, 'HEAD');
  const intent = await prepareWorkflowPr({ cwd: r.root, runId: s.runId, stageId: stage.id,
    repository: s.repo, baseBranch: s.base, bodyFile: join(directory, `pr-${stage.id}.md`) }, p.commandPorts);
  await current(s, r, p);
  s.pending = { kind: 'pr', stage: stage.id, intent }; record(s, directory, 'pr.intent');
  let outcome;
  try { outcome = await publishWorkflowPr({ cwd: r.root, intent }, p.commandPorts); }
  catch { return result(s, 'recovery_required', 'PR effect is uncertain; no blind resend.'); }
  if (['open', 'merged'].includes(outcome.state) && outcome.pr) {
    await current(s, r, p);
    await completePr(s, stage, intent, outcome.pr, directory); return null;
  }
  return result(s, outcome.state === 'failed' ? 'failed' : 'recovery_required', outcome.message);
}
async function reconcile(s, r, directory, options, p, canAdvance) {
  const stage = s.definitions[s.index];
  if (s.pending.kind === 'cleanup') return cleanupAgent(s, stage, r, directory, options, p, canAdvance);
  if (s.pending.kind === 'agent') {
    if (!s.pending.backend || typeof p.inspectHerdrStage !== 'function') return result(s, 'recovery_required', 'Original native identity is incomplete; no replacement was started.');
    const portOptions = nativePorts(s, directory, r, options, p);
    let seen;
    if (canAdvance && ['start_intent', 'ready'].includes(s.pending.backend.phase)) {
      if (typeof p.runHerdrStage !== 'function') fail('The original first-dispatch port is unavailable.');
      const instructions = s.pending.instructions ?? agentInstructions(s, stage, directory,
        s.pending.attemptId, s.pending.handoffPath, s.pending.input);
      if (typeof instructions !== 'string' || digest(`${s.context}\n\n# Current workflow stage\n${instructions}`) !== s.pending.promptDigest)
        fail('The original stage request bytes cannot be proved; no first dispatch was attempted.');
      await current(s, r, p);
      try {
        seen = await p.runHerdrStage({ runId: s.runId, stageId: stage.id, attemptId: s.pending.attemptId,
          agent: s.agent, cwd: r.root, context: s.context, instructions, backend: s.pending.backend,
          checkpoint: portOptions.checkpoint }, portOptions);
        candidateIdentity(s, stage, seen);
      } catch { return result(s, 'recovery_required', 'Original first dispatch is unconfirmed; preserve this same attempt for inspection.'); }
      s.pending.backend = structuredClone(seen.backend); s.pending.transport = seen;
      record(s, directory, 'agent.transport');
    } else {
      seen = await p.inspectHerdrStage({ backend: s.pending.backend, cwd: r.root }, portOptions);
      candidateIdentity(s, stage, seen);
    }
    if (seen.state !== 'settled') return result(s, seen.state === 'blocked' ? 'waiting' : 'recovery_required', seen.reason || 'Original native stage remains unresolved.');
    if (!canAdvance) return result(s, 'waiting', 'Original stage has a candidate handoff. Resume with approve to validate that same attempt; inspection alone starts nothing.');
    return acceptAgent(s, stage, r, directory, options, p, seen);
  }
  try {
    let outcome = await reconcileWorkflowPr({ cwd: r.root, intent: s.pending.intent }, p.commandPorts);
    if (outcome.state === 'recovery_required' && canAdvance) {
      await current(s, r, p);
      record(s, directory, 'pr.unpublished_retry_intent');
      outcome = await publishWorkflowPr({ cwd: r.root, intent: s.pending.intent, unpublishedOnly: true }, p.commandPorts);
    }
    if (!['open', 'merged'].includes(outcome.state) || !outcome.pr)
      return result(s, 'recovery_required', outcome.message || 'The exact original PR was not proved; no effect was repeated.');
    await current(s, r, p);
    await completePr(s, stage, s.pending.intent, outcome.pr, directory);
    return result(s, 'waiting', 'Original PR reconciled. Resume without a decision to observe merge, or with approve to advance.');
  } catch { return result(s, 'recovery_required', 'Original PR recovery is unconfirmed; preserve this same intent for inspection.'); }
}
async function advance(s, r, directory, options, p, decision, initial) {
  authority(s, r);
  const priorProposal = !s.pending ? s.proposal : null;
  const next = s.definitions[s.index];
  if (!s.pending && options.decision === 'approve' && next?.requiresMerge
    && s.completed.some(entry => entry.id === next.requiresMerge && entry.mergeCommit)) {
    const fresh = await fingerprint(r, p);
    if (!isDeepStrictEqual(fresh, s.expected)) {
      if (await git(p, r.root, 'status', '--porcelain=v1', '--untracked-files=all')) fail('The assigned code worktree must be clean and preserve accepted artifacts.');
      await sourceValid(s, r);
      const merged = s.completed.find(entry => entry.id === next.requiresMerge);
      await git(p, r.root, 'merge-base', '--is-ancestor', merged.mergeCommit, 'HEAD');
      const previous = s.expected; s.expected = fresh;
      s.inputTransitions ??= []; s.inputTransitions.push({ previous, current: fresh, reason: 'merged_proposal_base' });
      record(s, directory, 'human.merged_base.accepted');
    }
  }
  if (s.pending?.kind === 'agent') { await sourceValid(s, r); await git(p, r.root, 'merge-base', '--is-ancestor', s.pending.input.head, 'HEAD'); }
  else await current(s, r, p);
  if (s.pending) {
    const stop = await reconcile(s, r, directory, options, p, decision === 'approve');
    if (stop) return stop;
  }
  let canAdvance = initial || decision === 'approve' || decision === 'skip';
  let choice = decision;
  while (s.index < s.definitions.length) {
    await current(s, r, p);
    const stage = s.definitions[s.index];
    if (choice === 'skip' && !stage.optional) fail('Only an optional current stage may be skipped.');
    if (stage.optional) {
      let selected = s.optional?.[stage.id];
      if (!selected) {
        if (!choice) return result(s, 'waiting', 'Optional step: resume with --decision approve to run it or --decision skip to omit it.');
        s.optional ??= {}; selected = { decision: choice, input: s.expected };
        s.optional[stage.id] = selected; record(s, directory, 'optional.decision');
      }
      if (!['approve', 'skip'].includes(selected.decision) || !isDeepStrictEqual(selected.input, s.expected))
        fail('The saved optional decision does not match the current input.');
      if (selected.decision === 'approve' && choice === 'skip') fail('A durable optional approval cannot be replaced; inspect the saved choice before effects.');
      choice = undefined;
      if (selected.decision === 'skip') {
        s.completed.push({ id: stage.id, kind: stage.kind, skipped: true, input: selected.input }); s.index++;
        record(s, directory, 'optional.skipped'); continue;
      }
    }
    if (stage.kind === 'human') {
      if (choice !== 'approve') return result(s, 'waiting', 'Review the exact current proposal artifacts, independent expectations and test plan. Resume with --decision approve to accept this input.');
      if (!s.proposal?.files.length || !s.proposal.testCommands.length) fail('A complete independent proposal and test plan is required before approval.');
      await assertWorkflowArtifacts({ cwd: r.root, files: s.proposal.files });
      s.accepted = { ...s.proposal, input: s.expected };
      s.completed.push({ id: stage.id, kind: stage.kind, input: s.expected }); s.index++;
      record(s, directory, 'human.approved'); choice = undefined; continue;
    }
    if (stage.kind === 'merge') {
      const prior = s.completed.find(step => step.id === stage.prStage);
      if (prior?.skipped) { s.completed.push({ id: stage.id, kind: stage.kind, skipped: true }); s.index++; record(s, directory, 'merge.skipped'); continue; }
      if (!prior?.pr) fail('No original PR is saved for this merge step.');
      const outcome = await reconcileWorkflowPr({ cwd: r.root, intent: prior.intent }, p.commandPorts);
      if (outcome.pr && (outcome.pr.number !== prior.pr.number || outcome.pr.url !== prior.pr.url))
        return result(s, 'recovery_required', 'The observed PR is not the saved original PR number and URL; no merge accepted.');
      if (outcome.state === 'open') return result(s, 'waiting', `Waiting for actual merge of ${prior.pr.url}. No merge action performed.`);
      if (outcome.state !== 'merged' || !outcome.pr) return result(s,
        outcome.state === 'closed' || outcome.state === 'failed' ? 'failed' : 'recovery_required', outcome.message);
      const mergeCommit = outcome.pr.mergeCommit;
      if (!/^[a-f0-9]{40,64}$/.test(mergeCommit ?? '')) fail('Actual merged revision was not supplied by GitHub.');
      s.completed.push({ id: stage.id, kind: stage.kind, pr: outcome.pr, mergeCommit }); s.index++;
      record(s, directory, 'merge.observed');
      if (!canAdvance) return result(s, s.index === s.definitions.length ? 'completed' : 'waiting', 'Actual merge observed; no new stage was launched. Resume with approve to advance.');
      continue;
    }
    if (!canAdvance) return result(s, 'waiting', 'Saved input is current. Resume with --decision approve to advance; inspection alone launches nothing.');
    if (s.proposal?.approval === 'next-advance' && !s.accepted) {
      if (s.proposal !== priorProposal || decision !== 'approve')
        return result(s, 'waiting', 'Review the independent proposal and test plan; resume with approve to advance.');
      if (!s.proposal.files.length || !s.proposal.testCommands.length) fail('A complete independent proposal and test plan is required.');
      s.accepted = { ...s.proposal, input: s.expected }; record(s, directory, 'proposal.accepted');
    }
    if (stage.requiresMerge) {
      const merged = s.completed.find(entry => entry.id === stage.requiresMerge);
      if (!merged?.skipped) {
        if (!merged?.mergeCommit) fail('The required original PR merge is not recorded.');
        try { await git(p, r.root, 'merge-base', '--is-ancestor', merged.mergeCommit, 'HEAD'); }
        catch { return result(s, 'waiting', 'Work needs the exact merged proposal revision in its assigned branch. No checkout or base rewrite was performed.'); }
      }
    }
    const stopped = stage.kind === 'agent' ? await runAgent(s, stage, r, directory, options, p)
      : await makePr(s, stage, r, directory, p);
    if (stopped) return stopped;
    choice = undefined;
  }
  return result(s, 'completed', 'All listed steps completed with their recorded artifacts, checks and merge observations.');
}
function canonicalOverview(packageRoot) {
  const root = realpathSync(packageRoot), path = join(root, 'docs', 'workflows.md');
  requireDirectory(join(root, 'docs'));
  journalFile(path);
  return readFileSync(path, 'utf8');
}
function snapshotDigest(input) {
  return digest(JSON.stringify({ runId: input.runId, sourceRoot: input.sourceRoot,
    definition: input.definition, baseContext: input.baseContext, overview: input.overview }));
}
function inputDirectory(commonDir, runId) { return join(commonDir, 'pdd', 'workflow-inputs', runId); }
function saveInput(input, commonDir) {
  ensureDirectory(join(commonDir, 'pdd'));
  const parent = join(commonDir, 'pdd', 'workflow-inputs'); ensureDirectory(parent);
  const directory = inputDirectory(commonDir, input.runId);
  if (existsSync(directory)) fail('Run input identity already exists; inspect it without overwriting.');
  ensureDirectory(directory); syncDirectory(parent);
  durable(join(directory, 'input.jsonl'), { ...input, digest: snapshotDigest(input) });
}
function readInput(commonDir, runId) {
  const directory = inputDirectory(commonDir, runId); requireDirectory(directory);
  const path = join(directory, 'input.jsonl'); journalFile(path);
  const bytes = readFileSync(path, 'utf8');
  if (!bytes.endsWith('\n') || bytes.trimEnd().split('\n').length !== 1) fail('Saved run input is incomplete.');
  const input = json(bytes);
  if (input.runId !== runId || input.digest !== snapshotDigest(input)) fail('Saved workflow/context snapshot changed.');
  return input;
}
async function validateInput(s, options, p) {
  const input = readInput(s.assignment.commonDir, s.runId);
  if (input.digest !== s.inputDigest || !isDeepStrictEqual(input.definition, s.definition)) fail('Saved workflow snapshot does not match its run.');
  const live = loadWorkflowDefinition({ name: s.name, cwd: s.assignment.sourceRoot, packageRoot: options.packageRoot });
  if (!isDeepStrictEqual(live, s.definition)) fail('Workflow definition or Markdown source changed; no saved run input was replaced.');
  const base = await p.loadGuidance({ packageRoot: options.packageRoot, cwd: s.assignment.sourceRoot, workflows: false });
  if (base !== input.baseContext || canonicalOverview(options.packageRoot) !== input.overview) fail('Canonical guide/skill/context changed; the saved context was not replaced.');
  const context = stageContext(input, s.root);
  if (s.context !== context || s.contextDigest !== digest(context)) fail('Saved full stage context changed.');
}
function stageContext(input, cwd) {
  const base = input.baseContext.replace(`Current project: ${input.sourceRoot}`, `Original source project: ${input.sourceRoot}`);
  return [base, `Current assigned project: ${cwd}`, input.overview,
    `Selected workflow snapshot: ${input.definition.name} / ${input.definition.digest}`,
    ...input.definition.files.map(file => `--- .pdd/workflows/${input.definition.name}/${file.path} ---\n${file.content}`)].join('\n\n');
}
async function assignmentFor(options, p, resume, runId, binding) {
  const module = (!p.allocateIssueWorktree || !p.lookupIssueWorktree) ? await import('./workflow-worktree.mjs') : null;
  const response = resume
    ? await (p.lookupIssueWorktree ?? module.lookupIssueWorktree)({ cwd: options.cwd, runId }, p.commandPorts)
    : await (p.allocateIssueWorktree ?? module.allocateIssueWorktree)({ cwd: options.cwd,
      repository: binding.repository, issueNumber: binding.issue.number, runId,
      workflowName: options.name, baseRef: `refs/remotes/origin/${binding.defaultBranch}` }, p.commandPorts);
  return response?.assignment ? response : { ...response, assignment: null };
}
async function conflictingAssignment(source, binding, options, p, provided) {
  if (provided) return provided;
  // Allocation may report the exclusive issue conflict without a ready assignment.
  // The documented claim discovers only a run ID; helper lookup proves custody.
  let parent = source.commonDir;
  for (const part of ['pdd', 'worktree-assignments', 'issues']) {
    parent = join(parent, part); requireDirectory(parent);
  }
  const path = join(parent, `${binding.issue.number}.json`), before = lstatSync(path);
  if (!before.isFile() || before.isSymbolicLink() || before.nlink !== 2 || realpathSync(path) !== path)
    fail('The original issue claim is not an ordinary owned metadata record.');
  const fd = openSync(path, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
  let claim;
  try {
    const opened = fstatSync(fd);
    if (opened.dev !== before.dev || opened.ino !== before.ino || opened.nlink !== 2 || opened.size > 65536)
      fail('The original issue claim changed before discovery.');
    const raw = readFileSync(fd, 'utf8'), after = lstatSync(path), finished = fstatSync(fd);
    if (!raw.endsWith('\n') || [after, finished].some(stat => stat.dev !== opened.dev || stat.ino !== opened.ino
      || stat.nlink !== 2 || stat.size !== opened.size || stat.mtimeMs !== opened.mtimeMs || stat.ctimeMs !== opened.ctimeMs))
      fail('The original issue claim changed during discovery.');
    claim = json(raw);
  } finally { closeSync(fd); }
  if (!UUID.test(claim.runId ?? '') || claim.commonDir !== source.commonDir
    || claim.repository !== binding.repository || claim.issueNumber !== binding.issue.number)
    fail('The original issue claim does not match this repository and issue.');
  const found = await assignmentFor(options, p, true, claim.runId);
  if (found.state !== 'ready' || !found.assignment || found.assignment.runId !== claim.runId
    || found.assignment.commonDir !== source.commonDir || found.assignment.repository !== binding.repository
    || found.assignment.issueNumber !== binding.issue.number)
    fail('The original claimed worktree is not ready; inspect that saved run without allocating again.');
  return found.assignment;
}
async function assignedRepository(assignment, p) {
  if (!assignment || assignment.version !== 1 || !UUID.test(assignment.runId)
    || !text(assignment.repository) || !text(assignment.worktreePath)) fail('A verified issue worktree assignment is required.');
  const r = await repository(assignment.worktreePath, p);
  if (r.root !== assignment.worktreePath || r.gitDir !== assignment.gitDir || r.commonDir !== assignment.commonDir
    || await git(p, r.root, 'symbolic-ref', '--quiet', '--short', 'HEAD') !== assignment.branch)
    fail('Actual issue worktree identity changed.');
  await git(p, r.root, 'merge-base', '--is-ancestor', assignment.baseSha, 'HEAD');
  return r;
}
async function execute(options, ports, resume) {
  const p = dependencies(ports);
  let s, unlock;
  try {
    if (!text(options?.packageRoot) || typeof p.loadGuidance !== 'function') fail('A package root and canonical guidance port are required.');
    if (resume && (!UUID.test(options.runId ?? '') || options.decision !== undefined && !['approve', 'skip'].includes(options.decision))) fail('Supply a UUIDv4 run and optional approve/skip decision.');
    if (!resume && !['codex', 'claude'].includes(options.agent ?? 'codex')) fail('Choose codex or claude.');
    let assignment, input, r, directory;
    if (resume) {
      const found = await assignmentFor(options, p, true, options.runId);
      if (found.state !== 'ready' || !found.assignment) return result({ runId: options.runId }, 'recovery_required', found.message || 'Original worktree assignment is not proved.');
      assignment = found.assignment; r = await assignedRepository(assignment, p);
      directory = join(r.gitDir, 'pdd', 'workflows', options.runId);
      // Lookup is read-only. Missing journals are never filled with a new stage attempt.
      unlock = lock(join(r.gitDir, 'pdd', 'workflows'));
      s = readSaved(directory);
      if (!isDeepStrictEqual(s.assignment, assignment)) fail('Saved assignment identity changed.');
      progress(s, 'run.loaded');
      const binding = await resolveWorkflowIssue({ cwd: r.root, issue: s.issue.url }, p.commandPorts);
      r.repo = binding.repository; r.base = binding.defaultBranch;
      await validateInput(s, options, p);
      return await advance(s, r, directory, options, p, options.decision, false);
    }
    const source = await repository(options.cwd, p);
    const definition = loadWorkflowDefinition({ name: options.name, cwd: source.root, packageRoot: options.packageRoot });
    const binding = await resolveWorkflowIssue({ cwd: source.root, issue: options.issue }, p.commandPorts);
    const runId = randomUUID();
    const baseContext = await p.loadGuidance({ packageRoot: options.packageRoot, cwd: source.root, workflows: false });
    if (!text(baseContext)) fail('Full guide-first context is unavailable.');
    input = { runId, sourceRoot: source.root, definition, baseContext, overview: canonicalOverview(options.packageRoot) };
    // Preserve complete guide and recipe bytes BEFORE the allocator can create a checkout.
    saveInput(input, source.commonDir);
    s = { runId, name: options.name, definitions: definition.stages, index: 0 };
    const allocated = await assignmentFor({ ...options, cwd: source.root }, p, false, runId, binding);
    if (allocated.state === 'conflict' && allocated.assignment?.runId !== runId) {
      const original = await conflictingAssignment(source, binding, options, p, allocated.assignment);
      if (!original || original.commonDir !== source.commonDir || original.repository !== binding.repository
        || original.issueNumber !== binding.issue.number) return result(s, 'recovery_required', allocated.message || 'Issue assignment conflict.');
      s = { runId: original.runId };
      unlock = lock(join(original.gitDir, 'pdd', 'workflows'));
      const prior = readSaved(join(original.gitDir, 'pdd', 'workflows', original.runId));
      if (!isDeepStrictEqual(prior.assignment, original)) fail('Saved original assignment changed.');
      return result(prior, prior.pending ? 'recovery_required' : 'waiting', 'This issue already has its original assigned run. Resume that run; no duplicate was launched.');
    }
    if (allocated.state !== 'ready' || !allocated.assignment) return result(s, 'recovery_required', allocated.message || 'Worktree allocation is uncertain; no native attempt started.');
    assignment = allocated.assignment;
    if (assignment.runId !== runId || assignment.repository !== binding.repository || assignment.issueNumber !== binding.issue.number
      || assignment.workflowName !== options.name || assignment.sourceRoot !== source.root || assignment.commonDir !== source.commonDir)
      fail('Worktree allocation does not match the requested issue/run.');
    r = await assignedRepository(assignment, p); r.repo = binding.repository; r.base = binding.defaultBranch;
    unlock = lock(join(r.gitDir, 'pdd', 'workflows'));
    directory = join(r.gitDir, 'pdd', 'workflows', runId);
    if (existsSync(directory)) fail('Run journal already exists; do not overwrite it.');
    ensureDirectory(directory); ensureDirectory(join(directory, 'artifacts')); syncDirectory(directory);
    const context = stageContext(input, r.root);
    s = { version: 2, seq: 0, runId, name: options.name, agent: options.agent ?? 'codex', root: r.root, gitDir: r.gitDir,
      repo: r.repo, base: r.base, issue: binding.issue, assignment, definition, definitions: definition.stages,
      inputDigest: snapshotDigest(input), context, contextDigest: digest(context), index: 0, completed: [],
      expected: await fingerprint(r, p), pending: null };
    record(s, directory, 'run.started');
    await validateInput(s, options, p);
    return await advance(s, r, directory, options, p, undefined, true);
  } catch (error) { return result(s, error.code === 'WORKFLOW_STAGE_BUSY' ? 'waiting' : 'failed', error.message || 'Workflow failed; inspect saved state before another effect.'); }
  finally { unlock?.(); }
}
export async function runWorkflow(options, ports) { return progressScope.run(ports?.onProgress, () => execute(options, ports, false)); }
export async function resumeWorkflow(options, ports) { return progressScope.run(ports?.onProgress, () => execute(options, ports, true)); }

export async function attachWorkflow(options, ports) {
  const p = dependencies(ports);
  let s;
  try {
    if (!UUID.test(options?.runId ?? '')) fail('Supply the saved UUIDv4 run.');
    if (!text(options.packageRoot) || typeof p.loadGuidance !== 'function') fail('A package root and canonical guidance port are required.');
    const found = await assignmentFor(options, p, true, options.runId);
    if (found.state !== 'ready' || !found.assignment) return result({ runId: options.runId }, 'recovery_required', found.message || 'Original assignment is not proved.');
    const r = await assignedRepository(found.assignment, p);
    s = readSaved(join(r.gitDir, 'pdd', 'workflows', options.runId));
    if (!isDeepStrictEqual(s.assignment, found.assignment)) fail('Saved assignment changed.');
    if (!s.pending?.backend || s.pending.backend.phase === 'closed') return result(s, 'waiting', 'No live stage is retained. Completed stage history is archived; no conversation was started.');
    if (s.pending.kind === 'cleanup') return result(s, 'waiting', 'The stage is already accepted for cleanup; it is archived for workflow purposes.');
    if (typeof p.attachHerdrStage !== 'function') fail('Active native attachment is unavailable.');
    const guard = stageGuard(s);
    return await guard(s.pending.backend, async () => {
      // Acceptance/cleanup may have won the guard after the initial lookup.
      s = readSaved(join(r.gitDir, 'pdd', 'workflows', options.runId));
      if (!isDeepStrictEqual(s.assignment, found.assignment)) fail('Saved assignment changed.');
      await assignedRepository(s.assignment, p);
      if (!s.pending?.backend || s.pending.backend.phase === 'closed' || s.pending.kind === 'cleanup')
        return result(s, 'waiting', 'The stage is already accepted or archived. No live conversation was attached.');
      await validateInput(s, options, p);
      attachmentEpoch(s, true);
      const code = await p.attachHerdrStage({ backend: s.pending.backend }, { withStageGuard: guard });
      return result(s, code === 0 ? 'waiting' : 'recovery_required', code === 0
        ? 'Detached from the original active stage. Resume its saved run to inspect; attachment does not certify stage success.'
        : 'The exact original stage could not be attached. No replacement was started.');
    });
  } catch (error) { return result(s, 'recovery_required', error.message); }
}
