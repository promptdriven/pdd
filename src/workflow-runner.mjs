import { recordBugCause } from './workflow-bug-cause.mjs';
import {routeQuestionFor, idleParkingBlocker, idleSince, interpreterWaitFor, blockerFor} from './autopilot-parking.mjs';
import { selectAutopilotBase } from './autopilot-base.mjs';
import { runTestSuite, readSuiteProgress, suiteStatusWords } from './test-suite-queue.mjs';
import { classifyStuckCause, environmentRecovery, environmentStatus, environmentWakeTag, environmentHealthy, ENVIRONMENT_BACKOFF } from './autopilot-environment.mjs';
import { launchProfile, selectLaunchProfile, validLaunchProfile } from './workflow-launch-profile.mjs';
import { validateSnapshot } from './metrics-store.mjs';
import { findNativeSessions } from './approval-evidence.mjs';
import { projectIssueGraph } from './issue-dependencies.mjs';
import { sortClosingReferences } from './issue-sort.mjs';
import { readDependencySnapshot, createDependencyReadPorts, recoverCoordinatorClaim, releaseParkedClaim } from './issue-dependencies-github.mjs';
// Generated from prompts/cli/workflow-runner.prompt.md (sha256: de77aa929765fb52bf178b9996f1f56b8abc931079ddf84a2f2b0bdf3e4b8f5e).
import { approvalActor, readSaidWords, readApprovalPolicy, readPromptApprovals, recordPromptApproval } from './approval-policy.mjs';
import { approvePromptText } from './prompt-approve.mjs';
import { spawnSync, execFile as execFileCallback } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { constants, openSync, closeSync, fsyncSync, unlinkSync, existsSync, lstatSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, renameSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';

import * as nativeDeliveryFiles from 'node:fs';
import { homedir, hostname, tmpdir } from 'node:os';
import { dirname, isAbsolute, join, resolve } from 'node:path';
import { createInterface } from 'node:readline/promises';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { PUBLIC_COMMAND_ROUTES } from './command-catalog.mjs';
import { readWorkflowAreas } from './workflow-areas.mjs';
import { resolveWorkflowIssue, prepareWorkflowPr, publishWorkflowPr, reconcileWorkflowPr, readWorkflowPrChecker, readWorkflowPrStatus } from './workflow-github.mjs';
import { allocateIssueWorktree, releaseIssueClaim } from './workflow-worktree.mjs';
import { allRuns, currentChat, gitContext, listRuns, readRun, readRunOwnership, resolveRun, runDirFor, runForWorktree, updateRun, updateRunCosts, writeRun } from './workflow-runs.mjs';
import { armSavedWorkerCompletion } from './workflow-worker-completion.mjs';
import { startChat, sendToChat, herdrCommand, chatSession, chatHealth, openChat, rebuildClosedChat, assertRestartCaller, restartChat, validSessionId, closeFinishedChats, finishedChats, finishedAt, paneUsage, ensurePaneBudget, countReasons, mergeReasonCounts, reasonWords, expandHome, homeVariable, isFolder, observeLifecycle, applyLifecycle, launchAnchor, sessionEvidenceDue, ownSession, observedSession, START_GRACE_MS, removeStaleLoginFiles } from './workflow-chat.mjs';
import { samePath } from './workflow-herdr-layout.mjs';
import { workflowAgentEntry } from './workflow-agents.mjs';
import { captureSource, findTests, gitFiles, interfaceBlocks, interfaceSchemaProblems, isStoryPath, proseSha256 } from './runtime-preflight.mjs';
import { storyLines, PROMPT_TESTS_LABEL, PROMPT_TESTS_WORDS } from './runtime-output.mjs';
import { PDD_HERDR_SESSION } from './workflow-herdr-layout.mjs';
import { causeText } from './runtime-output.mjs';
import { approvalRecords, preparePrEvidence } from './workflow-pr-evidence.mjs';
import { validateProofRecord } from './workflow-prove.mjs';
import { readRunResults, resultLines, usableResult, noResultLine, NO_VERDICT, prepareNativeEvidence, savedCheckCause, savedLostCheck } from './workflow-results.mjs';
import { collectTestInventory } from './workflow-inventory.mjs';
import {readSmallChangeChecklist} from './workflow-small-change.mjs';
import {adoptReplayCorpus,REPLAY_POLICY,sourceFingerprint as gitFingerprint,pinReplayVectors,pinRunAnchor,readReplayEvidence,readFormalEvidence,formatFormalEvidence,formatReplayEvidence} from './workflow-replay.mjs';
import { DETAILS_OPEN, TOP_NOTE, balancedDetails, closingInert, detailsOf, pr1Order, prArea, prStatus, readPrFields, readableNextLines, readablePrBody, readablePrTitle, readablePrTop, sameReadableTop, userStory } from './workflow-pr-body.mjs';
import { nativeGithubCounter } from './github-calls.mjs';
import { storyCard, storyFingerprint, fingerprintChanges, fullCheckPass } from './workflow-story-card.mjs';

import { applyCostMeasurement, captureClosedCi, costReport } from './cost-ledger.mjs';

export const WORKFLOW_CAPABILITIES = Object.freeze(['prompt-reentry', 'route-interface-drafting', 'route-code-only-checker']);

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const CHANGE_PREFIX = 'The person asks for changes';
const ANSWER_PREFIX = 'The person answers your question';
// Try links (/s/<token>/) open a live session; they never go into a PR body. Report links (/r/) stay.
const redactTry = text => String(text).replace(/https?:\/\/[^\s)<>\]"'`]*?\/s\/[^/\s)<>\]"'`]+(?:\/[^\s)<>\]"'`]*)?/g, '(Try link removed)');
const ordinary = promisify(execFileCallback);
function execute(file, args, { cwd, input, ...options } = {}) {
  if (input === undefined) return ordinary(file, args, { cwd, ...options });
  return new Promise((resolve, reject) => {
    const child = execFileCallback(file, args, { cwd, ...options }, (error, stdout, stderr) => {
      if (error) { error.stdout = stdout; error.stderr = stderr; reject(error); return; }
      resolve({ stdout, stderr });
    });
    child.stdin.on('error', error => { if (error.code !== 'EPIPE') reject(error); });
    child.stdin.end(input);
  });
}
const shell = value => /^[A-Za-z0-9_@%+=:,./-]+$/.test(value) ? value : `'${value.replace(/'/g, `'\\''`)}'`;
const oneLine = value => String(value ?? '').replace(/\s+/g, ' ').trim();
// A chat failure as `code: reason` from the first message line, with the code only once; a bare code when there are no other words.
const firstLine = value => oneLine(String(value ?? '').split('\n')[0]);
const failureReason = error => {
  const code = oneLine(error?.code ?? 'error'), text = firstLine(error?.message), rest = text.startsWith(`${code}: `) ? text.slice(code.length + 2) : text;
  return !rest || rest === code ? code : `${code}: ${rest}`;
};
// The later message lines, such as the escaped expected and observed values of a Herdr layout identity refusal.
const failureDetails = error => String(error?.message ?? '').split('\n').slice(1).map(oneLine).filter(Boolean);
// A step summary keeps its line breaks (0.1.6: the chat pastes one Prompt tests line per line); blank lines go.
const keepLines = value => String(value ?? '').split('\n').map(oneLine).filter(Boolean).join('\n');
const done = message => ({ exitCode: 0, message });
const fail = message => ({ exitCode: 1, message });
const ended = run => ['cancelled', 'completed'].includes(run.state);
const isAgentSession = env => Boolean(env.PDD_AGENT_SESSION || env.CLAUDECODE || env.CODEX_THREAD_ID);
// About max characters at a word end, never inside a URL: a URL that crosses the end stays whole (0.1.6 tester: status
// showed "report https://ru").
function clip(text, max) {
  if (text.length <= max) return text;
  const url = [...text.matchAll(/https?:\/\/\S+/g)].find(match => match.index < max && match.index + match[0].length > max);
  const end = url ? url.index + url[0].length : /\s/.test(text[max]) ? max : text.slice(0, max).replace(/\s+\S*$/, '').length;
  // A space keeps the "…" out of a link that ends the cut text.
  return end >= text.length ? text : `${text.slice(0, end).trimEnd()}${url ? ' ' : ''}…`;
}
// The chat's open question. One asked before the current gate opened was answered when that gate opened (0.1.6 tester:
// status showed "Do you approve … so PDD can open PR 1?" after PR 1 was open).
const openQuestion = run => run.question && !(run.gate && run.question.at < run.gate.at) ? run.question : null;
const listed = items => items.length > 1 ? `${items.slice(0, -1).join(', ')} and ${items.at(-1)}` : items[0];
// A plain approval sent with changes (0.1.6 tester: "I approve. The Story and the prompt look good now." reached the chat as
// a change request, and the chat could not approve with it). An approval word with a change word is a change request.
const APPROVAL = /^\W*(?:(?:yes|ok(?:ay)?)\W+)?(?:i\W+)?(?:approve[ds]?|lgtm|looks good\W+(?:i\W+)?approve[ds]?)\b/i;
const CHANGE_WORDS = /\b(?:but|however|except|instead|change[ds]?|rename[ds]?|add|remove|delete|fix|use|make|move|replace|drop|update|should|need|must|want|not|don'?t|without|only)\b/i;
const looksLikeApproval = text => APPROVAL.test(text) && !CHANGE_WORDS.test(text.replace(APPROVAL, ''));

const shellQuote = value => "'" + String(value).replaceAll("'", "'\\''") + "'";
function paneOwners(rows, runs) {
  const owners = {working: 0, parked: 0, done: 0, unowned: 0}, chats = new Set(), shells = new Set(), refs = new Set();
  const matches = (pane, saved, workspaceId = saved?.workspaceId) => pane.workspace_id === workspaceId
    && pane.tab_id === saved?.tabId && pane.pane_id === saved?.paneId;
  const ordered = [...runs].sort((a,b) => Number(ended(a)) - Number(ended(b)));
  for (const pane of rows) {
    const run = ordered.find(run => (run.chats ?? []).some(chat => matches(pane,chat))
      || matches(pane,run.layout?.root ?? run.layout,run.layout?.workspaceId));
    if (!run) { owners.unowned++; continue; }
    owners[ended(run) ? 'done' : run.parking?.phase === 'parked' ? 'parked' : 'working']++;
    if ((run.chats ?? []).some(chat => matches(pane,chat))) chats.add(pane.pane_id);
    else shells.add(pane.pane_id);
    refs.add(`${run.repo}#${run.number} (${String(run.runId ?? 'unknown').slice(0,8)})`);
  }
  return {owners, chats, shells, refs};
}
function describePaneOwners(rows, ports) {
  const {owners, chats, shells, refs} = paneOwners(rows, allRuns({cancelled:true},ports));
  return `Open: ${chats.size} run chats (${[...refs].join(', ') || 'none'}), ${shells.size} run shells, ${owners.unowned} other panes. By run state: ${owners.working} working, ${owners.parked} parked, ${owners.done} done, ${owners.unowned} unowned.`;
}
function deps(ports = {}) {
  const env = ports.env ?? process.env;
  // The native runner records each gh call in the GitHub call ledger of its repository.
  const execFile = ports.execFile ?? nativeGithubCounter((file, args, options = {}) => execute(file, args, { encoding: 'utf8', maxBuffer: 16 * 1024 * 1024, ...options }), { env });
  return { ...ports, env, execFile, commandPorts: ports.execFile ? { execFile: ports.execFile } : {}, now: ports.now ?? Date.now, randomUUID: ports.randomUUID ?? randomUUID,
    isTTY: ports.isTTY ?? Boolean(process.stdin.isTTY && process.stderr.isTTY), say: ports.say ?? (() => {}), describePaneOwners: ports.describePaneOwners ?? (rows=>describePaneOwners(rows,ports)), sweepIdle: ports.sweepIdle ?? (options => sweepIdleRuns(options, {...ports, progressGuard: undefined})), sweepFinished: ports.sweepFinished ?? (options => tidyRuns(options, {...ports, progressGuard: undefined})) };
}
// This run lock is independent of the shared Herdr layout lock. Never wait on a live owner.
const lockProblem = cause => Object.assign(new Error('Another open operation holds this run, or its ownership cannot be verified. Wait for it to finish and retry.', cause ? { cause } : undefined), { code: 'run_busy' });
function readLock(path) {
  if (!lstatSync(path).isFile() || lstatSync(path).size > 4096) throw lockProblem();
  const fd = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_NONBLOCK);
  try {
    const value = JSON.parse(readFileSync(fd, 'utf8'));
    if (Object.keys(value).some(key => !['pid', 'token'].includes(key)) || !Number.isSafeInteger(value.pid) || value.pid < 1 || !validSessionId(value.token)) throw lockProblem();
    return value;
  } finally { closeSync(fd); }
}
const sameOwner = (a, b) => a.pid === b.pid && a.token === b.token;
function deadOwner(owner) {
  try { process.kill(owner.pid, 0); return false; } catch (error) { if (error.code === 'ESRCH') return true; throw lockProblem(); }
}
export function acquireRunLock(runDir, filename = 'chat-replacement.lock') {
  const path = join(runDir, filename), claim = `${path}.claim`, owner = { pid: process.pid, token: randomUUID() };
  const create = () => {
    const fd = openSync(path, 'wx', 0o600);
    try { writeFileSync(fd, JSON.stringify(owner)); fsyncSync(fd); } finally { closeSync(fd); }
  };
  try { create(); } catch (error) {
    if (error.code !== 'EEXIST') throw lockProblem(error);
    let prior, claimFd;
    try {
      prior = readLock(path);
      if (!deadOwner(prior)) throw lockProblem();
      claimFd = openSync(claim, 'wx', 0o600);
      if (!sameOwner(prior, readLock(path)) || !deadOwner(prior)) throw lockProblem();
      unlinkSync(path); create();
    } catch { throw lockProblem(); }
    finally { if (claimFd !== undefined) { closeSync(claimFd); unlinkSync(claim); } }
  }
  return () => { try { if (sameOwner(owner, readLock(path))) unlinkSync(path); } catch { /* Never remove another or unreadable owner. */ } };
}
async function lockedMutation(args, ports, action, filename) {
  const p = deps(ports), found = await resolveRun(args.ref, { cwd: args.cwd }, p);
  if (!found.run) return action(args, ports);
  let release;
  try { release = acquireRunLock(found.run.runDir, filename); return await action(args, { ...ports, releaseRunLock: release }); }
  catch (error) { if (error.code === 'run_busy') return fail(error.message); throw error; }
  finally { release?.(); }
}

// The real reason of a failed gh, git or Herdr call, in plain words.
function causeOf(error) {
  if (error?.code === 'ENOENT') return `${String(error.path ?? error.message ?? '').match(/\b(herdr|gh|git)\b/)?.[1] ?? 'a needed program'} is not installed or not on PATH`;
  if (error?.code === 'workflow_github_command_unavailable') return 'gh is not installed or not on PATH';
  return causeText(error?.stderr || error?.detail) || String(error?.code ?? 'error');
}
export const pddCommand = (packageRoot = PACKAGE_ROOT) => [process.execPath, join(packageRoot, 'bin', 'pdd.mjs')].map(shell).join(' ');
const pddFor = (p, packageRoot) => p.pdd ?? (p.env?.PDD_AGENT_SESSION && p.env?.PDD_BIN ? '"$PDD_BIN"' : pddCommand(packageRoot ?? PACKAGE_ROOT));
async function git(p, cwd, ...args) { return String((await p.execFile('git', args, { cwd })).stdout ?? '').trim(); }

// Command effects are explicit callbacks over the latest ordinary record. Keep the
// selected identity even when another run has replaced the record at this path.
const runIdentity=run=>JSON.stringify([run.runId,run.number,run.repo,run.root,run.commonDir,run.runDir]);
function commitRun(run, p, update) {
  const selected = runIdentity(run);
  const saved = updateRun(run.runDir, latest => {
    if (runIdentity(latest) !== selected) throw Error('The selected workflow run was replaced');
    p.progressGuard?.(latest);
    update(latest);
    return latest;
  }, p);
  for (const key of Object.keys(run)) delete run[key];
  Object.assign(run,saved);
  return run;
}
// Maintenance must not make a legacy blocked worker look newly active.
function commitMaintenance(run, p, update) {
  return commitRun(run, {...p,preserveProgress:true}, latest => {
    latest.progressAt ??= latest.updatedAt ?? latest.startedAt ?? 0;
    update(latest);
  });
}
// Revalidate command authority at local commits and before consequential effects.
function protectProgress(run,p,{approval=false,validate}={}) {
  const selectedState=run.state,selectedGate=structuredClone(run.gate ?? null),selectedArea=run.area;
  const check=latest=>{
    if (latest.parking?.phase === 'releasing') throw Object.assign(Error('This parked run is releasing its claim. Wait for release to finish.'), {code: 'workflow_progress_refused'});
    if(ended(latest) && !(selectedState==='completed'&&latest.state==='completed'&&selectedGate?.kind==='ask-code'))
      throw Object.assign(Error(`The run ended (${latest.state}). Stop working on it.`),{code:'workflow_progress_refused'});
    if(approval && (latest.area!==selectedArea || Boolean(latest.gate)!==Boolean(selectedGate) || (selectedGate?.id && latest.gate?.id!==selectedGate.id) || ['area','kind','at'].some(key=>latest.gate?.[key]!==selectedGate?.[key])))
      throw Object.assign(Error('The gate changed, look again.'),{code:'workflow_progress_refused'});
    validate?.(latest);
  };
  p.progressGuard=check;
  const inspect=()=>{const latest=readRun(run.runDir);if(!latest||runIdentity(latest)!==runIdentity(run))throw Object.assign(Error('The selected workflow run is missing or was replaced'),{code:'workflow_progress_refused'});check(latest);};
  p.inspectProgress=inspect;
  const exec=p.execFile,herdr=herdrCommand(p);
  p.execFile=async(file,args,options)=>{
    if((file==='git'&&['add','commit','push','checkout','switch','branch'].includes(args[0])) || (file==='gh'&&args[0]==='pr'&&['create','edit'].includes(args[1])))inspect();
    return exec(file,args,options);
  };
  p.commandPorts={...p.commandPorts,execFile:p.execFile};
  p.herdr=async args=>{if(['create','run','prompt'].includes(args[1]))inspect();return herdr(args);};
  return ()=>{approval=false;validate=undefined;};
}
const sameGate = (current, selected) => (!current || !selected) ? current === selected : ['area','kind','at'].every(key=>current[key]===selected[key]) && (!selected.id || current.id===selected.id);
const equalFact = (a,b) => JSON.stringify(a ?? null) === JSON.stringify(b ?? null);
// The same saved record regardless of key order.
const canonical = value => Array.isArray(value) ? value.map(canonical) : value && typeof value === 'object'
  ? Object.fromEntries(Object.keys(value).sort().map(key => [key, canonical(value[key])])) : value;
const sameFact = (a,b) => JSON.stringify(canonical(a ?? null)) === JSON.stringify(canonical(b ?? null));
const lastChat = (run, area) => [...(run.chats ?? [])].reverse().find(chat => chat.area === area);
// The chat identity and lifecycle fields that one observation may change.
const CHAT_OBSERVATION = ['workspaceId', 'repoWorkspaceId', 'tabId', 'paneId', 'terminalId', 'session', 'startedAt', 'messageFile', 'resumedAt', 'startUnconfirmed', 'state', 'evidence', 'code', 'closed', 'openedAt', 'endedAt', 'launchProfile', 'herdrAgentName', 'namingError', 'idleSince', 'idleAnchor', 'continueAnchor'];
const sameChat = (a,b) => a.area === b.area && a.paneId === b.paneId;
// Publication transports only the named fields produced by this observation.
// PR entries and metadata are applied separately by their actual publishers.
function publicationUpdate(run,keys=[]) {
  const fields=Object.fromEntries(keys.filter(key=>Object.hasOwn(run,key)).map(key=>[key,run[key]]));
  return latest=>Object.assign(latest,fields);
}

function saveGuard(action) {
  return async (...args)=>{
    try { return await action(...args); }
    catch(error){if(error?.code==='workflow_run_save_failed' || error?.code==='workflow_progress_refused')return fail(error.message);throw error;}
  };
}

async function confirm(p, question) {
  if (p.confirm) return p.confirm(question);
  const rl = createInterface({ input: p.stdin ?? process.stdin, output: p.stderr ?? process.stderr });
  const closed = new Promise(resolve => rl.once('close', () => resolve('')));
  try { return /^(?:y|yes)$/i.test(String(await Promise.race([rl.question(question).catch(() => ''), closed])).trim()); }
  finally { rl.close(); }
}

function claudeTrusts(folder, configDir, env) {
  try {
    const file = configDir ? join(configDir, '.claude.json') : join(env.HOME || homedir(), '.claude.json');
    return JSON.parse(readFileSync(file, 'utf8')).projects?.[folder]?.hasTrustDialogAccepted === true;
  } catch { return false; }
}

async function rawGit(p, root, ...args) {
  const reply = await p.execFile('git', args, {cwd:root});
  if (reply.code !== undefined && reply.code !== 0) throw Error(reply.stderr || 'Git inventory failed.');
  return String(reply.stdout ?? '');
}
async function changedFiles(run, p, strict = false) {
  try {
    const comparison = run.promptReturn && !run.replayAdoption ? await git(p,run.root,'merge-base','HEAD',`refs/remotes/origin/${run.baseBranch}`) : run.baseSha;
    const tracked = (await rawGit(p, run.root, 'diff', '--no-color', '--no-renames', '--name-only', '-z', comparison)).split('\0');
    const untracked = (await rawGit(p, run.root, 'ls-files', '--others', '--exclude-standard', '-z')).split('\0');
    return [...new Set([...tracked, ...untracked].filter(Boolean))];
  } catch (error) { if (strict) throw error; return []; }
}
const isScenario = text => JSON.parse(text)?.schema_version === 'prompt-runtime.program-scenario.v1';
async function scenarioInventory(run, p, changed) {
  const paths = [];
  const saved=new Set(run.replayBaseline?.vectors?.map(vector=>vector.path)??[]);
  const comparison = await git(p,run.root,'merge-base','HEAD',`refs/remotes/origin/${run.baseBranch}`);
  if (!commitSha(comparison)) throw Error('The original base comparison is unavailable.');
  for (const path of changed ?? await changedFiles({...run,baseSha:comparison},p,true)) {
    if(!path.endsWith('.json'))continue;
    // The replay reader reports deleted/malformed saved files with their value diff.
    if(saved.has(path)){paths.push(path);continue;}
    try {if(isScenario(readFileSync(join(run.root,path),'utf8')))paths.push(path);}
    catch(error){throw Error(`${JSON.stringify(path)}: ${oneLine(error.message)}`);}
  }
  return paths;
}
const replayEnabled = run => run.areas.some(area => area.replay_evidence === REPLAY_POLICY);
async function adoptionFailure(run,p) {
  const blocked=reason=>{
    const evidence={...readReplayEvidence(run),outcome:'blocked',reason};
    const step=run.areas[run.area]?.steps.filter(step=>run.done[step]).at(-1);
    if(p)commitRun(run,p,latest=>{latest.replayEvidence=evidence;if(step&&latest.done[step])latest.done[step].replayEvidence=evidence;});
    return reason;
  };
  if (!run.replayAdoption) return null;
  const code=run.areas[run.area]?.replay_evidence===REPLAY_POLICY;
  let snapshot;
  const result = await adoptReplayCorpus(run.root,join(run.runDir,'replay-adoption.json'),{
    ...(code ? {scenarioReference:run.replayAdoption.provenance.commit} : {}),onSnapshot:value=>{snapshot=value;}
  });
  if (result.outcome !== 'adopted' || JSON.stringify(result.provenance) !== JSON.stringify(run.replayAdoption.provenance))
    return blocked(`Corpus adoption cannot be reused (${result.reason || 'frozen provenance changed'}${result.cause ? `: ${result.cause}` : ''}). Start an ordinary approval workflow for changed requirements.`);
  const facts=vectors=>vectors?.map(v=>({path:v.path,sha256:v.sha256,checks:v.checks.map(c=>typeof c==='string'?c:
    JSON.stringify([c.vector,c.step_id,c.check_index,c.entry_path,c.operation,c.criterion_id,c.target,c.path,c.op]))})).sort((a,b)=>a.path.localeCompare(b.path));
  const anchor=code ? snapshot.approved_vectors : pinReplayVectors(run.root,result.paths).vectors;
  if(JSON.stringify(facts(anchor))!==JSON.stringify(facts(run.replayBaseline?.vectors)))
    return blocked('The adopted original anchor changed. Start an ordinary approval workflow for changed requirements.');
  return null;
}
const unavailableInventory = () => ({schema_version:'pdd.replay-vectors.v1',vectors:[],outcome:'blocked',reason:'The changed scenario inventory is unavailable; repair unreadable or malformed JSON candidates and Git listing failures.'});
async function refreshReplayBaseline(run,p,enteringCode=false,sourcePaths=null) {
  if (!replayEnabled(run) || run.replayAdoption) return;
  try {
    await rawGit(p,run.root,'fetch','origin',`refs/heads/${run.baseBranch}:refs/remotes/origin/${run.baseBranch}`);
    if (enteringCode) {const failure=await codeEntryFailure(run,p);if(failure)return failure;}
    const comparison = await git(p,run.root,'merge-base','HEAD',`refs/remotes/origin/${run.baseBranch}`);
    const saved = new Set(run.replayBaseline?.vectors?.map(vector=>vector.path) ?? []);
    const owned = (sourcePaths ?? prOf(run,askArea(run)?.name)?.sourcePaths ?? []).filter(path=>{
      if (!path.endsWith('.json') || saved.has(path)) return true;
      try { (p.fs?.lstatSync ?? lstatSync)(join(run.root,path)); return true; }
      catch (error) { if (error.code==='ENOENT') return false; throw error; }
    });
    const changed = [...new Set([...await changedFiles({...run,baseSha:comparison},p,true), ...owned])], paths = await scenarioInventory(run,p,changed);
    run.replayBaseline = pinRunAnchor(run.root,{paths,commit:run.baseSha,changed,scenarios:paths});
  }
  catch { run.replayBaseline = unavailableInventory(); }
  const applyPublication=publicationUpdate(run,['replayBaseline']);
  commitRun(run,p,applyPublication);
}
// #2640: a run with no prompt area before its replay code area selects the approved
// base scenarios in code space. Their values come only from the base commit.
function codeSpaceAnchor(run) {
  const first = run.areas.findIndex(area => area.replay_evidence === REPLAY_POLICY);
  return first >= 0 && !run.replayAdoption && !run.areas.slice(0, first).some(area => area.then === 'ask-code');
}
async function refreshCodeSpaceAnchor(run,p,scenarios) {
  let anchor;
  try { anchor = pinRunAnchor(run.root,{commit:run.baseSha,changed:await changedFiles(run,p,true),scenarios:scenarios ?? [],codeSpace:true}); }
  catch { anchor = unavailableInventory(); }
  if (JSON.stringify(anchor) === JSON.stringify(run.replayBaseline)) return;
  // Save only this field: a publication in progress keeps its unsaved in-memory facts.
  const selected = runIdentity(run);
  updateRun(run.runDir, latest => {
    if (runIdentity(latest) !== selected) throw Error('The selected workflow run was replaced');
    p.progressGuard?.(latest); latest.replayBaseline = anchor; return latest;
  }, p);
  run.replayBaseline = anchor;
}
async function currentReplayEvidence(run,p,validated=false) {
  let reason = validated ? null : await adoptionFailure(run,p);
  // Admit saved base paths before inventory classifies deleted or renamed files.
  if (codeSpaceAnchor(run)) await refreshCodeSpaceAnchor(run,p);
  let paths;
  try {
    paths=await scenarioInventory(run,p);
  } catch(error) { reason = `The current changed scenario inventory is unavailable: ${oneLine(error.message)}. Repair unreadable or malformed JSON candidates and Git listing failures.`; }
  if (codeSpaceAnchor(run)) await refreshCodeSpaceAnchor(run,p,paths);
  const evidence = readReplayEvidence(run,paths);
  return reason ? {...evidence,outcome:'blocked',reason} : evidence;
}
async function unpublishedScenarios(run,p) {
  const paths = (await rawGit(p,run.root,'diff','--name-only','-z','HEAD')).split('\0');
  paths.push(...(await rawGit(p,run.root,'ls-files','--others','--exclude-standard','-z')).split('\0'));
  const originals = new Set(run.replayBaseline?.vectors?.map(vector=>vector.path) ?? []);
  return [...new Set(paths.filter(Boolean))].filter(path=>path.endsWith('.json') &&
    (originals.has(path) || isScenario(readFileSync(join(run.root,path),'utf8'))));
}

function automaticHandoff(run, p, packageRoot = PACKAGE_ROOT) {
  if (!validSavedAutomaticOrigin(run) || !['pdd-bug','pdd-feature','pdd-small-change'].includes(run.skill)) return null;
  try {
    const root = realpathSync(run.sourceRoot), config = JSON.parse(readFileSync(join(root, 'pdd.json'), 'utf8'));
    const mode = config?.autopilot?.mode, id = createHash('sha256').update(root).digest('hex').slice(0, 20);
    const folder = p.autopilotStateRoot ?? join(p.env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
    const saved = JSON.parse(readFileSync(join(folder, `${id}.json`), 'utf8'));
    const action = saved.startAction, overlay = resolve(run.skillDir ?? join(packageRoot, 'skills', run.skill), 'steps', 'autopilot.md');
    if (!['auto','observe'].includes(mode) || !saved.enabled || saved.repo?.toLowerCase() !== run.repo.toLowerCase() || saved.coordinatorId !== run.automaticOrigin.coordinatorId || saved.machine !== run.automaticOrigin.machine || action?.command !== 'pdd autopilot start' || action.repository?.toLowerCase() !== run.repo.toLowerCase() || action.mode !== mode || !existsSync(overlay)) return null;
    return `Automatic run: the operator invoked ${action.command} for ${run.repo} in ${mode} mode. Read ${JSON.stringify(overlay)} and the actual owner handoff and run notes in ${JSON.stringify(run.runDir)}. Follow their scoped delegation for covered ordinary non-strict gates through the supported approval route; preserve strict approval and all repository, product, Try, code and merge restrictions. This action is not a quoted later person reply or checker approval. Current package CLI: ${pddCommand(packageRoot)}.`;
  } catch { return null; }
}

// Normal runs (#2962): no saved automatic origin and no strict approval policy. Strict and automatic runs keep their gates.
const THROUGH = ['prompt-pr', 'code'];
const throughWords = 'Use --through prompt-pr (stop after PR 1) or --through code (go on to the code PR).';
const TRY_SKIP = 'not asked in a normal run; the person can ask at the Story card to try it in the Simulator first';
function normalRun(run, p) {
  if (!run || Object.hasOwn(run, 'automaticOrigin')) return false;
  try { return !readApprovalPolicy({ root: run.sourceRoot }, p).strictApprovals; } catch { return false; }
}
// A return can reuse the code scope only under the same current operator
// delegation. Configuration alone is not a new approval.
function storyCoverage(run) {
  return Object.hasOwn(run,'automaticOrigin')
    ? [...run.decisions].reverse().find(decision=>decision.storyCoverage)?.storyCoverage ?? run.storyApproval
    : run.storyApproval;
}
function automaticPromptReturn(run,p) {
  if (!run.promptReturn || !storyCoverage(run)?.fingerprint || !run.promptReturn.codeApprovalId) return false;
  if (!run.decisions.some(decision=>decision.stage===askArea(run)?.name && decision.evidence?.id===run.promptReturn.codeApprovalId)) return false;
  try { return automaticFacts(run,p)?.mode === 'auto' && Boolean(automaticHandoff(run,p)) && !readApprovalPolicy({root:run.sourceRoot},p).strictApprovals; }
  catch { return false; }
}
// The Story gate of a workflow that approves before PR 1 (bug and feature) is its first approve area.
const storyGateIndex = run => run.areas.some(area => area.before === 'approve') ? run.areas.findIndex(area => area.gate === 'approve') : -1;
const atStoryGate = run => Boolean(run.gate) && !ended(run) && (run.gate.kind === 'approve' && run.area >= 0 && run.area === storyGateIndex(run)
  || run.gate.kind === 'approve-pr' && Boolean(run.gate.storyChanges?.length));
const storyApprovalGate = (run,area) => area?.gate==='approve' || Boolean(run.gate?.storyChanges?.length);
// Lines changed in each changed prompt against the run base; an untracked prompt counts all its lines as added.
async function promptLineCounts(run, p, changed) {
  const counts = new Map();
  try {
    const parts = (await rawGit(p, run.root, 'diff', '--numstat', '-z', run.baseSha)).split('\0');
    for (let i = 0; i < parts.length; i++) {
      const match = /^(\d+|-)\t(\d+|-)\t([\s\S]*)$/.exec(parts[i]);
      if (!match) continue;
      let path = match[3];
      if (path === '') { path = parts[i + 2]; i += 2; }
      counts.set(path, { added: match[1] === '-' ? '?' : Number(match[1]), removed: match[2] === '-' ? '?' : Number(match[2]) });
    }
  } catch { /* Unknown counts show as "?". */ }
  return changed.filter(path => path.endsWith('.prompt.md')).map(path => {
    if (counts.has(path)) return { path, ...counts.get(path) };
    try { const text = readFileSync(join(run.root, path), 'utf8'); return { path, added: text.split('\n').length - (text.endsWith('\n') || !text ? 1 : 0), removed: 0 }; }
    catch { return { path, added: '?', removed: '?' }; }
  });
}
async function cardText(run, p, extra = {}) {
  const changed = await changedFiles(run, p);
  return storyCard({ run, root: run.root, changed, prompts: await promptLineCounts(run, p, changed), through: run.through, ...extra });
}
const pddTestLines = (run, p) => ownResults(run, p).filter(result => result.kind === 'pdd test').flatMap(result => result.stories?.length ? result.stories : [result.summary]);
const cardGate = 'Gate: show the person the Story card above exactly as printed, then ask. Never ask a bare "approve?". Stop. Do not approve for them. When the person also wants the code PR after PR 1, add --through code to the approve command; without it, pdd stops after PR 1.';

async function areaMessage(run, index, p, packageRoot) {
  const area = run.areas[index], pdd = '"$PDD_BIN"', earlier = run.areas.slice(0, index).flatMap(item => item.steps);
  const summaries = earlier.filter(step => run.done[step]).map(step => `${step}: ${oneLine(run.done[step].summary).replace(/[.\s]+$/, '') || 'done'}`);
  const files = index ? await changedFiles(run, p) : [];
  const automatic = automaticHandoff(run, p, packageRoot), normal = !automatic && normalRun(run, p);
  return [
    `Read and follow the selected workflow skill at ${JSON.stringify(resolve(run.skillDir ?? join(packageRoot ?? PACKAGE_ROOT, 'skills', run.skill), 'SKILL.md'))} and its adjacent supporting files. This is a pdd workflow run.${index ? automatic ? ' Earlier areas have advanced.' : ' The person approved the earlier areas.' : ''}`,
    ...(automatic ? [automatic] : []),
    ...(validSavedAutomaticOrigin(run) ? [`Run the repository full suite through ${pddCommand(packageRoot)} workflow suite --command COMMAND and wait for the queue result. Test-slot waiting is not stuck.`] : []),
    ...promptReturnLines(run),
    `Issue: ${run.repo}#${run.number} "${oneLine(run.issue.title)}" ${run.issue.url}`,
    `Worktree: ${run.root} (branch ${run.branch}). Work and commit only here.`,
    `Saved base: ${run.baseBranch}. Use this base for this run; do not take a base from documents or ask which document to follow. PR 2 may stack on PR 1 as directed by pdd.`,
    `Run folder: ${run.runDir}. Put notes there. verify writes verify.md there with the exact test commands and their output.`,
    ...(index ? [`Approved so far: ${summaries.join('; ') || 'no step summaries'}.`, `Changed files: ${files.slice(0, 20).join(', ') || 'none yet'}${files.length > 20 ? ', …' : ''}.`] : []),
    `Area ${index + 1} of ${run.areas.length}: ${area.name}. Steps: ${area.steps.map(step => !area.optional.includes(step) ? step : normal && step === 'try' && area.before === 'approve' ? `${step} (optional: pdd skips it; do not ask)` : `${step} (optional: ask the person)`).join(', ')}.`,
    `After each step, run: ${pdd} workflow done STEP --summary "one line". It prints what to do next.`,
    ...(prLabel(run, area) === 'PR 2' && prOf(run, askArea(run).name) ? [`PR 1: ${prOf(run, askArea(run).name).url}. This area works on branch ${run.branch}, ${run.prBase === run.baseBranch ? `from the merged ${run.baseBranch}` : 'on top of PR 1'}.`] : []),
    ...(area.name === 'code' && askArea(run) ? [`If review finds a prompt defect, commit or keep code work, then run ${pdd} workflow open ${run.number} prompt-pr. Stop code work; all prompt corrections belong in PR 1.`] : []),
    area.gate === 'approve'
      ? automatic ? 'Gate: show the result and follow the scoped automatic overlay and owner handoff; preserve required human decisions.' : normal && index === storyGateIndex(run) ? `Gate: after the last step, pdd prints the Story card. Show it to the person as it is, then ask; never ask a bare "approve?". Never approve for them: ${approvalGuide(run, pdd)}` : `Gate: after the last step, show the person the result, ask them to approve or ask for changes, and stop. Never approve for them: ${approvalGuide(run, pdd)}`
      : area.then === 'ask-code' && normal && area.before === 'approve'
      ? 'After the last step, pdd reads its own saved check results. A full check pass opens PR 1 (prompt, Story and tests) with no question; then pdd follows the code-or-stop choice from the Story card. Never push, open a PR or merge yourself.'
      : area.then === 'ask-code'
      ? 'After the last step, pdd pushes the branch and opens PR 1 (prompt, Story and tests). Then show it and ask whether to make the code PR now. Never push, open a PR or merge yourself.'
      : `After the last step, pdd pushes the branch and opens ${prLabel(run, area)}. Never push, open a PR or merge yourself.`,
    `Read the shared prompting skill at ${JSON.stringify(resolve(packageRoot ?? PACKAGE_ROOT, 'skills', 'pdd-prompting', 'SKILL.md'))}; an installed copy with the same name may be older.`,
  ].join('\n') + '\n';
}

// The one sentence a person gets when they stop at PR 1 (0.1.4: testers saw the chat drop it when it was a hint).
const approvalGuide = run => `Show the gate and ask the person. One approval covers the gate and all its selected draft prompts. Relay their exact later words with:
"$PDD_BIN" workflow approve ${run.number} --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
Choose a quoted delimiter absent as a whole payload line. Or the person can use terminal y/N: pdd workflow approve ${run.number} in a normal terminal.`;
const approvalRetry = (run, prefix) => `The saved approval remains usable for this same gate. Retry with its exact recorded words; no new approval is needed. ${approvalGuide(run, prefix).replace('Show the gate and ask the person. One approval covers the gate and all its selected draft prompts. Relay their exact later words with:', 'Use the saved words with:')}`;
const codeLater = run => `To make the code PR later, tell your agent, or run pdd workflow approve ${run.number} in a terminal.`;
const prOf = (run, name) => (run.pr ?? []).find(pr => pr.stage === name) ?? null;
const askArea = run => run.areas.find(area => area.then === 'ask-code') ?? null;
// PR 1 is the ask-code area's prompt PR and PR 2 the code PR; a one-PR workflow says "the PR".
const prLabel = (run, area) => !askArea(run) ? 'the PR' : area.then === 'ask-code' ? 'PR 1' : 'PR 2';

// The status values of a prompt's Runtime interface blocks ("draft", "approved", …).
const statuses = text => interfaceBlocks(text).map(block => { try { return JSON.parse(block[1])?.status; } catch { return undefined; } });
// The *.prompt.md files that a branch changes against its base and whose Runtime interface is still "draft".
async function draftPrompts(run, p, branch, base) {
  try {
    const files = (await git(p, run.root, 'diff', '--no-color', '--name-only', `refs/remotes/origin/${base}...${branch}`)).split('\n').filter(path => path.endsWith('.prompt.md'));
    const drafts = [];
    for (const path of files) {
      let text;
      try { text = String((await p.execFile('git', ['show', `${branch}:${path}`], { cwd: run.root })).stdout ?? ''); } catch { continue; }
      if (statuses(text).includes('draft')) drafts.push(path);
    }
    return drafts;
  } catch { return []; }
}
const draftLine = drafts => `Draft prompts: ${drafts.join(', ')}. Approve them before you merge.`;
// How the person approves PR 1's draft prompts before the code PR (0.1.6: pdd asked "Make the code PR now?" and then refused).
// pdd approve works in the run worktree; approve then carries the approval to PR 1 (syncPr1).
const approveFirst = (run, drafts) => `Approve this gate and its draft prompts (${drafts.join(', ')}) together. Tell your agent, or run pdd workflow approve ${run.number} in a terminal.`;

// What PR 1 holds, read from the worktree before pdd opens it (files the chat did not commit count, because pdd commits
// them first): the changed prompts by Runtime interface status, the test files (prompt-runtime.program-scenario JSON)
// and the number of Stories.
async function worktreeContents(run, p) {
  const texts = new Map();
  for (const path of await changedFiles(run, p)) { try { texts.set(path, readFileSync(join(run.root, path), 'utf8')); } catch { /* Deleted or not a file. */ } }
  const paths = [...texts.keys()], prompts = paths.filter(path => path.endsWith('.prompt.md')), status = path => statuses(texts.get(path));
  const drafts = prompts.filter(path => status(path).includes('draft')), approved = prompts.filter(path => !drafts.includes(path) && status(path).includes('approved'));
  return { drafts, approved, other: prompts.filter(path => !drafts.includes(path) && !approved.includes(path)),
    tests: paths.filter(path => path.endsWith('.json') && (() => { try { return isScenario(texts.get(path)); } catch { return false; } })()),
    stories: paths.filter(isStoryPath).length };
}
// The words for what PR 1 holds (0.1.6 tester: the chat said "the approved prompt" while only the Story was approved).
function holdsLine({ drafts, approved, other, tests, stories }) {
  const prompts = (word, paths) => paths.length ? [`the ${word}prompt${paths.length > 1 ? 's' : ''} ${paths.join(', ')}`] : [];
  const parts = [stories > 1 ? 'the approved Stories' : 'the approved Story', ...prompts('approved ', approved), ...prompts('draft ', drafts), ...prompts('', other), ...(tests.length ? ['the tests'] : [])];
  return `PR 1 is ready with ${listed(parts)}.${tests.length ? '' : ' It has no test file.'}`;
}
// Nothing to try before the PR: no step of the area left a Try link, and the try step was skipped or the run has no test
// file (0.1.6 tester: status said "try it" for a browser-only Story with no runtime test).
const hasTryLink = text => redactTry(text) !== String(text);
const nothingToTry = (run, area, contents) => !area.steps.some(step => hasTryLink(run.done[step]?.summary ?? ''))
  && (/\bskip/i.test(run.done.try?.summary ?? '') || !contents.tests.length);
async function pr1Drafts(run, p) {
  const ask = askArea(run), pr1 = ask && prOf(run, ask.name);
  return pr1 ? draftPrompts(run, p, pr1.branch, pr1.base) : [];
}

// A failed chat request pauses the same run; it never authorizes another allocation or approval.
const activeChatFailure = run => !ended(run) && run.chatFailure?.area === run.areas[run.area]?.name ? run.chatFailure : null;
const chatFailureWords = run => {
  const failure = activeChatFailure(run);
  return `the ${failure.area} chat ${failure.phase === 'start' ? 'startup' : 'open'} was not confirmed (${failureReason(failure)}). Run pdd workflow open ${run.number} after Herdr is available.`;
};
const chatStatusWords = (run, chat) => run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase) ? `chat replacement pending at ${run.chatReplacement.phase}; run pdd workflow open ${run.number} --new` : chat === 'closed' ? `the Herdr workspace was closed. Reopen it with pdd workflow open ${run.number}.` : activeChatFailure(run) ? chatFailureWords(run)
  : chat === 'unavailable' ? `Herdr status unavailable (server_unavailable); chat activity is unknown. Run pdd workflow open ${run.number} after Herdr is available.`
  : chat === 'starting' ? `the chat is starting, not confirmed: Herdr shows no agent in its tab. Run pdd workflow open ${run.number}.`
  : `chat startup is not confirmed. Run pdd workflow open ${run.number} after Herdr is available.`;
// The words for an alive chat that cannot work (chatState 'cannot-work' with facts.health): the list words, the State
// words and the Next line. A known end time uses the status time format; otherwise the agent's own reset words.
const statusTime = (ms, timeZone) => new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit', hourCycle: 'h23', ...(timeZone ? { timeZone } : {}) }).format(new Date(ms));
function cannotWorkWords(run, health) {
  const n = run.number, time = health.until !== null ? statusTime(health.until, health.timeZone) : health.resets;
  const where = health.agent === 'codex' ? "codex login with this run's CODEX_HOME" : '/login in the chat, or fix its API key';
  if (health.kind === 'login') return { short: "the chat cannot work: the agent's login failed",
    long: `the chat cannot work: the agent's login failed (${health.message}). Sign the agent in again (${where}), then start a new chat for this area: pdd workflow open ${n} --new`,
    next: `pdd workflow open ${n} --new (after you sign the agent in again)` };
  // The limit has ended when its structured end time, else the time of the agent's own reset words, is not after now.
  const end = health.until ?? health.resetsAt ?? null;
  if (end !== null && end <= health.at) return { short: `the chat stopped at its usage limit (reset at ${time})`,
    long: `the chat stopped at its usage limit. The limit reset at ${time}. Open the chat and ask it to go on: pdd workflow open ${n}. Or start a new chat: pdd workflow open ${n} --new`,
    next: `pdd workflow open ${n}` };
  const until = time ? ` until ${time}` : '';
  return { short: `the chat cannot work: usage limit${until}`,
    long: `the chat cannot work: usage limit${until}. ${time ? 'After that time' : 'After the limit ends'}, open the chat and ask it to go on: pdd workflow open ${n}. Or start a new chat: pdd workflow open ${n} --new.${health.agent === 'codex' ? ` To use another Codex account now: CODEX_HOME=<folder> pdd workflow open ${n} --new` : ''}`,
    next: `pdd workflow open ${n}` };
}
function clearChatFailure(run) {
  if (!run.chatFailure) return;
  const selected = run.chatFailure.area === run.areas[run.area]?.name;
  delete run.chatFailure;
  if (selected && !ended(run) && !run.gate && !openQuestion(run)) run.state = 'running';
}

// A gate whose chat still works: after a change request it revises, else it writes the gate message (0.1.6 tester: status
// said "waiting for you" about a minute before the chat had asked).
const revising = run => { const last = run.changes?.at(-1); return Boolean(last && !last.answer && last.stage === run.gate.area && last.at >= run.gate.at); };
// A run stopped at the repair limit keeps that one-line reason, also after a later park (#3041).
const stuckReason = run => run.repairLimit?.area ? repairLimitReason(run.repairLimit.area) : run.integrationLimit?.area ? integrationLimitReason(run.integrationLimit.area) : run.parkReason ?? 'automatic work stopped';
// Read saved facts only. The digest must not probe or wake native workers.
export function automaticAttention({ repo, machine }, ports = {}) {
  return (ports.readRuns ? ports.readRuns() : allRuns({}, ports)).flatMap(run => {
    if (run.repo?.toLowerCase() !== repo?.toLowerCase() || !run.automaticOrigin || run.automaticOrigin.machine !== machine
      || run.state === 'cancelled' || run.state === 'completed' && run.gate?.kind !== 'ask-code') return [];
    const question = openQuestion(run);
    const item = run.state === 'stuck' ? { category: 'stuck', cause: stuckReason(run) }
      : run.state === 'paused' ? { category: 'parked', cause: run.runtimeWait?.reason ?? run.parkReason ?? 'automatic work paused' }
      : question || run.gate ? { category: 'decision', cause: question?.text ?? run.gate.kind } : null;
    return item ? [{ number: run.number, ...item }] : [];
  }).sort((a, b) => a.number - b.number);
}
const layoutClosing = run => ['close_intent', 'closed'].includes(run.layout?.phase);
function automaticResumeWords(run, now) {
  const success = run.chatResumeSuccess, chat = currentChat(run);
  if (!success || !chat || !Number.isFinite(now) || !Number.isFinite(success.at)
    || success.at > now || success.at <= now - 3600000 || ![1, 2, 3].includes(success.count)
    || success.area !== chat.area || success.paneId !== chat.paneId
    || success.sessionId !== chat.session?.id || success.resumedAt !== chat.resumedAt) return null;
  return `resumed after the chat stopped (${success.count} of 3)`;
}
const IDLE_WAIT_MS = 600000;
const idleAgent = (chat, live) => live.alive && ['idle', 'done'].includes(live.status)
  && validSessionId(chat.session?.id) && live.sessionId === chat.session.id;
function observeIdle(chat, live, now) {
  const next = structuredClone(chat);
  if (idleAgent(chat, live)) {
    if (!Number.isFinite(chat.idleSince) || chat.idleSince > now || chat.idleAnchor !== launchAnchor(chat)) next.idleSince = now;
    next.idleAnchor = launchAnchor(chat);
  } else { delete next.idleSince; delete next.idleAnchor; }
  return next;
}
const idleWords = (run, timeZone = 'UTC') => `agent idle since ${new Intl.DateTimeFormat('en-GB', {
  hour: '2-digit', minute: '2-digit', hourCycle: 'h23', timeZone,
}).format(new Date(currentChat(run).idleSince))}`;
// chat: what Herdr shows (chatState); facts: {drafts, nothing} read by the caller (gateFacts). describe itself makes no calls.
function describe(run, chat = null, { drafts = [], nothing = false, health = null, now = null, normal = false, suite = null, timeZone } = {}) {
  const area = run.areas[run.area], pr1 = askArea(run) && prOf(run, askArea(run).name);
  if (run.state === 'cancelled') return run.cancelled?.state === 'replaced' ? 'replaced' : 'cancelled';
  if (environmentStatus(run)) return environmentStatus(run);
  if (run.state === 'stuck') return `stuck: ${stuckReason(run)}`;
  if (suite && (suite.state !== 'finished' || suite.reason)) return suiteStatusWords(suite);
  if (runtimeWaiting(run)) return `waiting for the interpreter: ${run.runtimeWait.reason}. Autopilot checks the interpreter at each tick and wakes it when the interpreter is back; an Autopilot alert names any need for a person (pdd autopilot status)`;
  if (activeChatFailure(run) || ['unconfirmed', 'unavailable', 'starting', 'closed'].includes(chat)) return chatStatusWords(run, chat);
  if (openQuestion(run) && run.state !== 'completed') return `waiting for you: ${run.question.text.split('\n')[0]}`;
  if (chat === 'cannot-work' && health && run.state === 'running') return cannotWorkWords(run, health).long;
  if (chat === 'blocked' && run.state === 'running') return `waiting for you: the chat asks a question in its window (pdd workflow open ${run.number})`;
  if (chat === 'stopped' && run.state === 'running') return `the chat stopped. Run pdd workflow open ${run.number} to start it again.`;
  if (run.state === 'completed' && run.gate?.kind === 'ask-code') return `done at PR 1 (merged: ${pr1?.url}). ${codeLater(run)}`;
  if (run.state === 'completed') return 'complete: the PR is merged';
  if (run.gate?.automaticHold) return `PR 1 waits: ${run.gate.automaticHold}`;
  if (run.gate && chat === 'working') return revising(run) ? `the agent works on your changes to the ${run.gate.area} area` : `the agent writes the gate message for the ${run.gate.area} area`;
  if (normal && run.storyApproval && run.gate?.kind === 'approve-pr' && !atStoryGate(run)) return 'the agent must finish the prompt check before PR 1';
  if (normal && run.storyApproval && run.gate?.kind === 'ask-code' && !drafts.length) return run.through === 'code'
    ? `code PR requested; code entry waits. Fix the reported problem, then run pdd workflow done check.`
    : `stopped after PR 1 (${pr1?.url}). ${codeLater(run)}`;
  if (run.gate?.kind === 'approve-pr') return `waiting for you: ${nothing ? '' : 'try it, then '}approve to open ${prLabel(run, area) === 'the PR' ? 'the PR' : prLabel(run, area)} (or ask for changes)`;
  if (run.gate?.kind === 'ask-code' && drafts.length) return `PR 1 open (${pr1?.url}); waiting for you: approve the draft prompt${drafts.length > 1 ? 's' : ''} first, then make the code PR.`;
  if (run.gate?.kind === 'ask-code') return `PR 1 open (${pr1?.url}); waiting for you: code PR now, or stop and merge PR 1. ${codeLater(run)}`;
  if (run.gate) return `waiting for you: approve the ${run.gate.area} area or ask for changes`;
  if (run.promptReturn && area?.steps.some(step=>!run.done[step])) return `the agent works on ${area.steps.find(step=>!run.done[step])} after returning to prompt space`;
  if (prOf(run, area?.name) && area.gate === 'pr') return `waiting for you: review and merge ${prLabel(run, area)} on GitHub`;
  if (run.state === 'running' && chat === 'idle' && area?.steps.some(step => !run.done[step])) return idleWords(run, timeZone);
  const recovery = run.state === 'running' && automaticResumeWords(run, now);
  if (recovery) return recovery;
  const step = area?.steps.find(item => !run.done[item]);
  return step ? `the agent works on ${step}` : 'the agent works';
}

// Digest installed runtime bytes and the selected skill without exporting paths or contents.
function installedCandidateIdentity(packageRoot, skillDir) {
  try {
    const hash=createHash('sha256');
    const add=(label,path)=>{const stat=lstatSync(path); if(stat.isSymbolicLink()) throw Error('Unstable candidate');
      if(stat.isDirectory()) for(const name of readdirSync(path).sort()) add(`${label}/${name}`,join(path,name));
      else if(stat.isFile()) { const bytes=readFileSync(path); hash.update(`${label}:${bytes.length}:`); hash.update(bytes); }
    };
    add('package',join(packageRoot,'package.json')); add('runtime',join(packageRoot,'src')); add('skill',skillDir);
    return `sha256:${hash.digest('hex')}`;
  } catch {return 'unknown';}
}

const exactKeys = (value, keys) => value !== null && typeof value === 'object' && !Array.isArray(value)
  && Object.keys(value).length === keys.length && keys.every(key => Object.hasOwn(value, key));
const nonempty = value => typeof value === 'string' && value.trim().length > 0;
function validSavedAutomaticOrigin(run) {
  const origin = run.automaticOrigin;
  return exactKeys(origin, ['repository', 'coordinatorId', 'machine', 'claim'])
    && ['repository', 'coordinatorId', 'machine'].every(key => nonempty(origin[key]))
    && exactKeys(origin.claim, ['commentId', 'labelEventId'])
    && ['commentId', 'labelEventId'].every(key => nonempty(origin.claim[key]))
    && nonempty(run.repo) && origin.repository.toLowerCase() === run.repo.toLowerCase()
    && nonempty(run.issue?.url);
}
function explicitlyStopped(run, ports) {
  if (!Object.hasOwn(run, 'automaticOrigin')) return false;
  try {
    const root = realpathSync(run.sourceRoot);
    const id = createHash('sha256').update(root).digest('hex').slice(0, 20);
    const folder = ports.autopilotStateRoot ?? join(ports.env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
    return JSON.parse(readFileSync(join(folder, `${id}.json`), 'utf8'))?.enabled === false;
  } catch { return false; }
}
async function continuationOwnership(run, cwd, ports, custody = null, observed = null) {
  if (!Object.hasOwn(run, 'automaticOrigin')) return null;
  const origin = run.automaticOrigin;
  const reason = 'Automatic continuation refused: current claim ownership is unavailable or changed. Restore the admitted claim and retry.';
  if (!validSavedAutomaticOrigin(run)) return reason;
  try {
    const observation = observed ?? JSON.parse((await createDependencyReadPorts({ cwd: run.sourceRoot }, ports).owners.read({
      repository: run.repo, issues: [run.issue.url], purpose: 'claims',
    })).json);
    if (!observation || typeof observation !== 'object' || !Array.isArray(observation.claims)
      || !nonempty(observation.localOwner)
      || observation.claims.some(claim => !claim || typeof claim !== 'object' || Array.isArray(claim)
        || !nonempty(claim.issue) || typeof claim.active !== 'boolean')) return reason;
    const claims = observation.claims.filter(claim => claim?.issue === run.issue.url && claim?.active === true);
    if (claims.length !== 1) { if (custody && claims.length === 0) custody.unowned = true; return reason; }
    const claim = claims[0];
    if (!['owner', 'coordinatorId', 'machine', 'commentId', 'labelEventId'].every(key => nonempty(claim[key]))) return reason;
    if (custody) {
      custody.transferred = claim.owner === claim.coordinatorId && claim.machine !== origin.machine;
      custody.superseded = claim.owner === claim.coordinatorId && (claim.commentId !== origin.claim.commentId || claim.labelEventId !== origin.claim.labelEventId);
    }
    if (observation.localOwner !== origin.coordinatorId
      || claim.owner !== origin.coordinatorId || claim.coordinatorId !== origin.coordinatorId
      || claim.machine !== origin.machine || claim.commentId !== origin.claim.commentId
      || claim.labelEventId !== origin.claim.labelEventId) return reason;
    return null;
  } catch { return reason; }
}

function hasLiveReplacementRun(run, p) {
  return allRuns({cancelled:true}, p).some(other => other.runId !== run.runId && !ended(other)
    && other.repo?.toLowerCase() === run.repo?.toLowerCase()
    && other.issue?.url?.toLowerCase() === run.issue?.url?.toLowerCase()
    && samePath(other.sourceRoot, run.sourceRoot));
}

async function chatContinuationOwnership(run, p, {releaseUnowned = false, claimObservation = null, releaseReason = 'lost'} = {}) {
  const handedOver = run.cancelled?.state === 'handed-over', custody = {};
  let reason = handedOver ? run.cancelled.reason : await continuationOwnership(run, run.sourceRoot, p, custody, claimObservation);
  if (!reason || !handedOver && !(custody.transferred || releaseUnowned && (custody.unowned || custody.superseded))) return reason;
  if (releaseUnowned && continuationCheckHeld(run,p)) return reason;
  if (!handedOver) reason = custody.transferred ? 'Chat continuation refused: claim ownership transferred to another machine.' : 'Chat continuation refused: the admitted claim is no longer active.';
  // Persist the terminal state before cleanup, so an interrupted close cannot
  // leave the old worker eligible for another continuation or publication.
  if (!handedOver) commitRun(run, p, latest => {
    if (ended(latest) || !sameFact(latest.automaticOrigin, run.automaticOrigin))
      throw Object.assign(Error('Claim custody changed before handover.'), {code: 'workflow_progress_refused'});
    latest.state = 'cancelled';
    latest.cancelled = {state: 'handed-over', at: p.now(), reason};
    if (releaseUnowned) {
      delete latest.parking; delete latest.blockedOn; delete latest.parkReason; delete latest.runtimeWait; delete latest.routeWait;
      latest.claimRelease = {state: 'pending', reason: releaseReason, at: latest.cancelled.at};
    }
    for (const chat of latest.chats ?? []) chat.endedAt ??= latest.cancelled.at;
  });
  const {warnings, kept} = await cleanupRunChats(run, {...p, progressGuard: undefined}, {force: !releaseUnowned, reason: 'handover', ...(releaseUnowned ? {graceMs:0} : {})});
  let cleanupPending = false;
  if (releaseUnowned) {
    const latest = readRun(run.runDir) ?? run;
    const held = kept.length ? 'Chat cleanup retained work.' : hasLiveReplacementRun(latest,p) ? 'A replacement local run owns this issue.' : await releaseWorkerHeld(latest,p);
    if (held) cleanupPending = true;
    else {
      let local;
      try { local = await releaseIssueClaim({cwd:run.sourceRoot,issueNumber:run.number,runId:run.runId},p.commandPorts); }
      catch { local = {state:'recovery_required'}; }
      if (local?.state !== 'released') cleanupPending = true;
      else {
        const afterLocal = readRun(run.runDir) ?? latest;
        const heldAfterLocal = hasLiveReplacementRun(afterLocal,p) ? 'A replacement local run owns this issue.' : await releaseWorkerHeld(afterLocal,p);
        if (heldAfterLocal) cleanupPending = true;
        else if (custody.unowned && validSavedAutomaticOrigin(run)) {
          try {
            const released = await (p.releaseParkedClaim ?? releaseParkedClaim)({
              cwd: run.sourceRoot, repository: run.repo,
              claim: {issue: run.issue.url, coordinatorId: run.automaticOrigin.coordinatorId, machine: run.automaticOrigin.machine, ...run.automaticOrigin.claim},
              coordinatorId: run.automaticOrigin.coordinatorId, machine: run.automaticOrigin.machine,
              runId: run.runId, branch: run.branch, reason: releaseReason,
            }, {...p, ...p.commandPorts});
            if (released?.state === 'released') commitRun(run, p, latestRun => {
              if (latestRun.claimRelease?.reason === releaseReason) delete latestRun.claimRelease;
            });
            else cleanupPending = true;
          } catch { cleanupPending = true; }
        } else if (custody.superseded) cleanupPending = true;
      }
    }
  }
  return [reason, `This local run was handed over to another machine. The worktree stays at ${run.root}.`,
    ...warnings, ...(kept.length ? [`Kept open: ${kept.map(item => `${item.area} (${item.reason})`).join(', ')}. Retry safe cleanup with pdd workflow tidy.`] : []),
    ...(cleanupPending ? ['Claim cleanup remains pending; local work or both claim labels are not confirmed released. The coordinator will retry it on a later tick.'] : [])].join('\n');
}

function validAutomaticContext(value) {
  const envelope = value?.version === 'pdd.autopilot-coordinator.v1';
  const keys = envelope ? ['version', 'repository', 'coordinatorId', 'machine', 'activation'] : ['repository', 'coordinatorId', 'machine', 'activation', 'claim'];
  if (value?.runs !== undefined) keys.push('runs');
  return exactKeys(value, keys) && ['repository', 'coordinatorId', 'machine', 'activation'].every(k => nonempty(value[k]))
    && (value.runs === undefined || Number.isSafeInteger(value.runs) && value.runs > 0)
    && (envelope || exactKeys(value.claim, ['commentId', 'labelEventId']) && nonempty(value.claim.commentId) && nonempty(value.claim.labelEventId));
}

async function startRunUnlocked({ name, issue, agent = 'codex', model, herdrAgentName, codexThreads, base, adoptCorpus, coordinator, draft = false, origin, decisionId, outcome, through, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const automatic = coordinator !== undefined || Object.hasOwn(p.env, 'PDD_AUTOPILOT_CONTEXT');
  if (Object.hasOwn(p.env, 'PDD_AUTOPILOT_CONTEXT')) {
    let environmentContext;
    try { environmentContext = JSON.parse(p.env.PDD_AUTOPILOT_CONTEXT); } catch { return fail('Invalid automatic start context.'); }
    if (!validAutomaticContext(environmentContext)) return fail('Invalid automatic start context.');
    if (coordinator === undefined) coordinator = environmentContext;
  }
  if (automatic && !validAutomaticContext(coordinator)) return fail('Invalid automatic start context.');
  if (typeof draft !== 'boolean') return fail('Draft publication must be a Boolean.');
  if (through !== undefined && !THROUGH.includes(through)) return fail(throughWords);
  let workflow;
  try { workflow = readWorkflowAreas({ packageRoot, name, cwd, home: p.env.HOME || homedir() }); } catch (error) { return fail(error.message); }
  if (adoptCorpus !== undefined && (typeof adoptCorpus !== 'string' || !adoptCorpus.trim() || !workflow.areas.some(area=>area.replay_evidence===REPLAY_POLICY))) return {exitCode:2,message:'--adopt-corpus requires a declaration path and an explicitly replay-evidence-enabled workflow.'};
  // A built-in agent, or a ~/.config/pdd/agents.json entry name that runs as its kind with its own command.
  const chosen = workflowAgentEntry(agent, { cwd, env: p.env });
  if (!chosen.ok) return fail(chosen.message);
  agent = chosen.agent;
  const definition = chosen.definition, profileEnv = definition ? { ...p.env, ...definition.env } : p.env;
  // Save the initial profile for later chats; explicit Codex replacement may select another.
  const variable = homeVariable(agent), configDir = variable && profileEnv[variable] ? resolve(cwd, expandHome(profileEnv[variable], profileEnv)) : null;
  if (configDir && !isFolder(configDir)) return fail(`${variable} is "${configDir}", but that folder does not exist. Fix ${variable} and run the command again.`);
  let initialProfile;
  try { initialProfile = selectLaunchProfile({run: {agent, configDir}, model, herdrAgentName, codexThreads: codexThreads ?? (agent === 'codex' ? 5 : undefined)}, p); }
  catch (error) { return fail(error.message); }
  let explicitBase = base !== undefined;
  const badBase = () => fail('Use --base with a branch name, for example feature/checkout.');
  if (explicitBase && (typeof base !== 'string' || !base || base === 'HEAD' || base.startsWith('-') || base.startsWith('refs/'))) return badBase();
  const context = await gitContext(cwd, p);
  if (!context) return fail('Run this inside a Git checkout of the repository that has the issue.');
  if (through !== undefined) {
    if (automatic) return fail('--through applies only to a normal run. Nothing changed.');
    try { if (readApprovalPolicy({ root: context.toplevel }, p).strictApprovals) return fail('--through is not available in strict mode. Nothing changed.'); }
    catch (error) { return fail(error.message); }
  }
  if (explicitBase) {
    try {
      const checked = await p.execFile('git', ['check-ref-format', `refs/heads/${base}`], { cwd: context.toplevel });
      if (checked?.code !== undefined && checked.code !== 0) return badBase();
    } catch { return badBase(); }
  }
  let binding;
  p.say(`Reading issue ${issue} from GitHub…`);
  try { binding = await resolveWorkflowIssue({ cwd: context.toplevel, issue }, p.commandPorts); }
  catch (error) { return fail(`pdd could not read issue ${issue} with gh (${causeOf(error)}). Check "gh auth status", the origin remote and the issue number.`); }
  const number = binding.issue.number, runDir = runDirFor(context.commonDir, number), existing = readRun(runDir);
  let actualOrigin = origin === 'manual' ? 'manual' : 'unknown';
  if (origin === 'autopilot' && /^[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}$/.test(decisionId ?? '')) {
    try {
      const decision=JSON.parse(readFileSync(join(context.commonDir,'pdd','metrics','decisions',`${decisionId}.json`),'utf8'));
      const repo=binding.repository.toLowerCase(), snapshotId=decision.snapshotId;
      if (/^snapshot:[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}$/.test(snapshotId ?? '')
          && decision.id === decisionId && decision.repo === repo && decision.issue === number && decision.offered === true) {
        const snapshot=JSON.parse(readFileSync(join(context.commonDir,'pdd','metrics','snapshots',`${snapshotId.slice(9)}.json`),'utf8'));
        validateSnapshot(snapshot,repo);
        const matchingSelection=event=>event?.schema === 'pdd.metrics.event.v1' && event.id === `${decisionId}:selection`
          && event.repo === repo && event.issue === number && event.type === 'selection' && event.data?.snapshotId === snapshotId;
        const selected=Array.isArray(decision.events) ? decision.events.filter(matchingSelection) : [];
        if (snapshot.snapshotId === snapshotId && snapshot.repo === repo && Array.isArray(snapshot.events)
            && selected.length === 1 && snapshot.events.some(event=>matchingSelection(event) && sameFact(event,selected[0]))) actualOrigin='autopilot';
      }
    } catch { /* Unknown evidence must not block a workflow. */ }
  }
  let cliVersion='unknown', skillVersion='unknown';
  try { cliVersion=JSON.parse(readFileSync(join(packageRoot,'package.json'),'utf8')).version || 'unknown'; } catch {}
  try { skillVersion=/^  pdd-skills:\s*(\S+)/m.exec(readFileSync(join(workflow.dir,'SKILL.md'),'utf8'))?.[1] ?? 'unknown'; } catch {}
  const metricsOrigin={origin:actualOrigin, ...(actualOrigin === 'autopilot' ? {decisionId} : {}), requiredOutcome:['code','prompt-only'].includes(outcome) ? outcome : 'unknown',cliVersion,skillVersion,candidateVersion:installedCandidateIdentity(packageRoot,workflow.dir)};
  let automaticOrigin;
  if (automatic) {
    try {
      // Intake is a separate owner. A missing binding is never a manual start.
      const check = p.checkDependencyStart ?? (await import('./issue-dependencies-intake.mjs')).checkDependencyStart;
      if (typeof check !== 'function') throw Error('missing intake');
      const readPorts = createDependencyReadPorts({ cwd: context.toplevel }, {...p,checkPaneCapacity:()=>ensurePaneBudget(3,p)});
      const observation = JSON.parse((await readPorts.owners.read({ repository: binding.repository, issues: [binding.issue.url] })).json);
      const claims = observation.claims.filter(c => c.issue === binding.issue.url && c.active === true);
      if (claims.length !== 1 || observation.localOwner !== coordinator.coordinatorId || coordinator.repository.toLowerCase() !== binding.repository.toLowerCase()) return fail('Automatic start deferred: owner.');
      const claim = claims[0];
      if (claim.owner !== coordinator.coordinatorId || claim.coordinatorId !== coordinator.coordinatorId || claim.machine !== coordinator.machine || !nonempty(claim.commentId) || !nonempty(claim.labelEventId)) return fail('Automatic start deferred: owner.');
      if (coordinator.version) { const { version, ...identity } = coordinator; coordinator = { ...identity, claim: { commentId: claim.commentId, labelEventId: claim.labelEventId } }; }
      if (coordinator.claim.commentId !== claim.commentId || coordinator.claim.labelEventId !== claim.labelEventId) return fail('Automatic start deferred: owner.');
      const decision = await check({ cwd: context.toplevel, repository: binding.repository, issue: binding.issue.url, coordinator }, readPorts);
      if (!decision?.allowed) return fail(`Automatic start deferred: ${decision?.reason ?? 'unknown'}.`);
      if (existing && !ended(existing)) return fail('Automatic start deferred: issue has an active run.');
      automaticOrigin = { repository: binding.repository, coordinatorId: coordinator.coordinatorId, machine: coordinator.machine, claim: { ...coordinator.claim } };
    } catch { return fail('Automatic start is unavailable: native admission binding is incomplete.'); }
  }
  if (existing?.draft !== undefined && typeof existing.draft !== 'boolean') return fail('The saved draft publication policy must be a Boolean.');
  if (existing && !ended(existing) && draft && existing.draft !== true) return fail(`Issue #${number} already has a nondraft run. Use pdd workflow approve ${number} --draft at its ready unpublished gate; starting again cannot change that policy.`);
  if (automatic) {
    let selected;
    try { selected = await selectAutopilotBase({ cwd: context.toplevel, defaultBranch: binding.defaultBranch }, { execFile: p.execFile }); }
    catch (error) { return fail(error.message); }
    if (explicitBase && base !== selected) return fail(`Automatic base is ${selected}; --base ${base} conflicts with the configured selection. Do not select a base from documents.`);
    base = selected; explicitBase = true;
  }
  const warnings = [...(workflow.warnings ?? [])], baseBranch = explicitBase ? base : binding.defaultBranch;
  // A requested origin branch must be usable before releasing a cancelled run's claim.
  if (explicitBase) {
    try {
      const fetched = await p.execFile('git', ['fetch', 'origin', `refs/heads/${baseBranch}:refs/remotes/origin/${baseBranch}`], { cwd: context.toplevel });
      if (!fetched || fetched.code !== undefined && fetched.code !== 0) throw Error('base fetch failed');
      const sha = await git(p, context.toplevel, 'rev-parse', '--verify', '--end-of-options', `refs/remotes/origin/${baseBranch}^{commit}`);
      if (!/^[0-9a-f]{40}$/.test(sha)) throw Error('base commit unavailable');
    } catch {
      return fail(`Could not fetch --base ${baseBranch} from origin. Check that origin has this branch and Git can fetch it, then run again. No new run was started.`);
    }
  }
  let adoption, adoptionSnapshot, declarationBytes, frozenFolder;
  try {
  if(adoptCorpus !== undefined) {
    try {
      if(!explicitBase) {
        try {await rawGit(p,context.toplevel,'fetch','origin',baseBranch);}
        catch {return {exitCode:2,message:'Cannot adopt the approved corpus (unavailable: startup fetch failed). Repair the source or start an ordinary approval workflow. No new run was started.'};}
      }
      const selectedBase=await git(p,context.toplevel,'rev-parse','--verify','--end-of-options',`refs/remotes/origin/${baseBranch}^{commit}`);
      adoption=await adoptReplayCorpus(context.toplevel,resolve(cwd,adoptCorpus),{currentRef:selectedBase,onSnapshot:s=>{adoptionSnapshot=s;},onNativeDeclaration:bytes=>{declarationBytes=bytes;}});
      if(adoption.outcome!=='adopted')return {exitCode:2,message:`Cannot adopt the approved corpus (${adoption.reason}${adoption.cause ? `: ${adoption.cause}` : ''}). Repair the declaration/source or start an ordinary approval workflow. No new run was started.`};
      frozenFolder=realpathSync(mkdtempSync(join(tmpdir(),'pdd-adoption-declaration-')));
      writeFileSync(join(frozenFolder,'declaration.json'),declarationBytes,{mode:0o600});
    } catch(error) {const code=/^[A-Z0-9_-]{1,32}$/.test(String(error.code ?? '')) ? error.code : 'local-operation-failed';return {exitCode:2,message:`Cannot adopt the approved corpus (unavailable: source selection or declaration freezing failed; ${code}). Repair the declaration/source or start an ordinary approval workflow. No new run was started.`};}
  }
  try { await ensurePaneBudget(3, p); }
  catch (error) {
    if (['herdr_pane_budget','invalid_pane_budget'].includes(error.code)) return fail([
      ...(automatic && error.code === 'herdr_pane_budget' ? ['Automatic start deferred: panes.'] : []),
      failureReason(error), ...failureDetails(error)].join('\n'));
    // Unknown capacity is not evidence of a full server. Startup retains its
    // normal durable recovery path if Herdr itself is unavailable.
  }
  const runId = randomUUID();
  if (existing?.pr?.length && !ended(existing)) await refreshPr(existing, p);
  if (existing) {
    // An active run never blocks a new one (#2871): mark it replaced, name it once, then free it like a cancelled run.
    const replacing = !ended(existing);
    if (replacing) {
      const last = existing.updatedAt ?? existing.startedAt, minutes = Number.isFinite(last) ? Math.max(0, Math.floor((p.now() - last) / 60000)) : null;
      try { commitRun(existing, p, latest => { latest.state = 'cancelled'; latest.cancelled = { state: 'replaced', at: p.now() }; latest.replacedBy = runId; latest.gate = null; for (const chat of latest.chats ?? []) chat.endedAt ??= p.now(); }); }
      catch (error) { return fail(`Issue #${number} has an active run ${existing.runId}, but pdd could not mark it replaced (${oneLine(error.message)}). Retry in a moment.`); }
      warnings.push(`warning: Issue #${number} had an active run ${existing.runId} (${existing.workflow}). pdd marked it replaced and starts a new run.`
        + ` Its worktree stays at ${existing.root} (branch ${existing.branch}), from checkout ${existing.sourceRoot}. Last activity: ${minutes === null ? 'unknown' : `${minutes} min ago`}.`
        + (minutes === null || minutes < 60 ? ' It may still be working; close its chat if it is.' : '')
        + ` Cleanup retries with pdd workflow tidy. To stop retained busy chats, run pdd workflow cancel ${number} from ${existing.root}.`);
    }
    const released = await releaseIssueClaim({ cwd: context.toplevel, runId: existing.runId, issueNumber: number }, p.commandPorts);
    if (released.state !== 'released') return fail(`Issue #${number} has a ${replacing ? 'replaced' : existing.state} run, but pdd could not free the issue: ${released.message}`);
    const cleanup = await cleanupRunChats(existing, {...p, progressGuard: undefined}, {graceMs:0});
    warnings.push(...cleanup.warnings);
    if (!replacing) warnings.push(`Issue #${number} had a ${existing.state} run. Its worktree stays at ${existing.root} (branch ${existing.branch}). This run gets a new worktree and branch.`);
  }
  if (!explicitBase && adoptCorpus === undefined) {
    p.say(`Fetching origin/${baseBranch}…`);
    try { await p.execFile('git', ['fetch', 'origin', baseBranch], { cwd: context.toplevel }); }
    catch { warnings.push(`warning: "git fetch origin ${baseBranch}" failed; the worktree starts from the last fetched ${baseBranch}.`); }
  }
  p.say(`Making the worktree and branch for #${number}…`);
  const allocated = await allocateIssueWorktree({ cwd: context.toplevel, repository: binding.repository, issueNumber: number, runId,
    workflowName: name, baseRef: `refs/remotes/origin/${baseBranch}` }, p.commandPorts);
  if (allocated.state !== 'ready' || !allocated.assignment) {if(frozenFolder)rmSync(frozenFolder,{recursive:true,force:true});return fail(`pdd could not make the worktree for #${number}: ${allocated.message}`);}
  const a = allocated.assignment;
  let adoptedAnchor;
  if(adoption) {
    try {
      const actual=await adoptReplayCorpus(a.worktreePath,join(frozenFolder,'declaration.json'));
      adoptedAnchor=pinReplayVectors(a.worktreePath,adoption.paths);
      if(actual.outcome!=='adopted' || JSON.stringify(actual)!==JSON.stringify(adoption) || adoptedAnchor.outcome) {
        const released=await releaseIssueClaim({cwd:context.toplevel,runId,issueNumber:number},p.commandPorts);
        return {exitCode:2,message:`The allocated worktree differs from the approved corpus. No active run or chat was saved. Retained worktree: ${a.worktreePath}; branch: ${a.branch}. ${released.state==='released' ? 'The new issue claim was released; the retained files and branch are available for inspection.' : `The new issue claim ${runId} could not be released: ${released.message}. Inspect it before retrying.`} Start an ordinary approval workflow for changed requirements.`};
      }
    } finally {rmSync(frozenFolder,{recursive:true,force:true});}
  }
  // Keep the ended run's record next to the new one; only a plain issue number names the active run.
  if (existing) {
    const archived = `${runDir}-cancelled-${existing.runId.slice(0, 8)}`;
    renameSync(runDir, archived);
    const relocate = value => typeof value === 'string' && (value === runDir || value.startsWith(runDir + '/'))
      ? archived + value.slice(runDir.length) : Array.isArray(value) ? value.map(relocate)
      : value && typeof value === 'object' ? Object.fromEntries(Object.entries(value).map(([key,v]) => [key,relocate(v)])) : value;
    const retained = relocate(existing);
    writeRun(retained, p);
  }
  const productMarkers = [...new Set(String(binding.issue.body ?? '').match(/<!-- pdd-product: run=[^\r\n]+? -->/g) ?? [])];
  if (productMarkers.length > 1) warnings.push('Warning: The issue has multiple planned-run markers; its product association is unverified.');
  const run = { v: 1, runId, workflow: name, skill: workflow.skill, skillDir: workflow.dir, repo: binding.repository,
    ...(productMarkers.length === 1 ? { productMarker: productMarkers[0] } : {}),
    issue: { number, title: binding.issue.title, url: binding.issue.url, ...(String(binding.issue.body ?? '').trim() ? { asked: String(binding.issue.body).slice(0, 4000) } : {}) }, number, root: a.worktreePath, branch: a.branch,
    baseBranch, baseSha: a.baseSha, sourceRoot: a.sourceRoot, commonDir: a.commonDir, runDir, agent,
    // The agents.json entry by name, kind and command; its env values may be secrets, so only their names are saved.
    ...(definition ? { agentDefinition: { name: definition.name, kind: definition.kind, command: definition.command, envNames: Object.keys(definition.env) } } : {}),
    configDir, draft, ...(through ? { through } : {}), metricsOrigin, metricsObservations:[{type:'coverage',at:new Date(p.now()).toISOString(),data:{complete:false}}], ...(automaticOrigin ? { automaticOrigin } : {}),
    startedAt: p.now(), state: 'running', areas: workflow.areas, area: 0, done: {}, gate: null, chats: [], decisions: [], changes: [],
    approvalRecord: null, pr: [], prState: null, cancelled: null, warnings, journalSeq: 0,
    previous: existing ? [...(existing.previous ?? []), { runId: existing.runId, root: existing.root, branch: existing.branch, runDir: `${runDir}-cancelled-${existing.runId.slice(0, 8)}` }] : [] };
  run.launchProfile = { ...initialProfile, herdrAgentName: herdrAgentName ?? launchProfile(run).herdrAgentName };
  mkdirSync(runDir, { recursive: true });
  if(adoption) {
    writeFileSync(join(runDir,'replay-adoption.json'),declarationBytes,{mode:0o600,flag:'wx'});
    run.replayAdoption={declaration:adoptionSnapshot.declaration, declaration_sha256:adoption.provenance.declaration_sha256, provenance:adoption.provenance};
    run.replayBaseline=adoptedAnchor;
    warnings.push(`Adopted ${adoption.paths.length} unchanged scenarios from ${adoption.provenance.repository}@${adoption.provenance.commit}. External authorization: external-assertion-unverified; reference ${adoption.provenance.reference}; asserted by ${adoption.provenance.asserted_by}. pdd cannot independently authenticate that authorization; adoption does not prove execution.`);
  }
  writeRun(run, p);
  const first = workflow.areas[0];
  try { await startNextChat(run, p, packageRoot); }
  catch (error) {
    if(error?.code==='workflow_run_save_failed')throw error;
    const warning=`The ${first.name} chat startup was not confirmed (${error.code ?? 'error'}).`;
    commitRun(run,p,latest=>{latest.warnings.push(warning);});
    return fail([...warnings, `The worktree is ready at ${a.worktreePath}, but the ${first.name} chat startup was not confirmed (${error.code === 'ENOENT' ? causeOf(error) : failureReason(error)}).`,
      ...failureDetails(error), `Start it with: pdd workflow open ${number}`].join('\n'));
  }
  commitRun(run,p,()=>{});
  const chat = run.chats[0];
  return done([...warnings,
    `Started ${name} for ${run.repo}#${number} "${oneLine(run.issue.title)}".`,
    `Area 1 of ${run.areas.length}: ${first.name} (${first.steps.join(', ')}). ${agent === 'claude' ? 'Claude' : agent === 'gemini' ? 'Gemini' : agent === 'agy' ? 'Antigravity' : 'Codex'}${definition ? ` (agents.json entry ${JSON.stringify(definition.name)})` : ''} works in Herdr session pdd, tab "${chat.label}".`,
    ...(agent === 'claude' && !claudeTrusts(run.sourceRoot, run.configDir, p.env) ? ['Claude may first ask you to trust the new worktree folder. Open the chat and choose "Yes, I trust this folder".'] : []),
    `Base: origin/${run.baseBranch}`,
    `Worktree: ${run.root} (branch ${run.branch})`,
    `Run folder: ${runDir}`,
    `Watch the chat: pdd workflow open ${number}`,
    `Status:         pdd workflow status ${number}`,
    approvalGuide(run, p.pdd),
    'You can close this terminal. The chat keeps working in Herdr.'].join('\n'));
  } finally {if(frozenFolder)rmSync(frozenFolder,{recursive:true,force:true});}
}

// A runtime report link has a /r/ path segment, or starts with PDD_RUNTIME_URL when that is set. No host is fixed here.
function hasReportLink(text, env) {
  const base = String(env.PDD_RUNTIME_URL ?? '').replace(/\/+$/, '');
  return (text.match(/https?:\/\/[^\s)<>\]"']+/g) ?? []).some(url => /^https?:\/\/[^/]+\/(?:[^\s]*\/)?r\/[^/\s]+/.test(url) || base && url.startsWith(`${base}/`));
}

// PR bodies show repository paths, never the person's machine: the worktree becomes repo-relative, the run folder
// "<run folder>", and any other home or temp path "<local path>".
function hideLocalPaths(text, run) {
  return text.split(`${run.root}/`).join('').split(run.root).join('.').split(run.runDir).join('<run folder>')
    .replace(/(?:\/private)?\/(?:Users|home|var\/folders|tmp)\/[^\s)`'"<>\]]*/g, '<local path>');
}
// Prompt tests lines in a step summary (0.1.6): "Prompt tests (<story>) (DRAFT)?: …" per Story, and the overall
// "Prompt tests: …"; older summaries say "Runtime check" and read the same way. The chat pastes the lines that pdd test
// prints, one per line or joined with "; "; a result ends at a line break, ";", a "Report" line, a link or the next line.
const PROMPT_TESTS = new RegExp(PROMPT_TESTS_WORDS);
const LABEL_START = new RegExp(`^${PROMPT_TESTS_WORDS}`);
const LINE_PATTERN = new RegExp(`${PROMPT_TESTS_WORDS}((?:\\s*\\([^)]*\\))*):\\s*(.*?)(?=\\n|\\s*(?:;|\\bReport\\b|https?:\\/\\/|${PROMPT_TESTS_WORDS}|$))`, 'gs');
// A result is only its pdd parts, joined by " · " (mark and criteria, checks, other states, AI calls). Words an agent
// wrote after them on the same line ("… 2 AI calls. Full suite: 4085 passed.") are not part of the result.
const RESULT_PART = /^(?:(?:waiting|sent|passed|failed|refused|partial|not run)(?: \([^()]+\))?|\d+ (?:waiting|sent|passed|failed|refused|partial|not run)(?: \([^()]+\))?|\d+ tests could not run|\d+ criteria not checked|(?:✓|✗|no verdict|running|busy|unknown|UNKNOWN|queued|refused|not run)(?: (?:\d+ of \d+ criteri(?:a|on)|passed))?|\d+ of \d+ criteri(?:a|on)|passed|criteria details not reported|\d+\/\d+ checks|(?:\d+ AI calls?(?: \(\d+ for reruns\))?|\d+ for reruns)(?: \+ \d+ unknown)?|\d+ (?:refused|not run|unknown|queued|running|ahead|not yet settled|Stor(?:y|ies) skipped)|\d+ AI calls? so far|step \d+(?: of \d+)?(?: \([^)]*\))?)$/;
function resultParts(text) {
  const sentence = text.split(/\.\s/)[0].replace(/[.,]$/, ''), kept = [];
  for (const part of sentence.split(' · ')) {
    if (RESULT_PART.test(part)) { kept.push(part); continue; }
    // Without a step number, progress puts the step name directly after its own running marker.
    if (part && kept.length > 1 && (kept.at(-1) === 'running' || /^sent(?: \([^()]+\))?$/.test(kept.at(-1)))) { kept.push(part); continue; }
    const words = part.split(' ');
    for (let size = words.length - 1; size > 0; size--) if (RESULT_PART.test(words.slice(0, size).join(' '))) { kept.push(words.slice(0, size).join(' ')); break; }
    break;
  }
  return kept.length ? kept.join(' · ') : sentence.split(' ')[0];
}
export function runtimeLines(text) {
  return [...String(text ?? '').matchAll(LINE_PATTERN)].map(match => {
    const groups = [...match[1].matchAll(/\(([^)]*)\)/g)].map(group => group[1].trim());
    const story = groups.find(group => group && group.toUpperCase() !== 'DRAFT' && group !== 'all Stories') ?? null;
    const result = resultParts(match[2].replace(/\s+/g, ' ').trim());
    return { story, draft: groups.some(group => group.toUpperCase() === 'DRAFT'), result,
      line: `${PROMPT_TESTS_LABEL}${match[1].replace(/\s+/g, ' ')}: ${result}`, pass: result.includes('✓') && !result.includes('✗') };
  });
}
// The Prompt tests lines that pdd wrote as results in a PR body's top block: "pdd result:" lines and plain (receipt or older) lines.
// The Steps overview, full summaries, Verify and every agent note are never read.
export function recordedRuntimeLines(text) {
  const lines = [], rows = String(text ?? '').split('\n');
  // A readable description (#3042) keeps pdd's lines at the top of its Details section; the readable part above it holds no result line.
  const open = rows.findIndex(row => /^<details\b/i.test(row));
  for (const line of open >= 0 && rows[open] === DETAILS_OPEN ? rows.slice(open + 1) : rows) {
    if (/^#{1,6}\s/.test(line) || /^<details\b/i.test(line)) break;
    if (line.startsWith('pdd result:') || LABEL_START.test(line)) lines.push(line);
  }
  return runtimeLines(lines.join('\n'));
}
// One line per Story: a Story checked again keeps its place and takes its latest line.
const latestStories = lines => [...new Map(lines.filter(line => line.story).map(line => [line.story, line])).values()];
// The total over the Stories, added up by pdd: a pasted overall line can cover only the Stories checked last.
// ✓ only when every Story passes, DRAFT when any Story is a draft; a count goes in only when every line has it.
function totalLine(stories) {
  const sum = pattern => {
    const found = stories.map(line => line.result.match(pattern));
    return found.every(Boolean) ? found.reduce((total, match) => [total[0] + Number(match[1]), total[1] + Number(match[2] ?? 0)], [0, 0]) : null;
  };
  const criteria = sum(/(\d+) of (\d+) criteria/), checks = sum(/(\d+)\/(\d+) checks/), calls = sum(/(\d+) AI calls?/);
  const counts = [criteria && `${criteria[0]} of ${criteria[1]} criteria`, checks && `${checks[0]}/${checks[1]} checks`,
    calls && `${calls[0]} AI call${calls[0] === 1 ? '' : 's'}`].filter(Boolean).join(' · ');
  const mark = stories.every(line => line.pass) ? '✓' : stories.some(line => line.result.includes('✗')) ? '✗' : stories.find(line => !line.pass).result.split(/[\s·]+/)[0];
  const result = !counts ? mark : /^[✓✗]$/.test(mark) ? `${mark} ${counts}` : `${mark} · ${counts}`;
  return `${PROMPT_TESTS_LABEL} (all Stories)${stories.some(line => line.draft) ? ' (DRAFT)' : ''}: ${result}`;
}
// The Prompt tests lines for the top of a PR: with Story names, one line per Story and then pdd's total (when there
// are two or more); without, the lines as the chat wrote them.
function runtimeTop(text) {
  const lines = runtimeLines(text), stories = latestStories(lines);
  if (!stories.length) return lines.map(line => line.line);
  return [...stories.map(line => line.line), ...(stories.length > 1 ? [totalLine(stories)] : [])];
}
export function matchesSource(record, root, fingerprint, capture = captureSource) {
  const source = record.source;
  if (!source?.sha256) return false;
  if (source.kind === 'git-content-v1') return fingerprint !== null && fingerprint === source.sha256;
  if (source.kind === 'runtime-capture-v1') {
    const selection = {tests:source.tests,appMap:null,...(Object.hasOwn(source,'excludeFixtureProjects') ? {excludeFixtureProjects:source.excludeFixtureProjects} : {})};
    try {
      if (capture(root, selection).sha256 !== source.sha256) return false;
      return !source.nativeSource || !!source.nativeSource.sha256 && capture(root,{...selection,tests:source.nativeSource.tests}).sha256 === source.nativeSource.sha256;
    } catch { return false; }
  }
  return false;
}
// Registration authority is independent of receipt content and source equality.
const evidenceTests = tests => {
  if (!Array.isArray(tests) || !tests.length || tests.some(path => typeof path !== 'string' || !path || /[\\\x00-\x1f\x7f]/.test(path)
    || path.startsWith('/') || /^[A-Za-z]:/.test(path) || path.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git'))
    || new Set(tests).size !== tests.length) throw Error('Select nonempty unique safe authored-relative test paths.');
  return [...tests].sort();
};
const selectionEqual = (a,b) => sameFact(evidenceTests(a),evidenceTests(b));
const associationKey = a => JSON.stringify([a.workspaceRoot,evidenceTests(a.tests),a.source_sha256]);
function ownedPr1Head(run) {
  const area = askArea(run), pr = area && prOf(run,area.name);
  if (!pr || !Number.isSafeInteger(pr.number) || pr.url !== `https://github.com/${run.repo}/pull/${pr.number}` || !commitSha(pr.publishedHeadSha))
    throw Error('The owned recorded PR 1 head is missing or unavailable.');
  return pr.publishedHeadSha;
}
function selectedCapture(root,tests,capture=captureSource) {
  const visible=new Set(gitFiles(root));
  if(tests.some(path=>!visible.has(path)))throw Error('A selected authored source is missing or unavailable.');
  return capture(root,{tests,appMap:null});
}
const ANCHOR_FOLDER = {pr1:'evidence-pr1',before:'evidence-before'};
function frozenRoot(run,head,stage='pr1') { return join(realpathSync(run.runDir),ANCHOR_FOLDER[stage],head); }
// The before stage names its historical source by an explicit full commit id: the caller's reconstruction provenance.
function beforeHead(a) {
  if (!commitSha(a.sourceAnchor?.head) || a.sourceAnchor.head !== a.sourceAnchor.head.toLowerCase()) throw Error('The registered before commit is missing or invalid.');
  return a.sourceAnchor.head;
}
// Same Story: every selected test at the historical commit is a current test of the run with the same story_path.
function sameStoryTests(run,frozen,tests) {
  const current=new Set(gitFiles(run.root));
  for (const path of tests) {
    let then,now;
    try { then=JSON.parse(readFileSync(join(frozen,path),'utf8')).story_path; now=current.has(path)?JSON.parse(readFileSync(join(run.root,path),'utf8')).story_path:undefined; } catch { then=undefined; }
    if (typeof then !== 'string' || then !== now) throw Error(`${path} is not a current test of the same Story at that commit.`);
  }
}
function checkedAssociation(run,a,capture=captureSource) {
  if (a.runId !== run.runId || a.repo !== run.repo || !['current','pr1','before'].includes(a.stage)
    || !/^[a-f0-9]{64}$/.test(a.source_sha256 ?? '') || realpathSync(a.workspaceRoot) !== a.workspaceRoot
    || a.registration?.operation !== 'evidence-associate' || !Number.isFinite(a.registration.at)
    || a.registration.cwd !== realpathSync(run.root)) throw Error('The evidence association has a different run, owner, producer or registration.');
  evidenceTests(a.tests);
  const head = a.stage === 'pr1' ? ownedPr1Head(run) : a.stage === 'before' ? beforeHead(a) : null;
  const root = a.stage === 'current' ? realpathSync(run.root) : frozenRoot(run,head,a.stage);
  if (a.sourceAnchor?.root !== root || a.sourceAnchor?.head !== head || realpathSync(root) !== root)
    throw Error('The registered stage source anchor is missing, changed or unrelated.');
  if (selectedCapture(root,a.tests,capture).sha256 !== a.source_sha256) throw Error('The registered stage source has changed or is unavailable.');
  if (a.stage === 'current' && selectedCapture(a.workspaceRoot,a.tests,capture).sha256 !== a.source_sha256)
    throw Error('The producer selected source has changed or is unavailable.');
  return root;
}
// One eligibility rule for import, status/Story counts and prepared PR lines.
function eligibleEvidence(run,record,{stage='current',root=run.root,fingerprint=null,capture=captureSource}={}) {
  try {
    // Only a registered before association establishes historical before-the-fix evidence.
    if (stage === 'before' && record.association?.stage !== 'before') return false;
    if (record.association) {
      const saved = record.association;
      const a = (run.evidenceAssociations ?? []).find(a => associationKey(a) === associationKey(saved));
      if (!a || a.stage !== saved.stage || !sameFact(a.sourceAnchor,saved.sourceAnchor) || a.runId !== saved.runId || a.repo !== saved.repo
        || !(saved.stage === stage || stage==='pr1' && saved.stage==='current' && run.area<=run.areas.indexOf(askArea(run))) || record.source?.sha256 !== saved.source_sha256 || !selectionEqual(record.source?.tests,saved.tests)
        || realpathSync(record.receipt?.repo) !== saved.workspaceRoot) return false;
      checkedAssociation(run,a,capture);
      return root===run.root || matchesSource(record,root,fingerprint,capture);
    }
    if (record.receipt) {
      const producer=realpathSync(record.receipt.repo);
      const a=(run.evidenceAssociations??[]).find(a=>a.workspaceRoot===producer && selectionEqual(a.tests,record.source?.tests) && a.source_sha256===record.source?.sha256);
      if(a) { if(a.stage!=='current')return false; checkedAssociation(run,a,capture); }
      else if(producer!==realpathSync(run.root))return false;
    }
    return matchesSource(record,root,fingerprint,capture);
  } catch { return false; }
}
// Materialize local immutable commit objects inside the run folder, never a ref
// or checkout in the authored repository. Canonical preflight still owns capture.
async function retainPr1Source(run,head,p,stage='pr1') {
  const target = frozenRoot(run,head,stage);
  if (existsSync(target)) return target;
  // A missing previously registered anchor must not be silently reconstructed.
  if ((run.evidenceAssociations ?? []).some(a => a.stage === stage && a.sourceAnchor?.root === target)) throw Error(`The retained ${stage === 'pr1' ? 'PR 1' : 'before-the-fix'} source is missing.`);
  const parent = dirname(target); mkdirSync(parent,{recursive:true,mode:0o700});
  if(realpathSync(parent)!==parent)throw Error('The retained source folder cannot traverse a symlink.');
  const temporary = mkdtempSync(join(parent,'.source-'));
  try {
    const tree = await p.execFile('git',['ls-tree','-r','-z',head],{cwd:run.root,encoding:'buffer'});
    const entries = Buffer.from(tree.stdout).toString('utf8').split('\0').filter(Boolean).map(row => {
      const match = /^(100644|100755|120000|160000) (blob|commit) ([a-f0-9]{40,64})\t(.+)$/.exec(row);
      if (!match) throw Error(`The ${stage === 'pr1' ? 'PR 1' : 'before-the-fix'} tree contains an unavailable source entry.`);
      evidenceTests([match[4]]);
      return {mode:match[1],oid:match[3],path:match[4]};
    });
    const response = await p.execFile('git',['cat-file','--batch'],{cwd:run.root,input:entries.filter(e=>e.mode!=='160000').map(e=>e.oid+'\n').join(''),encoding:'buffer',maxBuffer:512*1024*1024});
    const bytes = Buffer.from(response.stdout); let offset=0;
    for (const entry of entries) {
      if(entry.mode==='160000'){mkdirSync(join(temporary,entry.path),{recursive:true});continue;}
      const end=bytes.indexOf(10,offset), header=bytes.subarray(offset,end).toString('utf8').split(' '), size=Number(header[2]);
      if (end<0 || header[0]!==entry.oid || header[1]!=='blob' || !Number.isSafeInteger(size) || size<0 || end+1+size>=bytes.length) throw Error('The frozen PR 1 objects are unavailable.');
      const content=bytes.subarray(end+1,end+1+size), path=join(temporary,entry.path); offset=end+2+size;
      mkdirSync(dirname(path),{recursive:true});
      if (entry.mode==='120000') symlinkSync(content.toString('utf8'),path);
      else writeFileSync(path,content,{mode:entry.mode==='100755'?0o700:0o600,flag:'wx'});
    }
    await p.execFile('git',['init','-q',`--object-format=${head.length===64?'sha256':'sha1'}`],{cwd:temporary});
    await p.execFile('git',['update-index','-z','--index-info'],{cwd:temporary,input:entries.map(e=>`${e.mode} ${e.oid}\t${e.path}\0`).join('')});
    renameSync(temporary,target);
    return target;
  } finally {rmSync(temporary,{recursive:true,force:true});}
}
async function associateEvidenceWorkspaceCommand({ref,workspace,stage,tests,commit,cwd},ports) {
  const p=deps(ports),found=await resolveRun(ref,{cwd},p);
  if(found.error)return fail(found.error);
  const run=found.run;
  try {
    const owned=await gitContext(cwd,p),producer=typeof workspace==='string' && workspace.trim() && await gitContext(resolve(cwd,workspace),p);
    if(!owned || owned.toplevel!==realpathSync(run.root) || owned.commonDir!==realpathSync(run.commonDir)
      || realpathSync(run.runDir)!==realpathSync(runDirFor(owned.commonDir,run.number))) throw Error('Register evidence only from the selected run owned worktree.');
    if(!producer || realpathSync(resolve(cwd,workspace))!==producer.toplevel) throw Error('Supply the exact existing producer Git root.');
    if(!['current','pr1','before'].includes(stage))throw Error('Evidence stage must be current, pr1 or before.');
    if(stage==='before'?commit===undefined:commit!==undefined)throw Error('Give --commit with --stage before, and only then.');
    if(stage==='before'){
      if(typeof commit!=='string'||!/^(?:[a-f0-9]{40}|[a-f0-9]{64})$/.test(commit))throw Error('Give the full lowercase commit id of the checked source.');
      let resolved='';try{resolved=(await git(p,owned.toplevel,'rev-parse','--verify','--quiet',`${commit}^{commit}`)).trim();}catch{resolved='';}
      if(resolved!==commit)throw Error('The commit is not a local commit of this repository.');
    }
    const selection=evidenceTests(tests),head=stage==='pr1'?ownedPr1Head(run):stage==='before'?commit:null;
    const root=stage==='current'?owned.toplevel:await retainPr1Source(run,head,p,stage);
    if(stage==='before'){try{sameStoryTests(run,root,selection);}catch(error){throw Error(`${error.message} Register only an earlier result of the same Story.`);}}
    const captured=selectedCapture(root,selection);
    if(stage==='current' && selectedCapture(producer.toplevel,selection).sha256!==captured.sha256)throw Error('The producer source does not match the current authored selection.');
    const association={runId:run.runId,repo:run.repo,workspaceRoot:producer.toplevel,stage,sourceAnchor:{root,head},tests:selection,
      source_sha256:captured.sha256,registration:{operation:'evidence-associate',cwd:owned.toplevel,at:p.now()}};
    checkedAssociation(run,association);
    commitRun(run,p,latest=>{
      checkedAssociation(latest,association);
      latest.evidenceAssociations=[...(latest.evidenceAssociations??[]).filter(a=>associationKey(a)!==associationKey(association)),association];
    });
    return done(`Registered ${stage === 'pr1'?'PR 1':stage === 'before'?`before-the-fix (commit ${commit.slice(0,7)})`:'current'} evidence workspace for ${run.repo}#${run.number}. No check, approval or workflow progress was recorded.`);
  } catch(error) {if(error?.code==='workflow_run_save_failed')throw error;return fail(`Evidence workspace not registered: ${oneLine(error.message)}`);}
}
// Historical before-the-fix evidence is its own stage: it never enters current or PR 1 counts.
const beforeStage = record => record?.association?.stage === 'before';
export function storyCount(run, ports = {}) {
  const records = [...(run.runtimeHistory ?? []), ...Object.values(run.done ?? {}), ...(run.evidence ?? [])]
    .filter(record => runtimeLines(record.summary).length && beforeStage(record) === (ports.stage === 'before')).sort((a, b) => (a.at ?? 0) - (b.at ?? 0));
  if (!records.length) return null;
  const fingerprint = (ports.fingerprint ?? gitFingerprint)(run.root), compatible = records.filter(record => eligibleEvidence(run,record,{stage:ports.stage,root:run.root,fingerprint,capture:ports.capture}));
  const current = latestStories(compatible.flatMap(record => runtimeLines(record.summary)));
  const all = latestStories(records.flatMap(record => runtimeLines(record.summary)));
  const currentByStory = new Map(current.map(line => [line.story, line]));
  const counted = all.length ? all.map(line => currentByStory.get(line.story) ?? line) : (compatible.length ? compatible : records).flatMap(record => runtimeLines(record.summary)).slice(-1);
  const known = line => currentByStory.has(line.story) || !all.length && compatible.length > 0;
  const unknown = line => !known(line) || !line.pass && !line.result.includes('✗');
  const result = { pass: counted.filter(line => known(line) && line.pass).length, total: counted.length,
    failing: counted.filter(line => !unknown(line) && !line.pass && line.story).map(line => line.story) };
  const unresolved = counted.filter(unknown).map(line => line.story ?? 'all Stories');
  if (unresolved.length) result.unknown = unresolved;
  if (counted.some(line => !known(line))) result.evidence = 'Source changed, unavailable, or not recorded; saved results are unverified.';
  return result;
}
export function storyEvidence(run, { comparisonRoot } = {}) {
  // Only pdd's own recorded pdd test batches and checked receipts; Prompt tests lines typed into a summary are not evidence.
  const records = [...ownStoryRecords(run), ...(run.evidence ?? [])]
    .filter(record => runtimeLines(record.summary).length && !beforeStage(record)).sort((a, b) => (a.at ?? 0) - (b.at ?? 0));
  const root = comparisonRoot === undefined ? run.root : comparisonRoot;
  const current = new Map(), older = new Map(), fingerprint = root === null ? null : gitFingerprint(root);
  for (const record of records) {
    const compatible = root !== null && eligibleEvidence(run,record,{root,fingerprint});
    for (const row of latestStories(runtimeLines(record.summary))) {
      (compatible ? current : older).set(row.story, { story: row.story, pass: row.pass, current: compatible, result: row.result, at: record.at ?? 0 });
    }
  }
  return [...new Map([...older, ...current]).values()];
}
// The Story count in status reads only pdd's own results: the pdd test batches that done recorded (pddHistory and step
// pddResults) and receipts that pdd workflow evidence checked. Prompt tests lines an agent typed into a summary never count.
function ownStoryRecords(run) {
  const batches = new Map();
  for (const result of [...(run.pddHistory ?? []), ...Object.values(run.done ?? {}).flatMap(record => record?.pddResults ?? [])])
    if (result?.kind === 'pdd test' && result.sourceSha256 && Array.isArray(result.tests) && !batches.has(result.batch)) batches.set(result.batch, result);
  return [...batches.values()].map(result => ({ at: result.at, summary: (result.stories?.length ? result.stories : [result.summary]).join('\n'),
    ...(result.association?{association:result.association,receipt:{repo:result.producerRoot}}:{}),
    source: { kind: 'runtime-capture-v1', sha256: result.sourceSha256, tests: result.sourceTests ?? result.tests, ...(Object.hasOwn(result,'excludeFixtureProjects') ? {excludeFixtureProjects:result.excludeFixtureProjects} : {}), ...(result.nativeSource ? {nativeSource:result.nativeSource} : {}) } }));
}
// Registered before-the-fix results: the latest valid line per Story, with its commit and original batch.
export function beforeResults(run, ports = {}) {
  const rows = new Map();
  for (const record of (run.evidence ?? []).filter(beforeStage).sort((a, b) => (a.at ?? 0) - (b.at ?? 0))) {
    if (!eligibleEvidence(run, record, { stage: 'before', capture: ports.capture })) continue;
    for (const line of runtimeLines(record.summary)) if (line.story) rows.set(line.story, { story: line.story, pass: line.pass, line: line.line,
      commit: record.association.sourceAnchor.head, batch: /^\d{8}-\d{6}-[a-z0-9]{4}$/.test(record.receipt?.batch ?? '') ? record.receipt.batch : null });
  }
  return [...rows.values()];
}
const beforeLine = row => `Before the fix (commit ${row.commit.slice(0, 7)}${row.batch ? `, batch ${row.batch}` : ''}): ${row.line}`;
// null when the run has no check claim at all; { none: true } when it has a check or typed lines but no pdd result.
export function ownStoryCount(run, ports = {}) {
  const own = [...(run.evidence ?? []), ...ownStoryRecords(run)];
  // A Story that only typed lines name shows as unknown: without a source binding, storyCount never trusts its result.
  const typed = [...(run.runtimeHistory ?? []), ...Object.values(run.done ?? {})].filter(record => runtimeLines(record?.summary).length).map(({ at, summary }) => ({ at, summary }));
  if (own.length) return storyCount({ ...run, runtimeHistory: [], done: {}, evidence: [...typed, ...own] }, ports);
  const claimed = run.done?.check || typed.length;
  return claimed ? { pass: 0, total: 0, failing: [], none: true } : null;
}
const storyText = count => count.none ? `no pdd result (${NO_VERDICT})` : `${count.pass} of ${count.total} Stories pass${count.unknown?.length ? ` · ${count.unknown.length} unknown` : ''}`;
const shortLine = text => clip(text, 199);
// Report links in a check summary, each once: "Report (<story>): <url>" keeps the Story name; a bare link has none.
function reportLinks(text, env) {
  const links = new Map();
  for (const [, story, url] of String(text ?? '').matchAll(/(?:\bReport\s*(?:\(([^)]*)\))?:\s*)?(https?:\/\/[^\s)<>\]"';]+)/g)) {
    if (hasReportLink(url, env) && !links.has(url)) links.set(url, story && story.trim().toUpperCase() !== 'DRAFT' ? story.trim() : null);
  }
  return [...links].map(([url, story]) => `Report${story ? ` (${story})` : ''}: ${url} (report links expire after 7 days)`);
}

// The verdict line (RUNBOOK §14) and the "Before ✗ … → after ✓ …" line (or "Before: no prompt → …") of a bug check summary,
// one per line or joined with "; ". "; " inside the verdict sentence stays.
const VERDICT = new RegExp(`\\bVerdict:[^\\n]*?(?=;?\\s*(?:\\n|\\bBefore\\s*[✗✓:]|\\b${PROMPT_TESTS_WORDS}\\b|\\bReport\\b|$))`);
const CHANGE = new RegExp(`\\bBefore\\s*[✗✓:][^\\n]*?(?=;?\\s*(?:\\n|\\bVerdict:|\\b${PROMPT_TESTS_WORDS}\\b|\\bReport\\b|$))`);
const verdictLine = text => String(text).match(VERDICT)?.[0].trim() ?? null;
const changeLine = text => String(text).match(CHANGE)?.[0].trim() ?? null;

// verify.md in the PR body (0.1.6 tester: 100 lines of shell came before the vector table). pdd drops a leading "# Verify"
// (the PR has "## Verify"), nests the "## " headings one level down, and folds each code block of more than 15 lines that is
// not inside a <details> block into a closed one. When verify.md has no <details> of its own, the text before the first
// heading stays on top, then come the sections about vectors or results, the Formal check, other sections with a table,
// and the rest.
function verifyBody(text) {
  const lines = String(text).split('\n');
  while (lines.length && !lines[0].trim()) lines.shift();
  if (/^#\s+verify\s*$/i.test(lines[0] ?? '')) lines.shift();
  const own = /<details\b/i.test(text), sections = [{ heading: '', lines: [], table: false }];
  let details = 0;
  for (let at = 0; at < lines.length; at++) {
    const line = lines[at], fence = line.trim().match(/^(`{3,}|~{3,})(\S*)/), section = sections.at(-1);
    if (fence) {
      let end = at + 1;
      while (end < lines.length && !lines[end].trim().startsWith(fence[1])) end++;
      const block = lines.slice(at, end + 1), inner = Math.min(end, lines.length) - at - 1;
      const label = /^(?:sh|bash|zsh|shell|console)$/i.test(fence[2]) ? 'Commands' : 'Output';
      section.lines.push(...(!details && inner > 15 ? [`<details><summary>${label} (${inner} lines)</summary>`, '', ...block, '', '</details>'] : block));
      at = end; continue;
    }
    if (/<details\b/i.test(line)) details++;
    if (/<\/details>/i.test(line)) details = Math.max(0, details - 1);
    if (/^##\s/.test(line) && !details && !own) { sections.push({ heading: line, lines: [`#${line}`], table: false }); continue; }
    section.lines.push(/^##\s/.test(line) ? `#${line}` : line);
    if (/^\s*\|.*\|\s*$/.test(line)) section.table = true;
  }
  const rank = section => !section.heading ? -1 : /vector|result/i.test(section.heading) ? 0 : /formal/i.test(section.heading) ? 1 : section.table ? 2 : 3;
  return sections.map((section, index) => ({ section, index })).sort((a, b) => rank(a.section) - rank(b.section) || a.index - b.index)
    .map(({ section }) => section.lines.join('\n').trim()).filter(Boolean).join('\n\n');
}

// GitHub refuses a PR description over 65,536 characters (0.1.7 tester: a 105,489-character verify report, and every retry
// failed the same way). The body stays at most 60,000 characters (code points), so the marker and GitHub's count have room.
const BODY_BUDGET = 60_000, characters = text => [...text].length;
const reportsFailure = line => /✗|\bfail(?:s|ed|ing)?\b/i.test(line);
// An inline code span (a run of N backticks up to the next run of exactly N) shows a tag as text: it opens and closes nothing.
const outsideCode = line => line.replace(/(?<!`)(`+)(?!`).*?(?<!`)\1(?!`)/g, '');
const withoutTags = line => line.replace(/((?<!`)(`+)(?!`).*?(?<!`)\2(?!`))|<\/?(?:details|summary)\b[^>]*>/gi, (tag, code) => code ?? '');
// verify.md in at most `room` characters: the whole report when it fits. Else each <details> block becomes one line; if it is
// still too long, its first lines that fit (cut at a line end, a code fence closed), then the lines of the cut part that report
// a failure. A note says that this is a summary and where the full report is, so no failure is dropped in silence.
function verifyFit(text, room, env, description = false, formatted = false) {
  const full = description || formatted ? text : verifyBody(text);
  if (characters(full) <= room) return full;
  const note = what => description
    ? `_The existing PR 1 description has ${characters(text).toLocaleString('en-US')} characters. It was shortened to fit the complete description's 60,000-character budget: ${what}._`
    : `_The full verify report has ${characters(text).toLocaleString('en-US')} characters, more than a PR description can hold (GitHub's limit is 65,536). This is a summary: ${what}. The PR author has the full report: verify.md in the run folder._`;
  const lines = [], hiddenEvidence = new Set();
  let depth = 0, summary = null;
  for (const line of full.split('\n')) {
    const shown = outsideCode(line), opens = (shown.match(/<details\b/gi) ?? []).length, closes = (shown.match(/<\/details>/gi) ?? []).length;
    if (!depth && !opens) { lines.push(line); continue; }
    if (reportsFailure(line) && !/^\s*(`{3,}|~{3,})/.test(line)) hiddenEvidence.add(withoutTags(line));
    for (const reference of reportLinks(line, env)) hiddenEvidence.add(reference);
    summary ??= /<summary>(.*?)<\/summary>/i.exec(shown)?.[1].trim() || null;
    depth = Math.max(0, depth + opens - closes);
    if (!depth) { lines.push(`- ${summary ?? 'Details'}: not shown here.`); summary = null; }
  }
  if (hiddenEvidence.size) lines.push('', 'Evidence from the blocks not shown:', '', ...hiddenEvidence);
  const short = note('the long blocks are not shown');
  if (characters(lines.join('\n')) + characters(short) + 2 <= room) return `${lines.join('\n')}\n\n${short}`;
  const reserve = characters(note('its first 000000 lines; 000000 more lines are not shown, and 000000 of them report a failure (the first 000000 are listed below); 000000 report references are listed and 000000 are not shown')) + 256;
  const failRoom = Math.max(0, Math.min(8000, Math.floor((room - reserve) / 4))), keepRoom = Math.max(0, room - reserve - failRoom);
  let used = 0, at = 0, fence = null;
  for (; at < lines.length; at++) {
    const size = characters(lines[at]) + 1;
    if (used + size > keepRoom) break;
    used += size;
    const mark = lines[at].trim().match(/^(`{3,}|~{3,})/)?.[1];
    if (mark) fence = !fence ? mark : lines[at].trim().startsWith(fence) ? null : fence;
  }
  const kept = [...lines.slice(0, at), ...(fence ? [fence] : [])], failing = lines.slice(at).filter(line => reportsFailure(line) && !/^\s*(`{3,}|~{3,})/.test(line));
  const references = [...new Set(lines.slice(at).flatMap(line => reportLinks(line, env)))];
  const listed = [], linked = [];
  let left = room - reserve - used - 40;
  for (const line of failing) { if (characters(line) + 1 > left) break; listed.push(line); left -= characters(line) + 1; }
  const alreadyShown = [...kept, ...listed].join('\n');
  const remainingRefs = references.filter(line => {
    const url = line.match(/https?:\/\/[^\s)<>\]"';]+/)?.[0];
    return !url || !alreadyShown.includes(url);
  });
  for (const line of remainingRefs) { if (characters(line) + 1 > left) break; linked.push(line); left -= characters(line) + 1; }
  const what = `its first ${at} lines; ${lines.length - at} more lines are not shown, and ${failing.length} of them report${failing.length === 1 ? 's' : ''} a failure${listed.length < failing.length ? listed.length ? ` (the first ${listed.length} are listed below)` : ' (they do not fit here)' : ''}${remainingRefs.length ? `; ${linked.length} report references are listed and ${remainingRefs.length - linked.length} are not shown` : ''}`;
  return [...kept, ...(listed.length ? ['', 'Lines that report a failure, from the part not shown:', '', '```text', ...listed, '```'] : []), ...(linked.length ? ['', 'Report references from the part not shown:', '', ...linked] : []), '', note(what)].join('\n');
}

const withoutForgedMachineLines = text => String(text ?? '').split('\n').filter(line => !/^(?:Old-code proof:|Tests vs base:)/.test(line)).join('\n');
async function promptApprovalContext(run, p) {
  const commonDir = run.commonDir ?? (await gitContext(run.root, p))?.commonDir;
  if (!commonDir) throw Error('Cannot resolve Git common directory for prompt approvals.');
  return { commonDir };
}
async function matchingPromptApprovals(run, p) {
  const records = readPromptApprovals(await promptApprovalContext(run, p), p);
  if (!records.some(record => record.prompts.length)) return [];
  const published = new Map();
  for (const path of await changedFiles(run, p, true)) {
    if (!path.endsWith('.prompt.md')) continue;
    try { published.set(path, proseSha256(readFileSync(join(run.root, path), 'utf8'))); } catch { /* Deleted files have no current identity. */ }
  }
  return records.flatMap(record => {
    const prompts = record.prompts.filter(prompt => published.get(prompt.path) === prompt.proseSha256);
    return prompts.length ? [{ ...record, prompts }] : [];
  });
}
async function publicationEvidence(run, area, p) {
  const saved = { runId: run.runId, ...(Number.isFinite(run.startedAt) ? { startedAt: run.startedAt } : {}), runDir: run.runDir, root: run.root, baseSha: run.baseSha, baseBranch:run.baseBranch, workflow:run.workflow, number: run.number,
    bugCause: run.done.reproduce?.bugCause,
    decisions: run.decisions ?? [], promptApprovals: await matchingPromptApprovals(run, p),
    steps: run.areas.flatMap(item => item.steps).map(step => ({ step, summary: run.done[step]?.summary ?? '' })) };
  let observedHead, observedProof;
  const proofFiles = p.fs ?? { lstatSync, readFileSync };
  const evidence = await preparePrEvidence({ run: saved, isCode: prLabel(run, area) !== 'PR 1' }, {
    currentHead: async ({ root, baseBranch }) => {
      try { await git(p,root,'check-ref-format',`refs/heads/${baseBranch}`);await git(p,root,'fetch','origin',`refs/heads/${baseBranch}:refs/remotes/origin/${baseBranch}`);const headSha=await git(p,root,'rev-parse','--verify','HEAD^{commit}');return observedHead = {headSha,baseSha:await git(p,root,'merge-base',headSha,`refs/remotes/origin/${baseBranch}`),error:''}; }
      catch { return { headSha: '', baseSha:'', error: 'Current Git head unavailable.' }; }
    },
    readOldCodeProof: async ({runDir}) => {
      try {
        const path = join(runDir, 'old-code-proof.json');
        if (!proofFiles.lstatSync(path).isFile()) return {content:'',error:'Proof is not a regular file.'};
        observedProof = proofFiles.readFileSync(path, 'utf8');
        return {content:observedProof,error:'',savedAt:proofFiles.lstatSync(path).mtimeMs};
      } catch (error) { return {content:'',error:error.code === 'ENOENT' ? 'missing' : 'Proof could not be read.'}; }
    }
  });
  if (prLabel(run, area) !== 'PR 1') {
    evidence.nativeLine = 'Native tests: unknown (no current machine counts).';
    try {
      const record = JSON.parse(observedProof);
      if (!['not-run','stale','unavailable'].includes(evidence.proofStatus) && validateProofRecord(record) && record.runId === run.runId && record.headSha === observedHead?.headSha && record.baseSha === observedHead?.baseSha
          && !record.interruptSignal && [0,1].includes(record.head.exitCode) && !record.head.signal && !record.head.timedOut && !record.head.outputLimited && !record.head.error && !record.head.setupError) {
        const facts = new Map();
        for (const line of record.head.stdoutTail) {
          const match = /^# (tests|pass|fail|cancelled|skipped|todo) (\d+)$/.exec(line);
          if (match) { if (facts.has(match[1])) throw Error('Ambiguous test summary'); facts.set(match[1], Number(match[2])); }
        }
        const total = facts.get('tests'), passed = facts.get('pass'), failed = facts.get('fail');
        if ([total, passed, failed].every(Number.isSafeInteger) && total >= 0 && passed + failed + (facts.get('cancelled') ?? 0) + (facts.get('skipped') ?? 0) + (facts.get('todo') ?? 0) === total)
          evidence.nativeLine = `Native tests (current old-code proof, new-code output): ${passed}/${total} passed; ${failed} failed.`;
      }
    } catch { /* Missing, stale or unparseable machine output supplies no counts. */ }
  }
  if (run.publicationPending) evidence.lines.unshift('Check evidence: publication-pending (source is being published).');
  // pdd's own pdd test and pdd lint results lead the body; the code PR's prove result is its Old-code proof line.
  const results=ownResults(run,p);
  evidence.pddLines = resultLines(results, { kinds: ['pdd test', 'pdd lint', ...results.some(result=>result.kind==='native evidence')?['native evidence']:[]] });
  // The readable part (#3042) reads the same records as plain facts: results, approvals and the proof judgment.
  evidence.results = results;
  evidence.approvals = approvalRecords(saved).map(item => ({ route: item.route, at: item.at, words: typeof item.words === 'string' ? item.words : null }));
  return evidence;
}
function evidenceFit(lines, room, env) {
  if (characters(lines.join('\n')) <= room) return lines;
  const kept = [], omitted = [];
  const notice = rows => {
    const approvals = rows.filter(row => /^Approved in /.test(row)).length;
    return `Evidence omitted: ${approvals ? `${approvals} approval evidence records omitted; ` : ''}${rows.length} labels, ${rows.filter(reportsFailure).length} failure lines, ${rows.flatMap(line => reportLinks(line, env)).length} report references. The full evidence remains in the run folder.`;
  };
  let machineRoom = lines.some(line => line.startsWith('Old-code proof:')) ? 100 : 0;
  let left = Math.max(0, room - characters(notice(lines)) - 1 - machineRoom);
  for (const line of lines) {
    if (line.startsWith('Old-code proof:')) { left += machineRoom; machineRoom = 0; }
    if (characters(line) + 1 <= left) { kept.push(line); left -= characters(line) + 1; }
    else {
      omitted.push(line);
      const unavailable = 'Old-code proof: unavailable (result omitted; exceeds description budget).';
      if (line.startsWith('Old-code proof:') && characters(unavailable) + 1 <= left) { kept.push(unavailable); left -= characters(unavailable) + 1; }
    }
  }
  kept.push(notice(omitted));
  return kept;
}
// Approval rows are complete JSON-encoded records. Shorten the display by omitting
// whole records, never by cutting the person's words or changing durable history.
function publicationFit(lines, approvals, room, env) {
  const notice = count => `Evidence omitted: ${count} approval evidence records omitted. Full approval evidence, including exact words, remains in the durable local approval journal and run history.`;
  const approvalSize = characters(approvals.join('\n'));
  const reserve = approvals.length ? Math.min(1000, approvalSize + characters(notice(approvals.length)) + 2) : 0;
  const lifted = evidenceFit(lines, Math.max(0, room - reserve), env);
  const available = Math.max(0, room - characters(lifted.join('\n')) - (lifted.length ? 2 : 0));
  if (approvalSize <= available) return { lifted, approvals };
  const kept = [];
  let left = Math.max(0, available - characters(notice(approvals.length)) - 1);
  for (const line of approvals) {
    const size = characters(line) + 1;
    if (size <= left) { kept.push(line); left -= size; }
  }
  return { lifted, approvals: [...kept, notice(approvals.length - kept.length)] };
}
// The Steps overview cuts each summary to a short line; it is never the only copy that a reviewer can read. Below it, one
// closed block keeps every whole summary as inert code spans: no summary line starts a body line, so its labels, HTML,
// mentions and markers stay text. The block has the lowest priority in the body budget. When it does not fit, the longest
// summaries are shortened first, each cut shows " …", and one line names each shortened step and what was left out.
const AGENT_NOTE = 'Agent note — not checked by pdd';
const FULL_SUMMARIES = '<details><summary>Full step summaries</summary>', SLOT = '\u0000';
function codeSpan(line) {
  const text = line.replaceAll('pdd-workflow:', 'pdd-workflow\\u003a').replaceAll('pdd-product:', 'pdd-product\\u003a');
  const fence = '`'.repeat([...text.matchAll(/`+/g)].reduce((most, run) => Math.max(most, run[0].length), 0) + 1);
  const padding = /^`|`$/.test(text) ? ' ' : '';
  return `${fence}${padding}${text}${padding}${fence}`;
}
// The first `size` characters (code points) of a summary, moved back to a word end and to the start of a URL that crosses the cut.
function summaryStart(text, size) {
  const points = [...text];
  if (points.length <= size) return text;
  let kept = points.slice(0, size).join('');
  const url = [...text.matchAll(/https?:\/\/\S+/g)].find(match => match.index < kept.length && match.index + match[0].length > kept.length);
  if (url) kept = kept.slice(0, url.index);
  else if (/\S/.test(points[size])) kept = kept.replace(/\s+\S*$/, '');
  return kept.trimEnd();
}
const SHORTENED = /^_\d+ step summar(?:y was|ies were) shortened to fit the PR size limit: .*\._$/;
// The steps of one PR area (those since the previous PR) and their whole summaries after the PR cleaning.
function prSteps(run, area) {
  const index = run.areas.findIndex(item => item.name === area.name), from = run.areas.slice(0, index).map((item, at) => item.gate === 'pr' ? at + 1 : 0).reduce((a, b) => Math.max(a, b), 0);
  return run.areas.slice(from, index + 1).flatMap(item => item.steps).filter(step => run.done[step]);
}
const noteRuntime = text => String(text).replace(LINE_PATTERN, match => `Saved runtime receipt (unverified in this agent note): ${match}`);
const cleanSummary = (run, step) => hideLocalPaths(redactTry(noteRuntime(withoutForgedMachineLines(run.done[step].summary))), run);
// render(section) is the whole body with that block; the block takes the room that is left: whole when it fits, else one
// common length for the longest summaries, as large as the search finds within the limit.
function withSummaries(steps, texts, render, limit) {
  const fits = size => characters(render(fullSummaries(steps, texts, size))) <= limit;
  let low = 0, high = Object.values(texts).reduce((most, text) => Math.max(most, characters(text)), 0);
  if (fits(Infinity)) return render(fullSummaries(steps, texts, Infinity));
  while (high - low > 1) { const middle = Math.floor((low + high) / 2); if (fits(middle)) low = middle; else high = middle; }
  return render(fullSummaries(steps, texts, low));
}
function fullSummaries(steps, texts, size) {
  if (!steps.length) return [];
  const shortened = [];
  const items = steps.map(step => {
    if (!texts[step]) return `- **${step}**: done`;
    const kept = summaryStart(texts[step], size), left = characters(texts[step]) - characters(kept);
    if (left) shortened.push(`${step} (${left.toLocaleString('en-US')} characters left out)`);
    return `- **${step}**: ${AGENT_NOTE}: ${kept.split('\n').filter(Boolean).map(codeSpan).join('<br>')}${left ? `${kept ? ' ' : ''}…` : ''}`;
  });
  const notice = shortened.length ? [`_${shortened.length} step ${shortened.length === 1 ? 'summary was' : 'summaries were'} shortened to fit the PR size limit: ${listed(shortened)}. The PR author has the full summaries in the run folder._`, ''] : [];
  return [...notice, FULL_SUMMARIES, '', ...items, '', '</details>'];
}
function publicationRuntime(run, env, stage = 'current') {
  if (run.publicationPending) return [];
  const fingerprint = gitFingerprint(run.root);
  const records = [...(run.runtimeHistory ?? []), ...Object.values(run.done ?? {}), ...(run.evidence ?? [])]
    .filter(record => runtimeLines(record.summary).length && eligibleEvidence(run,record,{stage,fingerprint})).sort((a,b) => (a.at ?? 0) - (b.at ?? 0));
  const stories = new Map();
  for (const record of records) for (const line of runtimeLines(record.summary)) if (line.story) stories.set(line.story, { line, record });
  // Lines that an agent typed or pasted into a step summary stay agent notes; only a receipt that pdd workflow evidence checked is not.
  const receipts = new Set(run.evidence ?? []), note = (record, line) => receipts.has(record) ? line : `${AGENT_NOTE}: ${line}`;
  if (!stories.size) {
    const record = records.at(-1);
    return record ? [...runtimeTop(record.summary), ...reportLinks(record.summary, env)].map(line => note(record, line)) : [];
  }
  const selected = [...stories.values()];
  const reports = selected.flatMap(({line, record}) => reportLinks(record.summary, env).filter(report => {
    const name = /^Report \(([^)]+)\):/.exec(report)?.[1];
    return !name || name === line.story;
  }).map(report => note(record, report)));
  const total = selected.length > 1 ? [totalLine(selected.map(item => item.line))].map(line => selected.every(item => receipts.has(item.record)) ? line : `${AGENT_NOTE}: ${line}`) : [];
  return [...selected.map(item => note(item.record, item.line.line)), ...total, ...new Set(reports)];
}
// #3042: the facts for the readable part of a PR. Agent words come only from the labeled PR fields in the done
// summaries; every check and proof row comes from pdd's own records, CI and the checker verdict.
async function diffStat(run, p, base, head) {
  try {
    const out = await rawGit(p, run.root, 'diff', '--numstat', '--no-renames', '-z', `refs/remotes/origin/${base}...${head}`);
    const files = [];
    for (const row of out.split('\0').filter(Boolean)) {
      const match = /^(-|\d+)\t(-|\d+)\t([\s\S]+)$/.exec(row.replace(/^\n/, ''));
      if (match) files.push({ path: match[3], added: match[1] === '-' ? 0 : Number(match[1]), removed: match[2] === '-' ? 0 : Number(match[2]), binary: match[1] === '-' });
    }
    return { added: files.reduce((sum, file) => sum + file.added, 0), removed: files.reduce((sum, file) => sum + file.removed, 0), files };
  } catch { return null; }
}
// Coverage is a scope fact, never an agent's claim. Classify before savedReadable bounds the file list.
async function coverageOnlyDiff(run, p, diff, head) {
  if (!diff?.files?.length || (diff.count !== undefined && diff.count !== diff.files.length)) return false;
  const entries = new Set(diff.files.filter(file => /\.(?:test|spec)\.(?:[cm]?js|jsx|tsx?)$|(?:^|\/)test_[^/]*\.py$|_test\.(?:py|go)$/.test(file.path)).map(file => file.path));
  for (const file of diff.files) {
    if (file.added <= 0 || !/(?:^|\/)tests?\/.*\.json$/.test(file.path)) continue;
    try {
      // Use the same head as the diff, not an uncommitted scenario or an arbitrary JSON fixture.
      const doc = JSON.parse(await rawGit(p, run.root, 'show', `${head}:${file.path}`));
      if (doc?.schema_version === 'prompt-runtime.program-scenario.v1' && Array.isArray(doc.steps) && doc.steps.length > 0) entries.add(file.path);
    } catch { /* Missing or malformed scenario bytes cannot establish executable coverage. */ }
  }
  const testPath = path => /^(?:tests?|__tests__)\//.test(path) || entries.has(path);
  return diff.files.every(file => testPath(file.path)) && diff.files.some(file => entries.has(file.path) && file.added > 0);
}
// Autopilot's mode for an automatic run (auto, observe or off), read like its handoff; a manual run has none.
function automaticFacts(run, p) {
  if (!validSavedAutomaticOrigin(run)) return null;
  let mode = 'auto', activatedAt = NaN;
  try {
    const configured = JSON.parse(readFileSync(join(realpathSync(run.sourceRoot), 'pdd.json'), 'utf8'))?.autopilot?.mode;
    if (['auto', 'observe', 'off'].includes(configured)) mode = configured;
  } catch { /* An unreadable configuration keeps the automatic start's mode. */ }
  try {
    const root = realpathSync(run.sourceRoot), id = createHash('sha256').update(root).digest('hex').slice(0, 20);
    const folder = p.autopilotStateRoot ?? join(p.env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
    const saved = JSON.parse(readFileSync(join(folder, `${id}.json`), 'utf8'));
    if (mode !== 'off' && ['auto', 'observe'].includes(saved?.startAction?.mode)) mode = saved.startAction.mode;
    activatedAt = Date.parse(saved?.activatedAt);
  } catch { /* No saved Autopilot state: the run's own start date stands in. */ }
  return { mode, startedAt: Number.isFinite(activatedAt) ? activatedAt : run.startedAt };
}
async function githubLogin(run, p) {
  if (p.githubLogin !== undefined) return p.githubLogin;
  try {
    const reply = await p.execFile('gh', ['api', 'user', '--jq', '.login'], { cwd: run.root });
    const login = reply.code === undefined || reply.code === 0 ? String(reply.stdout ?? '').trim() : '';
    // One read per command: the pending and final descriptions name the same person.
    return p.githubLogin = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/.test(login) ? login : null;
  } catch { return p.githubLogin = null; }
}
// One PR's state, CI and base on GitHub (with `view`, also its description, head and comments, in the same read); a read
// problem stays unknown.
async function prStatusOf(run, pr, p, cwd = run.root, view = false) {
  try { return await (p.readPrStatus ?? readWorkflowPrStatus)({ cwd, url: pr.url, ...(view ? { view } : {}) }, p.commandPorts); } catch { return { state: 'unknown', ci: 'unknown' }; }
}
// The checker verdict for one head, from the comments of a read that has them, else from its own read.
async function checkerOf(pr, headSha, p, cwd, view) {
  try { return await (p.readPrChecker ?? readWorkflowPrChecker)({ cwd, url: pr.url, headSha, ...(Array.isArray(view?.comments) ? { comments: view.comments } : {}) }, p.commandPorts); } catch { return null; }
}
// CI and the checker verdict for the head of a published PR, and its base on GitHub. A read problem stays unknown.
async function publishedChecks(run, pr, headSha, p) {
  const status = await prStatusOf(run, pr, p, run.root, true);
  return { ci: status.ci, base: status.base ?? null, checker: await checkerOf(pr, headSha, p, run.root, status.view) };
}
function reviewVerdict(run, area) {
  if (!area.steps.includes('review')) return null;
  try {
    const first = readFileSync(join(run.runDir, 'review.md'), 'utf8').split(/\r?\n/).find(line => line.trim()) ?? '';
    const match = /^Review:\s*(?:(no)|(\d+))\s+must-fix\b/i.exec(first.trim());
    return match ? { mustFix: match[1] ? 0 : Number(match[2]) } : 'missing';
  } catch { return 'missing'; }
}
function formalCounterexample(run) {
  try {
    const path = join(run.runDir, 'replay-evidence.json');
    if (!lstatSync(path).isFile() || lstatSync(path).size > 4 * 1024 * 1024) return null;
    const value = JSON.parse(readFileSync(path, 'utf8'))?.formal?.counterexample;
    return value === undefined || value === null ? null : typeof value === 'string' ? value : JSON.stringify(value);
  } catch { return null; }
}
const resultText = summary => oneLine(summary).replace(/^[^:]*:\s*/, '');
const STORY_FILE = /(?:^|\/)user_stories\/[^/]+\.md$/;
// The Story paths that the step summaries name; `extra` is the summary of a step that `done` records now.
const safeStoryPath = path => typeof path === 'string' && isStoryPath(path) && !isAbsolute(path)
  && !/^[A-Za-z]:[\\/]/.test(path) && !path.split('/').includes('..') && !/[\u0000-\u001f\u007f-\u009f\u2028\u2029]/.test(path);
function namedStories(run, extra = '') {
  const summaries = [...run.areas.flatMap(item => item.steps).filter(step => run.done[step]).map(step => String(run.done[step]?.summary ?? '')), String(extra)];
  let paths; try { paths = gitFiles(run.root).filter(safeStoryPath); } catch { return []; }
  // Resolve longer repository filenames first, so a complete reference owns its whole span.
  const selected = new Set();
  for (const summary of summaries) {
    const spans = [];
    for (const path of [...paths].sort((a, b) => b.length - a.length)) {
      for (let at = summary.indexOf(path); at !== -1; at = summary.indexOf(path, at + 1)) {
        const start = summary.slice(Math.max(0, at - 2), at) === './' ? at - 2 : at;
        const end = at + path.length;
        const before = summary[start - 1] ?? '', after = summary.slice(end);
        if (!/[\p{L}\p{N}_./\\-]/u.test(before) && !/^[\p{L}\p{N}_/\\-]|^\.[\p{L}\p{N}_]/u.test(after)
          && !spans.some(([left, right]) => start >= left && end <= right)) {
          selected.add(path); spans.push([start, end]);
        }
      }
    }
  }
  return paths.filter(path => selected.has(path));
}
// PR 1 ownership survives its merge into main and the deletion of its branch.
async function pr1StoryPaths(run, p) {
  const area = askArea(run), pr1 = area && prOf(run, area.name);
  if (!pr1) return [];
  const saved = pr1.readable?.facts?.storyPaths;
  if (Array.isArray(saved)) return saved;
  // A legacy record has no ownership snapshot. The PR's file list distinguishes
  // its changes from upstream updates, including fast-forwards before its first
  // commit. Local history since baseSha cannot establish that distinction.
  try {
    const reply = await p.execFile('gh', ['api', `repos/${run.repo}/pulls/${pr1.number}/files?per_page=100`, '--paginate', '--slurp'], { cwd: run.root });
    if (reply.code !== undefined && reply.code !== 0) return [];
    const pages = JSON.parse(reply.stdout);
    if (!Array.isArray(pages) || !pages.every(Array.isArray)) return [];
    return pages.flatMap(page => page.map(file => file?.filename));
  } catch { return []; }
}
// Readable Stories come from the current run-base diff, PR 1 or explicit Story references/approval.
// The original baseSha also sees changes inherited from main and cannot establish Story ownership.
function runStoryPaths(run, files) {
  const approved = (run.storyApproval?.fingerprint?.stories ?? []).map(story => story.path);
  return [...new Set([...files, ...namedStories(run), ...approved])].filter(path => safeStoryPath(path) && STORY_FILE.test(path));
}
// #3029: true when a Story of the run (changed or named, user_stories/**/S.md) or the Story of an anchored scenario has
// `## Rules to check`; false when pdd read a Story of the run and none has it; null (unknown) when pdd found no Story file.
function storyRulesToCheck(run, files, extra) {
  const anchored = (run.replayBaseline?.vectors ?? []).map(vector => vector?.snapshot?.story_path);
  const paths = [...new Set([...files, ...namedStories(run, extra), ...anchored])].filter(safeStoryPath);
  let read = false;
  for (const path of paths) {
    let text; try { text = readFileSync(join(run.root, path), 'utf8'); } catch { continue; }
    if (/^##[ \t]+Rules to check[ \t]*$/im.test(text)) return true;
    read = true;
  }
  return read ? false : null;
}
const rulesToCheck = async (run, p, extra) => storyRulesToCheck(run, await changedFiles(run, p), extra);
async function readableFacts(run, area, p, evidence, { drafts = [], pending = false, published = null, base, head = 'HEAD', replay = null } = {}) {
  const label = prLabel(run, area), layout = label === 'PR 1' ? 'spec' : 'code';
  const steps = prSteps(run, area), all = run.areas.flatMap(item => item.steps).filter(step => run.done[step]);
  const own = readPrFields(steps.map(step => run.done[step]?.summary ?? ''));
  const earlier = readPrFields(all.filter(step => !steps.includes(step)).map(step => run.done[step]?.summary ?? ''));
  const verdict = [run.done.check?.summary, ...steps.toReversed().map(step => run.done[step]?.summary)].filter(Boolean).map(verdictLine).find(Boolean);
  const fields = { ...own, problem: own.problem ?? earlier.problem, area: own.area ?? earlier.area,
    verdict: layout === 'spec' ? verdict?.replace(/^Verdict:\s*/, '') ?? own.verdict : own.verdict,
    cases: own.cases.length ? own.cases : layout === 'code' ? earlier.cases.map(({ after, ...row }) => row) : [] };
  const files = await changedFiles(run, p);
  const diffBase = base ?? run.prBase ?? run.baseBranch;
  const diff = await diffStat(run, p, diffBase, head);
  const storyDiff = diffBase === run.baseBranch ? diff : await diffStat(run, p, run.baseBranch, head);
  const changed = new Set(files);
  const retained = layout === 'code' ? await pr1StoryPaths(run, p) : [];
  const storyPaths = runStoryPaths(run, [...(storyDiff?.files ?? []).map(file => file.path).filter(path => changed.has(path)), ...retained]);
  const stories = [], missing = [];
  for (const path of storyPaths) {
    let text = null;
    try { text = readFileSync(join(run.root, path), 'utf8'); } catch { /* A Story that is gone has no line. */ }
    const story = text === null ? null : userStory(text);
    if (story) stories.push(story); else if (text !== null) missing.push(path);
  }
  const results = evidence.results ?? [], test = results.find(result => result.kind === 'pdd test'), lint = results.find(result => result.kind === 'pdd lint');
  const testResult = test ? resultText(test.summary) : '', lintCount = lint && /(\d+) of (\d+) tests pass/.exec(lint.summary);
  const native = /(\d+)\/(\d+) passed/.exec(evidence.nativeLine ?? '');
  const automatic = automaticFacts(run, p), mode = !automatic || automatic.mode === 'off' ? 'manual' : automatic.mode;
  const approvals = evidence.approvals ?? [];
  const proofDiff = (base ?? run.prBase ?? run.baseBranch) === run.baseBranch ? diff : await diffStat(run, p, run.baseBranch, head);
  const proofKind = run.workflow === 'small-change' && label === 'the PR' && evidence.proofStatus === 'old-passes' && await coverageOnlyDiff(run, p, proofDiff, head) ? 'coverage' : 'defect';
  const formal = layout === 'code' && area.steps.includes('formal') && !replay ? readFormalEvidence(run) : null;
  const paths = (diff?.files ?? []).map(file => file.path);
  const prompts = paths.filter(path => path.endsWith('.prompt.md')), storyFiles = paths.filter(path => /(?:^|\/)user_stories\/[^/]+\.md$/.test(path));
  const rest = paths.filter(path => !prompts.includes(path) && !storyFiles.includes(path));
  const tests = rest.filter(path => /(?:^|\/)(?:tests?|__tests__|fixtures)\//.test(path) || /\.(?:test|spec)\.[^/]+$/.test(path)), others = rest.filter(path => !tests.includes(path));
  const count = (number, word) => `${number} ${word}${number === 1 ? '' : 's'}`;
  const holds = [...prompts.slice(0, 3).map(path => `the prompt \`${path.split('/').at(-1)}\``), ...(prompts.length > 3 ? [count(prompts.length - 3, 'more prompt')] : []),
    ...(storyFiles.length ? [storyFiles.length > 1 ? `${storyFiles.length} Stories` : 'the Story'] : []),
    ...(tests.length ? [count(tests.length, 'test file')] : []), ...(others.length ? [`${count(others.length, 'other file')} (not prompts, Stories or tests)`] : [])];
  const ask = askArea(run), pr1 = ask && prOf(run, ask.name);
  const pr2 = layout === 'spec' ? run.areas.filter(item => item !== area && item.gate === 'pr').map(item => prOf(run, item.name)).find(Boolean) ?? null : null;
  const stacked = layout === 'code' && Boolean(pr1) && Boolean(run.prBase) && run.prBase !== run.baseBranch;
  // A code PR reads PR 1's state and CI on every render, also a new code PR (the red pair of RUNBOOK §2).
  const first = layout === 'code' && pr1 ? await prStatusOf(run, pr1, p) : null;
  const pr1Merged = Boolean(pr1) && (run.prBase === run.baseBranch || first?.state === 'merged');
  return { layout, single: label === 'the PR', workflow: run.workflow, number: run.number, baseBranch: run.baseBranch, mode, pending, draft: run.draft === true, issueReference: evidence.issueReference,
    stories, storyPaths, storyNote: missing.length ? `${missing.join(', ')} has no "As a …, I want …, so that …" line` : storyPaths.length ? 'the Story file could not be read' : 'no Story applies to this PR',
    fields, thisPr: holds.length ? `${others.length ? '' : 'no code change. '}It holds ${listed(holds)}.` : 'no code change.', diff,
    area: prArea({ area: fields.area, files, workflow: run.workflow }), title: fields.title,
    records: {
      promptTests: test ? { result: testResult, pass: /✗/.test(testResult) ? false : /✓/.test(testResult) ? true : null, report: test.reports?.[0] ?? null, current: test.source === 'current' } : null,
      lint: lint ? { result: lintCount ? `${lintCount[1]} of ${lintCount[2]} tests pass` : resultText(lint.summary), pass: lintCount ? Number(lintCount[2]) > 0 && lintCount[1] === lintCount[2] : null } : null,
      replay: replay ? { ...replay, ...(replay.formal?.result === 'failed' ? { counterexample: formalCounterexample(run) } : {}) } : null,
      ...(run.workflow === 'small-change' && label === 'the PR' ? { checklist: readSmallChangeChecklist(run) } : {}),
      formal, ...(formal?.result === 'failed' ? { counterexample: formalCounterexample(run) } : {}),
      proof: layout === 'code' ? { kind: proofKind, status: pending ? 'pending' : evidence.proofStatus, ...(native ? { passed: Number(native[1]), total: Number(native[2]) } : {}) } : null,
      review: layout === 'code' ? reviewVerdict(run, area) : null, formalStep: area.steps.includes('formal'), formalDone: Boolean(run.done.formal && !run.done.formal.skipped),
      rulesToCheck: storyRulesToCheck(run, files),
      ci: published?.ci ?? null, checker: published?.checker ?? null, drafts: layout === 'spec' ? drafts : [] },
    approval: mode !== 'manual'
      ? { kind: 'auto', mode, login: await githubLogin(run, p), date: Number.isFinite(automatic.startedAt) ? new Date(automatic.startedAt).toISOString().slice(0, 10) : '', person: approvals.some(item => item.route === 'terminal') }
      : { kind: 'words', items: approvals },
    pr1: pr1 ? { number: pr1.number, url: pr1.url, merged: pr1Merged, state: pr1Merged ? 'merged' : first?.state ?? 'unknown', ci: first?.ci ?? 'unknown' } : null,
    pr2: pr2 ? { number: pr2.number, url: pr2.url } : null,
    stacked, carriesPr1: stacked && published?.base === run.baseBranch && !pr1Merged,
    // "Not fixed yet:" makes the issue reference `Refs #N`: the PR helps find the cause and is never ready.
    notFixed: /^Refs #/.test(evidence.issueReference ?? ''), updatedAt: p.now() };
}
// The readable part, made safe like the rest of the body and kept to a bounded size.
function readableTopText(facts, run) {
  let top = readablePrTop(facts);
  if (characters(top.text) > 12_000) top = readablePrTop(facts, { fileLimit: 10 });
  if (facts.workflow === 'small-change' && facts.single && characters(top.text) > BODY_BUDGET - 4000)
    throw Object.assign(Error('The complete issue checklist exceeds the PR description budget. Keep every request; shorten evidence references before publishing.'), {code: 'workflow_pr_body_too_large'});
  return { text: hideLocalPaths(redactTry(top.text), run), notes: top.notes.map(note => hideLocalPaths(redactTry(note), run)) };
}

// The Details line of a stacked code PR (#3042): where it stands on PR 1, and PR 1's place in the merge order by the same
// rule as the readable part. Without facts (the publication identity) it names only the branch.
const STACKED = /^It (?:is|was) stacked on PR 1's branch /;
function stackedLine(run, facts) {
  if (!run.prBase || run.prBase === run.baseBranch) return null;
  const branch = `PR 1's branch \`${run.prBase}\``, order = facts ? pr1Order(facts) : null;
  if (facts?.pr1?.merged) return `It was stacked on ${branch}; PR 1 is merged.`;
  if (facts?.carriesPr1) return `It was stacked on ${branch} and now targets \`${run.baseBranch}\`. This PR also merges PR 1. Do not merge PR 1 alone.`;
  return `It is stacked on ${branch}${{ carried: '. PR 1\'s CI fails, so this PR also merges PR 1. Do not merge PR 1 alone.', first: ': merge PR 1 first.',
    ci: '. PR 1\'s CI has no result yet.', closed: '. PR 1 is closed without a merge.' }[order] ?? '.'}`;
}
// pdd's own result lines for the top of a PR; while source is being published they say so instead.
const ownLines = (run, evidence) => evidence.pddLines?.length ? (run.publicationPending ? ['pdd result: publication-pending (source is being published).'] : evidence.pddLines) : [];
// With `readable` (#3042), the description is the readable part and one closed Details section that holds this whole
// pdd body; without it (the publication identity), only the pdd body.
function prBody(run, area, env, drafts = [], tests = true, evidence, readable = null) {
  const steps = prSteps(run, area);
  const raw = Object.fromEntries(steps.map(step => [step, cleanSummary(run, step)]));
  const summaries = Object.fromEntries(steps.map(step => [step, oneLine(raw[step])]));
  // Agent text is inert everywhere in the body: the short Steps line is a code span too.
  const lines = steps.map(step => `- **${step}**: ${run.done[step].skipped ? 'skipped (recorded by pdd). ' : ''}Agent note — not checked by pdd: ${summaries[step] ? codeSpan(shortLine(summaries[step])) : 'done'}`);
  const full = Object.fromEntries(steps.map(step => [step, keepLines(raw[step])]));
  // Only a PR that covers a verify step carries verify.md (PR 1 never does).
  let verify = null;
  if (steps.includes('verify')) {
    // Agent Markdown in Details closes no issue (#3042): only pdd's own `Closes #N` can.
    try { verify = closingInert(redactTry(withoutForgedMachineLines(readFileSync(join(run.runDir, 'verify.md'), 'utf8').trim()))); } catch { verify = '_verify.md was not written in the run folder._'; }
  }
  const label = prLabel(run, area), ask = askArea(run), pr1 = ask && prOf(run, ask.name);
  // The readable part says what comes next; the PR 1 head keeps only its issue reference.
  const stacked = label === 'PR 2' ? stackedLine(run, readable?.facts) : null;
  const head = label === 'PR 1' ? [evidence.issueReference]
    : label === 'PR 2' ? [evidence.issueReference, '', `PR 2 of this run: the code. It builds on PR 1: ${pr1?.url}.`, ...(stacked ? [stacked] : [])]
    : [evidence.issueReference];
  // verify writes "✗ N vectors fail" as its first line when cases still fail; the person must see it first.
  const failing = verify?.split('\n').find(row => row.trim())?.trim().startsWith('✗') ? [`Agent note — not checked by pdd: ${verify.split('\n').find(row => row.trim()).trim()}`] : [];
  if (verify !== null) verify = `${AGENT_NOTE}:\n\n${verifyBody(noteRuntime(verify))}`;
  // The Prompt tests line and its report link go on top (#18).
  // The check step's result wins; else the latest step that reports a Prompt tests line. One line per Story (0.1.6), then the overall line.
  // Lines are read from the summary as stored, with its line breaks.
  const sources = [run.done.check?.summary, ...steps.toReversed().map(step => run.done[step]?.summary)].filter(Boolean);
  const verdict = sources.map(verdictLine).find(Boolean), change = sources.map(changeLine).find(Boolean);
  const shown = change?.match(/https?:\/\/[^\s;]+/g) ?? [];
  const runtime = publicationRuntime(run, env, label === 'PR 1' ? 'pr1' : 'current').filter(line => !line.replace(`${AGENT_NOTE}: `, '').startsWith('Report') || !shown.some(url => line.includes(` ${url} `)));
  const noted = runtime.some(line => hasReportLink(line, env)) || change && hasReportLink(change, env);
  const replayResult = area.replay_evidence === REPLAY_POLICY ? run.replayEvidence ?? readReplayEvidence(run) : null;
  const rules = run.workflow === 'small-change' && label === 'the PR' ? true : readable?.facts?.records?.rulesToCheck;
  const formal = readable?.facts?.records?.formal ?? (label !== 'PR 1' && area.steps.includes('formal') && !replayResult ? readFormalEvidence(run) : null);
  const replay = replayResult ? [formatReplayEvidence(replayResult,{maxCharacters:0,rules}), ''] : formal ? [formatFormalEvidence(formal, rules), ''] : [];
  const prefix = [...failing, ...replay, ...promptReturnLines(run)];
  // A registered before-the-fix result is pdd-checked historical evidence, never an agent note.
  const historical = beforeResults(run).flatMap(row => [beforeLine(row), ...reportLinks((run.evidence ?? []).filter(beforeStage).map(record => record.summary).join('\n'), env)
    .filter(link => link.startsWith(`Report (${row.story}):`))]);
  const top = [...ownLines(run, evidence), ...(verdict ? [`${AGENT_NOTE}: ${closingInert(verdict)}`] : []), ...new Set(historical), ...(change ? [`${AGENT_NOTE}: ${closingInert(change)}${hasReportLink(change, env) ? ' (report links expire after 7 days)' : ''}`] : []), ...runtime];
  if (evidence.lines.some(line => line.includes('pdd-workflow:'))) throw Error('Remove supplied workflow ownership markers from the report; pdd preserves its own marker.');
  const inventory = run.testInventory && label !== 'PR 1' ? [run.testInventory.text.trimEnd(), ...(run.testInventory.saved ? [] : ['warning: The full test inventory report was not saved.']), inventoryCommits(run.testInventory)] : [];
  const slot = evidence.lines.findIndex(line => line.startsWith(`${AGENT_NOTE}:`));
  const machineEnd = slot < 0 ? evidence.lines.length : slot;
  const native = evidence.nativeLine ? [run.publicationPending ? 'Native tests: publication-pending.' : evidence.nativeLine] : [];
  const preparedLines = [...evidence.lines.slice(0, machineEnd), ...native, ...inventory, ...evidence.lines.slice(machineEnd)].map(line => hideLocalPaths(redactTry(line), run));
  const body = (text, lifted, approvals = [], section = []) => hideLocalPaths([...lifted, ...prefix, ...top, ...(prefix.length || lifted.length || top.length ? [''] : []), ...head, ...(approvals.length ? ['', ...approvals] : []), ...(run.productMarker ? ['', run.productMarker] : []), ...(drafts.length ? ['', draftLine(drafts)] : []), '', `Made with \`pdd workflow run ${run.workflow}\`.`, '', '## Steps', ...lines,
    ...(section.length ? ['', ...section] : []),
    ...(!noted && hasReportLink([...lines, ...Object.values(full), ...preparedLines, verify ?? ''].join('\n'), env) ? ['', 'Interpreter report links expire after 7 days.'] : []),
    ...(text !== null ? ['', '## Verify', '', text] : []), ''].join('\n'), run);
  const approvalLines = (evidence.approvalLines ?? []).map(line => hideLocalPaths(redactTry(line), run));
  const notes = readable?.notes ?? [], budget = BODY_BUDGET - (readable ? characters(readablePrBody(readable.text, notes.join('\n'))) + 2 : 0);
  // Room for the full summaries with every summary left out comes first, so a cut is never silent. The top evidence,
  // approvals and verify.md then fit as before, and the full summaries get the room that is left.
  const least = fullSummaries(steps, full, 0);
  const { lifted, approvals } = publicationFit(preparedLines, approvalLines, Math.max(0, budget - 200 - (verify === null ? 0 : 1000) - characters(body(null, [], [], least))), env);
  if(replayResult){
    const room=Math.max(0,budget-200-(verify===null?0:1000)-characters(body(null,lifted,approvals,least)));
    prefix[failing.length]=formatReplayEvidence(replayResult,{maxCharacters:characters(replay[0])+room,rules});
  }
  // A stray </details> in verify.md never closes the Details section early (#3042).
  const verifyText = verify === null ? null : balancedDetails(verifyFit(hideLocalPaths(verify, run), budget - 200 - characters(body('', lifted, approvals, least)), env, false, true));
  const inner = withSummaries(steps, full, section => body(verifyText, lifted, approvals, section), budget - 200);
  return readable ? readablePrBody(readable.text, [inner.trimEnd(), ...(notes.length ? ['', ...notes] : [])].join('\n')) : inner;
}

// GitHub refuses a PR title over 256 characters; the GitHub intent checks its UTF-16 length. The issue title stays whole
// when the PR title fits. Else it is cut at a character boundary and shows " …" before its suffix, which always stays.
function prTitle(issueTitle, suffix) {
  if (`${issueTitle}${suffix}`.length <= 256) return `${issueTitle}${suffix}`;
  let kept = '';
  for (const point of issueTitle) { if (kept.length + point.length + 2 + suffix.length > 256) break; kept += point; }
  return `${kept.trimEnd()} …${suffix}`;
}

const commitSha = value => /^(?:[a-f\d]{40}|[a-f\d]{64})$/i.test(value);
// Updates use the same publication owner's identity checks as initial creation.
// Local source supplies an expected intent, never authority for the saved head.
async function readPublishedPr1(run, pr, p) {
  const intent = await prepareWorkflowPr({cwd:run.root,runId:run.runId,stageId:pr.stage,repository:run.repo,
    baseBranch:pr.base,title:prTitle(oneLine(run.issue.title) || `Issue #${run.number}`)},p.commandPorts);
  if (intent.headBranch !== pr.branch) throw Error('The owned PR 1 branch changed.');
  if (run.draft !== undefined && typeof run.draft !== 'boolean') throw Error('The saved draft publication policy must be a Boolean.');
  const outcome = await reconcileWorkflowPr({cwd:run.root,intent,draft:run.draft ?? false},p.commandPorts);
  p.inspectProgress?.();
  if (!['open','merged'].includes(outcome.state) || !outcome.pr || outcome.pr.number !== pr.number || outcome.pr.url !== pr.url)
    throw Error('The published PR 1 head is unavailable or does not match the owned publication.');
  return outcome.pr;
}
function inventoryCommits(inventory) {
  return commitSha(inventory.baseSha) && commitSha(inventory.headSha)
    ? `Test inventory commits: ${inventory.baseSha.slice(0,7)} → ${inventory.headSha.slice(0,7)}.`
    : 'Test inventory commits: unavailable.';
}

// Qualify draft policy before any write to an already published PR.
async function requireExistingDraft(run, pr, p) {
  if (run.draft !== true) return;
  // Existing-update paths have no saved prepared intent. Qualify the saved PR
  // itself before writes, retaining their ordinary source/marker checks below.
  const expected = `https://github.com/${run.repo}/pull/${pr.number}`;
  try {
    if (!Number.isSafeInteger(pr.number) || pr.number < 1 || typeof pr.url !== 'string'
      || pr.url.toLowerCase() !== expected.toLowerCase()) throw Error('Invalid saved PR identity');
    const reply = await p.execFile('gh', ['pr', 'view', pr.url, '--json', 'number,url,isDraft'], {cwd:run.root});
    if (reply.code !== undefined && reply.code !== 0) throw Error('PR unavailable');
    const actual = JSON.parse(reply.stdout);
    if (actual.number !== pr.number || actual.url !== pr.url || actual.isDraft !== true) throw Error('Draft PR unconfirmed');
  } catch {
    throw Error('The existing PR is not confirmed as the original draft. Inspect it; no PR update was started.');
  }
  p.inspectProgress?.();
}
async function commitPublicationFiles(run, p, lines, promptGuard = null) {
  const status = await rawGit(p, run.root, 'status', '--porcelain=v1', '-z', '--untracked-files=all');
  if (status) {
    const records = status.split('\0');
    const files = [];
    for (let i = 0; i < records.length && records[i]; i++) {
      const row = records[i];
      files.push(row.slice(3));
      if (/[RC]/.test(row.slice(0, 2))) i++;
    }
    await git(p, run.root, 'add', '-A');
    if (promptGuard) {
      const staged = await git(p,run.root,'write-tree');
      const unsafe = await promptGuard(staged);
      if (unsafe) return unsafe;
    }
    await git(p, run.root, 'commit', '-q', '-m', `${oneLine(run.issue.title)} (#${run.number})`);
    lines.push(`warning: pdd committed ${files.length} uncommitted file(s): ${files.slice(0, 10).join(', ')}${files.length > 10 ? ', …' : ''}.`);
  }
}
// Commit leftovers, then push to the area's PR or open it. Returns a failure result, or null when the PR is there.
async function publishAreaPr(run, area, p, lines, retry, automatic = null) {
  if (run.draft !== undefined && typeof run.draft !== 'boolean') return fail('The saved draft publication policy must be a Boolean.');
  const label = prLabel(run, area), existing = prOf(run, area.name), title = oneLine(run.issue.title) || `Issue #${run.number}`;
  if (existing) {
    try { await requireExistingDraft(run, existing, p); }
    catch (error) { if(error?.code==='workflow_progress_refused')throw error;return fail(error.message); }
  }
  const promptIndex = run.areas.findIndex(item=>item.then==='ask-code');
  const promptBase = label === 'PR 2' && promptIndex >= 0 && run.areas.findIndex(item=>item.name===area.name) > promptIndex
    ? run.prBase ?? existing?.base ?? prOf(run,askArea(run).name).branch : null;
  const promptGuard = async candidate => {
    if (!promptBase) return null;
    try {
      const edits = await specificationEdits(run,p,promptBase,candidate);
      if (edits.length) return fail(`Prompt edits belong in PR 1: ${edits.join(', ')}. Run pdd workflow open ${run.number} prompt-pr.`);
    } catch { return fail(`Cannot compare prompts with the PR base. Retain the local work and run pdd workflow open ${run.number} prompt-pr.`); }
    return null;
  };
  const unsafePrompts = await promptGuard();
  if (unsafePrompts) return unsafePrompts;
  const unsafeStaged = await commitPublicationFiles(run, p, lines, promptBase ? promptGuard : null);
  if (unsafeStaged) return unsafeStaged;
  const changedAdoption = await adoptionFailure(run,p);
  if(changedAdoption)return fail(changedAdoption);
  if (automatic) { const refused = await automatic.prepare(); if (refused) return refused; }
  const codePr = label !== 'PR 1';
  // Keep ownership separate from the immutable run start and the bounded display.
  // The current merge-base excludes main's integrations before this publication.
  let sourcePaths, sourceHead;
  if (!codePr) {
    sourceHead = await git(p,run.root,'rev-parse','--verify','HEAD^{commit}');
    const base = await git(p,run.root,'merge-base',sourceHead,`refs/remotes/origin/${run.baseBranch}`);
    sourcePaths = [...new Set([...(existing?.sourcePaths ?? []), ...(await rawGit(p,run.root,'diff','--name-only','-z',base,sourceHead)).split('\0').filter(Boolean)])].sort();
  }
  // Publication custody must survive an unavailable informational inventory.
  const candidateHead = codePr ? await git(p,run.root,'rev-parse','--verify','HEAD^{commit}') : null;
  const unsafeCandidate = await promptGuard(candidateHead);
  if (unsafeCandidate) return unsafeCandidate;
  if (codePr) {
    let baseSha = '', headSha = '', result;
    try {
      headSha = candidateHead;
      if (!commitSha(headSha)) {headSha='';throw Error('Invalid head commit');}
      const ref = `refs/remotes/origin/${run.baseBranch}`;
      await rawGit(p,run.root,'fetch','origin',`refs/heads/${run.baseBranch}:${ref}`);
      const fetched = (await rawGit(p,run.root,'rev-parse','--verify',`${ref}^{commit}`)).trim();
      if (!commitSha(fetched)) throw Error('Invalid fetched commit');
      baseSha = (await rawGit(p,run.root,'merge-base',headSha,fetched)).trim();
      if (!commitSha(baseSha)) {baseSha='';throw Error('Invalid merge base');}
      result = await collectTestInventory({cwd:run.root,baseSha,headSha},p.commandPorts);
    } catch {
      const text = 'Tests vs base: unavailable ("snapshot unavailable").\nChanged assertions in kept tests: unavailable.\nNew skips: unavailable.\nStatic inventory only; tests were not run.\n';
      result = {available:false,reason:'snapshot unavailable',text,details:text};
    }
    run.testInventory = {text:result.text,baseSha,headSha,saved:false};
    try {
      writeFileSync(join(run.runDir,'test-inventory.json'), JSON.stringify({...result,baseSha,headSha,saved:true},null,2)+'\n');
      run.testInventory.saved = true;
    } catch { lines.push('warning: The full test inventory report was not saved to test-inventory.json in the run folder.'); }
  }
  const opted = area.replay_evidence === REPLAY_POLICY;
  let prepared = await publicationEvidence(run, area, p);
  if (opted) {run.replayEvidence=await currentReplayEvidence(run,p,true);
    const last=area.steps.filter(step=>run.done[step]).at(-1),evidence=run.replayEvidence,applyPublication=publicationUpdate(run,['replayEvidence',...(codePr?['testInventory']:[])]);
    commitRun(run,p,latest=>{applyPublication(latest);if(last&&latest.done[last])latest.done[last].replayEvidence=evidence;});
  }

  // #3053: current shared-cause members travel with the umbrella's PR pair.
  if (run.automaticOrigin) {
    try {
      const { snapshot } = await (p.readDependencySnapshot ?? readDependencySnapshot)({ cwd: run.sourceRoot || run.root, repository: run.repo }, p);
      const references = sortClosingReferences({ snapshot, issue: `https://github.com/${run.repo.toLowerCase()}/issues/${run.number}`, code: label !== 'PR 1', graph: projectIssueGraph({ snapshot }) });
      prepared = { ...prepared, issueReference: [prepared.issueReference, ...references].join('\n') };
    } catch { /* Unproved members get no closing promise. */ }
  }
  const bodyBase = run.prBase ?? run.baseBranch;
  const bodyDrafts = label === 'PR 1' ? await draftPrompts(run, p, run.branch, bodyBase) : [];
  const bodyTests = label === 'PR 1' ? (await worktreeContents(run, p)).tests.length > 0 : true;
  // The readable part (#3042) for this PR, from the same evidence as its pdd body; `published` adds CI and the checker.
  const readableFor = async (evidence, { pending = false, replay = run.replayEvidence, published = null } = {}) => {
    const facts = await readableFacts(run, area, p, evidence, { drafts: bodyDrafts, pending, published, base: bodyBase, replay: opted ? replay ?? readReplayEvidence(run) : null });
    return { ...readableTopText(facts, run), facts };
  };
  const markedReplayBody = (replay, pending = false, readable = null) => {
    const evidence = pending ? { ...prepared, lines: ['Check evidence: publication-pending (source is being published).', ...prepared.lines.map(line => line.startsWith('Old-code proof:') ? 'Old-code proof: publication-pending (source is being published).' : line)] } : prepared;
    const body=prBody({...run,replayEvidence:replay,publicationPending:pending},area,p.env,bodyDrafts,bodyTests,evidence,readable);
    if(body.includes('pdd-workflow:')) throw Error('Remove supplied workflow ownership markers from the report; pdd preserves its own marker.');
    return body+`\n<!-- pdd-workflow:${run.runId}:${area.name} -->\n`;
  };
  const editReplay = async (body,afterPush=false,informational=false) => {
    try {
      const reply=await p.execFile('gh',['pr','edit',existing.url,'--body-file','-'],{cwd:run.root,input:body});
      if(reply.code !== undefined && reply.code !== 0) throw Object.assign(Error(reply.stderr||'gh pr edit failed'),{stderr:reply.stderr,code:reply.code});
    } catch(error) {if(informational)return fail(causeOf(error));return fail([...lines,`The code-space PR description could not be updated (${causeOf(error)}). ${afterPush ? 'Source was pushed; the PR stays publication-pending.' : 'No source was pushed.'} ${retry}.`].join('\n'));}
    return null;
  };
  // Only an unchanged source and identical non-inventory body can be an
  // informational refresh. Missing prior custody always takes the safety path.
  const bodyIdentity = () => createHash('sha256').update(prBody({...run,testInventory:null},area,p.env,bodyDrafts,bodyTests,prepared)).digest('hex');
  const rememberPublication = (pr, observed) => {
    if (codePr) { pr.publishedHeadSha = run.testInventory.headSha; pr.publicationBodySha256 = bodyIdentity(); }
    else if (commitSha(observed?.headSha)) { pr.publishedHeadSha = observed.headSha; pr.sourcePaths = sourcePaths; }
  };
  if (existing) {
    if (automatic) { const refused = await automatic.authorize(); if (refused) return refused; }
    let inventoryOnly = false;
    if (codePr && !opted && commitSha(existing.publishedHeadSha) && existing.publishedHeadSha === run.testInventory.headSha && existing.publicationBodySha256 === bodyIdentity()) {
      try {
        const remote = await rawGit(p,run.root,'ls-remote','origin',`refs/heads/${run.branch}`);
        inventoryOnly = remote.trim() === `${run.testInventory.headSha}\trefs/heads/${run.branch}`;
      } catch { /* Unavailable remote identity cannot weaken proof safety. */ }
    }
    if (!inventoryOnly) {
      let pending;
      try { const replay={...run.replayEvidence,outcome:'blocked',reason:'Publication pending; source-bound replay status will be refreshed after the push.'};pending=markedReplayBody(replay,true,await readableFor(prepared,{pending:true,replay})); }
      catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail([...lines, `${oneLine(error.message)} No source was pushed. ${retry}.`].join('\n')); }
      const failed=await editReplay(pending);if(failed)return failed;
    }
    const unsafe = await promptGuard(candidateHead);
    if (unsafe) return unsafe;
    if (codePr && await git(p,run.root,'rev-parse','--verify','HEAD^{commit}') !== candidateHead)
      return fail(`The local head changed during publication. Retain the work and run pdd workflow open ${run.number} prompt-pr to inspect prompt changes.`);
    p.say(`Pushing ${run.branch} to ${label}…`);
    const promptHead = codePr ? null : automatic?.head ?? await git(p,run.root,'rev-parse','--verify','HEAD^{commit}');
    if (!codePr && promptHead !== sourceHead) return fail('The publication head changed after ownership selection. No source was pushed; retry prompt publication.');
    if (automatic) { const refused = await automatic.validate(); if (refused) return refused; }
    try {
      const reply = await p.execFile('git', ['push', 'origin', `${codePr ? candidateHead : promptHead}:refs/heads/${run.branch}`], { cwd: run.root });
      if (reply.code !== undefined && reply.code !== 0) throw Object.assign(Error(reply.stderr || 'git push failed'), {stderr:reply.stderr, code:reply.code});
    }
    catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail([...lines, `git push to ${run.branch} failed (${causeOf(error)}). Check the network and gh auth, then ${retry}.`].join('\n')); }
    if (await git(p,run.root,'rev-parse','--verify','HEAD^{commit}') !== (codePr ? candidateHead : promptHead)) return fail('Source was pushed; the local head changed. The PR stays publication-pending; retry from the pushed source.');
    prepared = await publicationEvidence(run, area, p);
    let finalBody, finalFacts;
    try {
      // CI and the checker are read for the pushed head; a code PR also reads PR 1's state and CI (readableFacts).
      const published = await publishedChecks(run, existing, codePr ? run.testInventory.headSha : promptHead, p), readable = await readableFor(prepared,{published});
      finalFacts = readable.facts;
      finalBody=markedReplayBody(run.replayEvidence,false,readable);
    }
    catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail([...lines, `${oneLine(error.message)} Source was pushed; the PR stays publication-pending. ${retry}.`].join('\n')); }
    const failed=await editReplay(finalBody,true,inventoryOnly);
    if (failed) {
      if (!inventoryOnly) return failed;
      lines.push(`warning: The code PR still shows the previous inventory; its displayed commit pair identifies the older comparison. The new comparison is ${commitSha(run.testInventory.baseSha)&&commitSha(run.testInventory.headSha)?`${run.testInventory.baseSha.slice(0,7)} → ${run.testInventory.headSha.slice(0,7)}`:'unavailable'}. The current full report ${run.testInventory.saved ? 'was saved locally in test-inventory.json in the run folder' : 'was not saved locally'}. Inventory refresh failed (${failed.message}); ${retry}.`);
    } else {
      let observed;
      if (!codePr) {
        try { observed = await readPublishedPr1(run,existing,p); }
        catch (error) {
          if(error?.code==='workflow_progress_refused')throw error;
          return fail([...lines,`${oneLine(error.message)} Source was pushed; PR 1 publication remains unconfirmed. ${retry}.`].join('\n'));
        }
      }
      rememberPublication(existing,observed);
      if (finalFacts && commitSha(existing.publishedHeadSha)) existing.readable = savedReadable(finalFacts, existing.publishedHeadSha);
    }
    const applyPublication=publicationUpdate(run,codePr?['testInventory']:[]);
    const metadata=Object.fromEntries(['publishedHeadSha','publicationBodySha256','readable','sourcePaths'].filter(key=>Object.hasOwn(existing,key)).map(key=>[key,existing[key]]));
    commitRun(run,p,latest=>{applyPublication(latest);const pr=latest.pr.find(pr=>pr.url===existing.url&&pr.stage===existing.stage);if(pr)Object.assign(pr,metadata);});
    if (area.then === 'ask-code') await refreshReplayBaseline(run,p,false,sourcePaths);
    lines.push(`Pushed the new commits to ${label}.`);
    return null;
  }
  const base = bodyBase;
  // PR 1 says "tests" only when it has a test file (0.1.6 tester: a browser-only Story had none).
  const tests = bodyTests;
  let body, readable;
  try { readable = await readableFor(prepared); body = prBody(run, area, p.env, bodyDrafts, tests, prepared, readable); }
  catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail([...lines, `${oneLine(error.message)} No source was pushed. ${retry}.`].join('\n')); }
  let intent;
  p.say(`Pushing ${run.branch} and opening ${label} on GitHub…`);
  try {
    intent = await prepareWorkflowPr({ cwd: run.root, runId: run.runId, stageId: area.name, repository: run.repo, baseBranch: base,
      title: readablePrTitle({ layout: readable.facts.layout, workflow: run.workflow, area: readable.facts.area, statement: readable.facts.title || title, number: run.number, part: label === 'PR 1' ? 1 : label === 'PR 2' ? 2 : null }) }, p.commandPorts);
  } catch (error) {
    if(error?.code==='workflow_progress_refused')throw error;
    const why = error.code === 'workflow_github_topic_has_no_commits' ? `There are no new commits on ${run.branch}. Commit the change, then ${retry}.`
      : `pdd could not prepare ${label} (${causeOf(error)}). Fix it, then ${retry}.`;
    return fail([...lines, why].join('\n'));
  }
  if (!codePr && intent.headSha !== sourceHead) return fail('The publication head changed after ownership selection. No source was pushed; retry prompt publication.');
  if (automatic) {
    const changedSource = await automatic.validate(); if (changedSource) return changedSource;
    if (intent.headSha !== automatic.head) return fail('The publication head changed after validation. Run done check again.');
    const refused = await automatic.authorize(); if (refused) return refused;
    // The body must include the approval that was deferred until the prepared
    // intent was validated, including its native journal evidence.
    prepared = await publicationEvidence(run, area, p);
    readable = await readableFor(prepared);
    body = prBody(run, area, p.env, bodyDrafts, tests, prepared, readable);
    const changed = await automatic.validate(); if (changed) return changed;
  }
  const unsafe = await promptGuard(codePr ? intent.headSha : undefined);
  if (unsafe) return unsafe;
  if (codePr && intent.headSha !== candidateHead) return fail(`The local head changed during publication. Retain the work and run pdd workflow open ${run.number} prompt-pr to inspect prompt changes.`);
  const outcome = await publishWorkflowPr({ cwd: run.root, intent, body: `${body}\n<!-- ${intent.marker} -->\n`, draft: run.draft ?? false }, p.commandPorts);
  p.inspectProgress?.();
  // GitHub's refusal and a too-long body are certain: their message names the fix. Only a real doubt says "unconfirmed".
  if (!['open', 'merged'].includes(outcome.state) || !outcome.pr) return fail([...lines, `${label[0].toUpperCase()}${label.slice(1)} did not open: ${/ then try again\.$/.test(outcome.message)
    ? outcome.message.replace(/ then try again\.$/, ` then ${retry}.`) : `${outcome.message} ${retry[0].toUpperCase()}${retry.slice(1)} to retry.`}`].join('\n'));
  if (area.then === 'ask-code') await refreshReplayBaseline(run,p,false,sourcePaths);
  const published = { stage: area.name, number: outcome.pr.number, url: outcome.pr.url, branch: run.branch, base };
  rememberPublication(published,outcome.pr);
  if (commitSha(published.publishedHeadSha)) published.readable = savedReadable(readable.facts, published.publishedHeadSha);
  const applyPublication=publicationUpdate(run,codePr?['testInventory']:[]);
  commitRun(run,p,latest=>{applyPublication(latest);if(!latest.pr.some(pr=>pr.url===published.url&&pr.stage===published.stage))latest.pr.push(published);});
  // PR 1's Next line now links PR 2 (#3042). A failure there only warns.
  const ask = askArea(run), pr1 = codePr && ask && prOf(run, ask.name);
  if (pr1) {
    // One read: PR 1's state, and for a refresh of its readable top also its description, head and comments.
    const status = await prStatusOf(run, pr1, p, run.root, Boolean(pr1.readable?.facts));
    if (status.state === 'open') lines.push(...await linkPr2InPr1(run, pr1, published, p, status));
  }
  return null;
}
// Only the Next line of PR 1's readable part changes: its Details section (pdd's evidence, read on PR 1's own branch)
// stays byte for byte, because the worktree is on the code branch now. A PR 1 with saved readable facts gets its whole
// readable part again (refreshReadableTop), with the PR 2 link and its current CI and checker rows.
async function linkPr2InPr1(run, pr1, pr2, p, status) {
  if (pr1.readable?.facts) {
    const lines = await refreshReadableTop(run, pr1, p, { pr2, observed: new Map([[pr1.url, status]]) });
    if (lines.length) return lines.map(line => line.startsWith('warning:') ? `warning: pdd could not link PR 2 in the PR 1 description (${line.replace(/^warning: /, '')}). PR 2 is open; PR 1 keeps its previous Next line.` : 'pdd updated the PR 1 description: its Next line links PR 2.');
    // No refresh (GitHub gave no head, or nothing changed): only the Next line, as below.
  }
  try {
    await requireExistingDraft(run, pr1, p);
    const body = JSON.parse(String((await p.execFile('gh', ['pr', 'view', pr1.url, '--json', 'body'], { cwd: run.root })).stdout ?? '')).body;
    if (typeof body !== 'string') throw Error('PR 1 description unavailable.');
    const rows = body.split('\n'), open = rows.indexOf(DETAILS_OPEN), at = rows.findIndex(row => row.startsWith('**Next:** '));
    if (open < 0 || at < 0 || at > open) return [];
    const reference = /((?:Part of|Refs|Closes) #\d+)\.$/.exec(rows[at])?.[1] ?? `Part of #${run.number}`, automatic = automaticFacts(run, p);
    rows[at] = readableNextLines({ layout: 'spec', mode: !automatic || automatic.mode === 'off' ? 'manual' : automatic.mode, pr2: { number: pr2.number }, issueReference: reference })[0];
    const next = rows.join('\n');
    if (next === body) return [];
    const reply = await p.execFile('gh', ['pr', 'edit', pr1.url, '--body-file', '-'], { cwd: run.root, input: next });
    if (reply.code !== undefined && reply.code !== 0) throw Object.assign(Error('PR 1 description update failed.'), { code: reply.code });
    return ['pdd updated the PR 1 description: its Next line links PR 2.'];
  } catch (error) {
    if (error?.code === 'workflow_progress_refused') throw error;
    return [`warning: pdd could not link PR 2 in the PR 1 description (${error.code ?? 'error'}). PR 2 is open; PR 1 keeps its previous Next line.`];
  }
}

// The facts of a published readable part, saved on its PR record with the head they are for, so that a later refresh can
// render the same part again with fresh CI, checker and PR 1 facts (#3042). The copy keeps 40 files (and their count) and
// only the replay fields that the rows read.
function savedReadable(facts, head) {
  const copy = structuredClone(facts), replay = copy.records?.replay, files = copy.diff?.files ?? [];
  if (copy.diff) { copy.diff.count = Math.max(copy.diff.count ?? 0, files.length); copy.diff.files = files.slice(0, 40); }
  if (replay) copy.records.replay = { outcome: replay.outcome, reason: replay.reason, counts: replay.counts ?? {},
    ...(replay.mutation ? { mutation: { outcome: replay.mutation.outcome, failures: replay.mutation.failures } } : {}),
    ...(replay.formal ? { formal: Object.fromEntries(['status', 'result', 'scope', 'reason', 'control_outcome', 'control_exit_code', 'field', 'cause', 'reported', 'required'].filter(key => replay.formal[key] !== undefined).map(key => [key, replay.formal[key]])) } : {}),
    ...(replay.counterexample !== undefined ? { counterexample: replay.counterexample } : {}) };
  return { head, facts: { ...copy, pending: false } };
}
// The readable top of one open PR again (#3042): the saved facts of its last publication with the current CI, checker
// verdict for GitHub's head, PR 1's state and CI (code PR) and PR 2's link (PR 1). Only the part above the Details line
// changes, and in a stacked code PR the one Details line about PR 1's merge order; the rest stays byte for byte. A head
// that pdd did not publish waits for pdd's records. A description that is not pdd's own, or that already says the same
// (apart from its time), is left alone. The facts come from the status read (`observed`, with the description, head and
// comments), so a refresh with no change makes no other GitHub call. Before it writes, it reads the description, the head
// and the run record again: when a publication changed any of them in the meantime, it writes nothing (the next status
// tries again), so it never puts an older Details section back. Any problem only warns; it never changes the run.
async function refreshReadableTop(run, pr, p, { observed = new Map(), pr2 = null, cwd = run.root } = {}) {
  const area = run.areas.find(item => item.name === pr.stage), label = area ? prLabel(run, area) : 'the PR', name = `${label === 'the PR' ? 'the PR' : label} (#${pr.number})`;
  try {
    const marker = `<!-- pdd-workflow:${run.runId}:${pr.stage} -->`;
    const readView = async () => { const view = JSON.parse(String((await p.execFile('gh', ['pr', 'view', pr.url, '--json', 'body,headRefOid'], { cwd })).stdout ?? '')); return { body: view?.body, head: view?.headRefOid }; };
    const status = observed.get(pr.url) ?? await prStatusOf(run, pr, p, cwd, true);
    const seen = typeof status.view?.body === 'string' && commitSha(status.view?.head) ? status.view : await readView();
    const { body, head } = seen;
    if (typeof body !== 'string' || !commitSha(head) || !body.includes(marker) || (body.match(/pdd-workflow:/g) ?? []).length !== 1) return [];
    const rows = body.split('\n'), open = rows.indexOf(DETAILS_OPEN);
    if (open < 1) return [];
    const facts = structuredClone(pr.readable.facts);
    facts.records = { ...facts.records, ci: status.ci ?? 'unknown', checker: await checkerOf(pr, head, p, cwd, seen) };
    facts.headChanged = head.toLowerCase() !== String(pr.readable.head).toLowerCase();
    facts.updatedAt = p.now();
    const ask = askArea(run), first = ask && prOf(run, ask.name);
    if (facts.layout === 'code' && first && facts.pr1) {
      const state = observed.get(first.url) ?? await prStatusOf(run, first, p, cwd), merged = run.prBase === run.baseBranch || state.state === 'merged';
      facts.pr1 = { ...facts.pr1, merged, state: merged ? 'merged' : state.state ?? 'unknown', ci: state.ci ?? 'unknown' };
      facts.carriesPr1 = Boolean(facts.stacked) && status.base === run.baseBranch && !merged;
    }
    if (facts.layout === 'spec') {
      const code = pr2 ?? run.areas.filter(item => item.gate === 'pr' && item.name !== pr.stage).map(item => prOf(run, item.name)).find(Boolean);
      if (code) facts.pr2 = { number: code.number, url: code.url };
    }
    const top = readableTopText(facts, run).text, details = rows.slice(open);
    if (facts.layout === 'code' && first) {
      const anchor = details.indexOf(`PR 2 of this run: the code. It builds on PR 1: ${first.url}.`), line = stackedLine(run, facts);
      if (anchor >= 0 && line && STACKED.test(details[anchor + 1] ?? '')) details[anchor + 1] = line;
    }
    const next = `${top.trimEnd()}\n\n${details.join('\n')}`;
    if (sameReadableTop(next, body)) return [];
    await requireExistingDraft(run, pr, p);
    // #3042 review 2: a `done` in another process can publish between the first read and this write.
    const again = await readView(), latest = readRun(run.runDir)?.pr?.find(item => item.url === pr.url && item.stage === pr.stage);
    if (again.body !== body || String(again.head ?? '').toLowerCase() !== head.toLowerCase()
      || !['readable', 'publishedHeadSha', 'publicationBodySha256'].every(key => equalFact(latest?.[key], pr[key]))) return [];
    const reply = await p.execFile('gh', ['pr', 'edit', pr.url, '--body-file', '-'], { cwd, input: next });
    if (reply.code !== undefined && reply.code !== 0) throw Object.assign(Error('description update failed'), { code: reply.code });
    return [`pdd updated the top of ${name}: ${prStatus(facts)}.`];
  } catch (error) {
    if (error?.code === 'workflow_progress_refused') throw error;
    return [`warning: pdd could not update the top of ${name} (${error.code ?? 'error'}); it keeps its previous status line.`];
  }
}

// The code-or-stop question after PR 1, as the chat must show it.
async function askCodeLines(run, area, p) {
  const summaries = area.steps.filter(item => run.done[item]).map(item => `  ${item}: ${oneLine(run.done[item].summary) || 'done'}`);
  const drafts = await pr1Drafts(run, p), url = prOf(run, area.name).url;
  // The code is built only from approved prompts, so the code PR is not offered while PR 1 has a draft prompt.
  if (drafts.length) return [`PR 1: ${url}`, ...summaries, draftLine(drafts),
    `Gate: show the person PR 1 and the Prompt tests line. Do not offer the code PR yet. Tell the person exactly: "PR 1 is open: ${url}. ${approveFirst(run, drafts)}" Stop there.`, approvalGuide(run)];
  // Normal runs (#2962): the person chose code or stop at the Story card, so pdd asks no separate question.
  if (run.storyApproval && normalRun(run, p)) return [`PR 1: ${url}`, ...summaries,
    `Gate: show the person PR 1 and the Prompt tests line. Do not ask about the code PR: the person chose at the Story card. Tell the person exactly: "PR 1 is open: ${url}. ${codeLater(run)}" Stop there.`, `When the person later asks for the code PR, record their words: ${approvalGuide(run, p.pdd)}`];
  return [`PR 1: ${url}`, ...summaries,
    `Gate: show the person PR 1, the Prompt tests line and the Try link, then ask exactly: "Do you want the code PR now, or stop here and merge PR 1 first? ${codeLater(run)}" Stop there.`,
    approvalGuide(run, p.pdd),
    `If they stop, tell them exactly: "PR 1 is open: ${prOf(run, area.name).url}. ${codeLater(run)}" pdd never merges.`];
}

async function finishPr(run, area, step, p, lines, packageRoot = PACKAGE_ROOT) {
  // A coordinator that lost or let expire its claim does not push to the issue.
  const ownership = await continuationOwnership(run, run.root, p);
  if (ownership) return fail(ownership);
  const label = prLabel(run, area), existing = prOf(run, area.name);
  const selectedArea=run.area,selectedGate=run.gate;
  lines.push(`pdd recorded ${step}. pdd opens ${label} now.`);
  const failed = await publishAreaPr(run, area, p, lines, `run done ${step} again`);
  if (failed) return failed;
  // Capture readiness in the native waiting transition, never in a separate save.
  const candidate = prOf(run, area.name);
  const ready = step === area.steps.at(-1) && run.done[step] && !run.done[step].skipped && run.area === run.areas.length - 1 && (area.name === 'code' || run.workflow === 'small-change' || run.areas.slice(0,-1).some(item => item.then === 'ask-code')) && area.steps.every(name => run.done[name] && (!run.done[name].skipped || area.optional.includes(name))) && candidate?.number && commitSha(candidate.publishedHeadSha);
  const recordReadiness = latest => {
    const pr=prOf(latest,area.name);
    if (ready && latest.area===selectedArea && area.steps.every(name=>latest.done[name] && (!latest.done[name].skipped || area.optional.includes(name))) && pr?.number===candidate.number && pr.publishedHeadSha===candidate.publishedHeadSha && !(latest.metrics?.events ?? []).some(event=>event.type==='milestone' && event.data?.stage==='implementation-ready' && event.data.pr===pr.number && event.data.head===pr.publishedHeadSha) && !(latest.metricsObservations ?? []).some(event=>event.type==='milestone' && event.data?.stage==='implementation-ready' && event.data.pr===pr.number && event.data.head===pr.publishedHeadSha)) {
      latest.metricsObservations=[...(latest.metricsObservations ?? []),{type:'milestone',at:new Date(p.now()).toISOString(),data:{stage:'implementation-ready',pr:pr.number,head:pr.publishedHeadSha}}];
    }
  };
  if(area.replay_evidence===REPLAY_POLICY)lines.push(formatReplayEvidence(run.replayEvidence,{rules:await rulesToCheck(run,p)}));
  if (area.then === 'ask-code') {
    // New commits on an open PR 1 keep the question's time, so a yes the person already gave still counts
    // (a change request with pdd workflow changes moves it).
    const at=p.now();
    commitRun(run,p,latest=>{if(latest.area===selectedArea&&sameGate(latest.gate,selectedGate)){recordReadiness(latest);latest.state='waiting';latest.gate=existing && latest.gate?.kind==='ask-code'?latest.gate:{id:p.randomUUID(),area:area.name,at,kind:'ask-code'};}});
    const savedApproval = !!run.gate && (run.decisions ?? []).some(decision => decision.gateId === run.gate.id && decision.evidence);
    const shownGate = run.area===selectedArea && run.gate?.kind==='ask-code' ? (savedApproval ? snapshotLines(run.gate.promptSnapshot ?? []) : await showGate(run, p)) : [];
    if (run.storyApproval && normalRun(run, p) && run.through === 'code') return afterPr1(run, area, p, [...lines, ...shownGate], packageRoot);
    return done([...lines, ...shownGate, ...await askCodeLines(run, area, p)].join('\n'));
  }
  commitRun(run,p,latest=>{if(latest.area===selectedArea&&sameGate(latest.gate,selectedGate)){recordReadiness(latest);latest.state='waiting';latest.gate=null;}});
  return done([...lines, `${label === 'the PR' ? 'PR' : label}: ${prOf(run, area.name).url}`, `Tell the person ${label} is open. pdd never merges. Stop here.`].join('\n'));
}

// Normal-run gates (#2962). The prompt PR gate opens PR 1 by itself only after a verified full check pass under a valid
// Story approval; a changed Story or expected value reopens the Story gate for the person. null keeps the person gate.
const promptPathChanges = (approved, current) => !Array.isArray(approved) ? [] : [
  ...current.filter(path => !approved.includes(path)).map(path => `Prompt added: ${path}`),
  ...approved.filter(path => !current.includes(path)).map(path => `Prompt removed: ${path}`)];
async function changedStoryGate(run, area, step, p, lines, snapshot = run.gate?.promptSnapshot, approval = storyCoverage(run), extraChanges = []) {
  if (!approval?.fingerprint || !Array.isArray(snapshot)) return null;
  const paths = snapshot.map(row => row.path);
  const current = storyFingerprint({ root: run.root, changed: await changedFiles(run, p) });
  const changes = [...extraChanges, ...fingerprintChanges(approval.fingerprint, current), ...promptPathChanges(approval.prompts, paths)];
  if (changes.length) {
    const contract=await storyContract(run,p),paths=await storyContractPaths(run,p);
    const gateId = run.gate.id;
    commitRun(run, p, latest => { if (latest.gate?.id === gateId) {
      const parkedApproval = latest.parking?.phase === 'parked' && latest.parking.blocker?.kind === 'person'
        && sameGate(latest.parking.personWait?.gate, latest.gate) && !latest.parking.personWait?.question;
      if (!latest.gate.storyChanges?.length || fingerprintChanges(latest.gate.storySnapshot, current).length) latest.gate.id = p.randomUUID();
      latest.state = 'waiting'; latest.doneAt = null; latest.gate.kind = 'approve-pr';
      latest.gate.storyChanges = changes; latest.gate.storySnapshot = current; latest.gate.promptSnapshot = snapshot; latest.gate.storyContract=contract; latest.gate.storyPaths=paths;
      // Move only this gate's reservation, so the progress guard can save its new hold.
      if (parkedApproval) latest.parking.personWait = {gate: latest.gate, question: latest.question ?? null};
    } });
    return done([...lines, `pdd recorded ${step}. The Story, an expected value or the prompt list changed after the person approved the Story, so the Story gate is open again. pdd does not open ${prLabel(run, area)} until the person approves the change.`,
      await cardText(run, p, { changes, results: pddTestLines(run, p) }), cardGate, approvalGuide(run, p.pdd),
      'If they ask for changes or say no, revise or undo the change in this chat, run done again for the step you changed, and show the new card.'].join('\n'));
  }
  return null;
}
// A later code request is not approval of a changed Story or a replacement for current check evidence.
async function normalCodeReview(run, area, p) {
  if (!normalRun(run, p) || !run.storyApproval?.fingerprint) return null;
  const snapshot = await gatePromptSnapshot(run, p);
  const changed = await changedStoryGate(run, area, 'check', p, [], snapshot);
  if (changed) return changed;
  const pr1 = prOf(run, area.name);
  if (commitSha(pr1?.publishedHeadSha)) {
    const pending = await git(p, run.root, 'diff', '--name-only', '-z', pr1.publishedHeadSha);
    const untracked = await git(p, run.root, 'ls-files', '--others', '--exclude-standard', '-z');
    if (!pending && !untracked) return null;
  }
  const contents = await worktreeContents(run, p);
  const check = fullCheckPass({ root: run.root, since: run.promptReturn?.at ?? run.startedAt ?? 0, tests: contents.tests, stories: (run.storyApproval?.fingerprint.stories??[]).filter(story=>story.criteria.length).map(story=>story.path), prompts: snapshot.map(row => row.path) }, p);
  if (!check.pass) return fail(['The prompt check did not pass in full on the current files. No code approval was recorded or source synchronized.',
    ...check.problems.slice(0, 20).map(problem => `Not passed (${problem.kind}): ${problem.path}: ${problem.detail}`),
    'Repair and check again, then run pdd workflow done check.'].join('\n'));
  return null;
}
async function normalPromptGate(run, area, step, p, lines, contents, packageRoot) {
  if (!storyCoverage(run)?.fingerprint || !Array.isArray(run.gate?.promptSnapshot)) return null;
  const changed = await changedStoryGate(run, area, step, p, lines);
  if (changed) return changed;
  const paths = run.gate.promptSnapshot.map(row => row.path);
  const check = fullCheckPass({ root: run.root, since: run.promptReturn?.at ?? run.startedAt ?? 0, tests: contents.tests, stories: (storyCoverage(run)?.fingerprint.stories??[]).filter(story=>story.criteria.length).map(story=>story.path), prompts: paths }, p);
  if (check.pass) return automaticPr1(run, area, step, p, lines, check, packageRoot);
  // A typed summary cannot replace pdd's saved check results.
  if (!check.tests.length) lines.push('pdd has no saved check result of its own for this run. Run the check; do not ask the person to approve.');
  const shown = check.problems.slice(0, 20).map(problem => `Not passed (${problem.kind}): ${problem.path}: ${problem.detail}`);
  if (check.problems.length > 20) shown.push(`… ${check.problems.length - 20} more problems`);
  const verdictOnly = check.problems.length > 0 && check.problems.some(problem => problem.kind === 'no-verdict');
  return done([...lines, `pdd recorded ${step}. The prompt check did not pass in full on the current files, so pdd does not open ${prLabel(run, area)} yet.`, ...shown,
    verdictOnly ? 'No verdict: this is not a failed check. Follow RUNBOOK §11 for no verdict: tell the person the cause and pdd\'s next step. Do not ask them to approve, and never send the same check again on your own.'
      : `Do not ask the person to approve. Repair and check again, then run: ${p.pdd} workflow done check --summary "one line". After 2 fix rounds for the same ✗, stop with the evidence. When the fix needs a Story or expected-value change, propose it and run done again: pdd then shows the Story card with the change, for the person.`,
    ].join('\n'));
}
// The coordinator supplies custody, never approval words or a model verdict.
function automaticPr1Scope(run, p, packageRoot) {
  try {
    if (readApprovalPolicy({root: run.sourceRoot}, p).strictApprovals) return 'strict approval policy requires a person terminal';
    if (JSON.parse(readFileSync(join(run.sourceRoot, 'pdd.json'), 'utf8'))?.autopilot?.mode !== 'auto'
      || !automaticHandoff(run, p, packageRoot)) return 'current automatic operator scope is unavailable';
  } catch { return 'current automatic approval policy or operator scope is unavailable'; }
  return null;
}
function automaticPr1ParkingEligible(run, p) {
  const park = run.parking;
  return !park || park.phase === 'parked' && park.blocker?.kind === 'person'
    && sameGate(park.personWait?.gate, run.gate) && !park.personWait?.question
    && !run.blockedOn && !run.runtimeWait && !park.checkHeld
    && blockerFor({...run, parking: null})?.kind === 'person' && !continuationCheckHeld(run, p);
}
function automaticPr1Eligible(run, {cwd, coordinatorId, machine}, p, published = null) {
  const area = run.areas[run.area];
  return validSavedAutomaticOrigin(run) && run.automaticOrigin.coordinatorId === coordinatorId
    && run.automaticOrigin.machine === machine && samePath(run.sourceRoot, cwd)
    && ['pdd-bug', 'pdd-feature'].includes(run.skill) && run.state === 'waiting'
    && automaticPr1ParkingEligible(run, p) && !openQuestion(run) && !run.repairLimit && !run.integrationLimit
    && (!run.chatReplacement || ['launched', 'rolledBack', 'ended'].includes(run.chatReplacement.phase))
    && run.gate?.kind === 'approve-pr' && run.gate.area === area?.name
    && area.gate === 'pr' && area.before === 'approve'
    && (!prOf(run, area.name) || published && sameFact(prOf(run, area.name), published))
    && area.steps.every(step => run.done[step]);
}
const recordedStoryDecision = run => [...run.decisions].reverse().find(decision =>
  decision.stage === run.areas[storyGateIndex(run)]?.name && decision.decision === 'approve');

async function deriveStoryCoverage(run, decision, p) {
  const evidence = decision?.evidence;
  if (!evidence?.id || !Array.isArray(evidence.prompts) || !readPromptApprovals({commonDir: run.commonDir}, p).some(row => sameFact(row, evidence)))
    throw Error('recorded Story approval evidence is unavailable');
  if (typeof decision.storyContract !== 'string' || !Array.isArray(decision.storyPaths))
    throw Error('approval-bound Story contract is unavailable');
  const paths = await storyContractPaths(run, p), changed = await changedFiles(run, p, true);
  const inventory = [...new Set([...paths, ...changed.filter(path => path.endsWith('.json') || path.endsWith('.md') && path.split('/').includes('user_stories'))])].sort();
  const folder = mkdtempSync(join(tmpdir(), 'pdd-story-coverage-'));
  let recovered, changes = [];
  try {
    const texts = [];
    // Freeze each file once. Contract and fingerprint then read the same bytes,
    // without another asynchronous inventory or a read from the live worktree.
    for (const path of inventory) {
      const file = resolve(run.root, path);
      if (!file.startsWith(resolve(run.root) + '/') || path.includes('\\') || path.split('/').includes('.git'))
        throw Error('unsafe Story contract path');
      let bytes;
      try {
        if (!lstatSync(file).isFile()) throw Error('Story contract files must be regular files');
        bytes = readFileSync(file);
      } catch (error) { if (error.code === 'ENOENT') continue; throw error; }
      texts.push([path, bytes.toString('utf8')]);
      mkdirSync(dirname(join(folder, path)), {recursive: true});
      writeFileSync(join(folder, path), bytes);
    }
    if (storyContractHash(run, texts) !== decision.storyContract)
      changes = ['Story contract changed since its recorded approval'];
    const fingerprint = storyFingerprint({root: folder, changed});
    if (!changes.length && [...fingerprint.stories, ...fingerprint.tests].some(row => !decision.storyPaths.includes(row.path)))
      changes = ['Story fingerprint contains files outside the approved contract'];
    recovered = {fingerprint, derivedFrom: {storyContract: decision.storyContract}};
  } finally { rmSync(folder, {recursive: true, force: true}); }
  if (!changes.length && !recovered.fingerprint.stories.some(row => row.sha256 && row.criteria.length))
    throw Error('recorded approval has no Story coverage');
  return {coverage: {gateId: decision.gateId, evidenceId: evidence.id, at: decision.at,
    fingerprint: recovered.fingerprint, prompts: evidence.prompts.map(row => row.path),
    source: 'derived from the recorded approval', derivedFrom: recovered.derivedFrom}, changes};
}
export const advanceAutomaticPr1 = saveGuard((args, ports = {}) => lockedMutation(args, ports, async ({ref, cwd, packageRoot = PACKAGE_ROOT, coordinatorId, machine}, ports) => {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const found = await resolveRun(ref, {cwd}, p);
  if (found.error) return fail(found.error);
  const run = found.run, area = run.areas[run.area];
  const owner = {cwd, coordinatorId, machine};
  if (!automaticPr1Eligible(run, owner, p)) return done('Automatic PR 1 gate skipped.');
  const selected = structuredClone({origin: run.automaticOrigin, coverage: storyCoverage(run), storyDecision: recordedStoryDecision(run), area, index: run.area, branch: run.branch});
  let publicationGate;
  const progressRecorded = protectProgress(run, p, {validate: latest => {
    // Only this invocation's durably saved PR may appear during its final transition.
    if (!automaticPr1Eligible(latest, owner, p, prOf(run, area.name)) || !sameFact(latest.automaticOrigin, selected.origin)
      || !sameFact(storyCoverage(latest), selected.coverage) || !sameFact(latest.areas[latest.area], selected.area)
      || !sameFact(recordedStoryDecision(latest), selected.storyDecision)
      || latest.area !== selected.index || latest.branch !== selected.branch
      || publicationGate && (!sameGate(latest.gate, publicationGate) || latest.gate.storyChanges?.length))
      throw Object.assign(Error('Automatic PR 1 eligibility changed. Preserve the current blocker and inspect the run.'), {code: 'workflow_progress_refused'});
  }});
  p.inspectProgress();
  const hold = reason => {
    const gateId = run.gate.id;
    commitRun(run, p, latest => { if (latest.gate?.id === gateId) latest.gate.automaticHold = reason; });
    return done(`PR 1 waits: ${reason}.`);
  };
  const scope = automaticPr1Scope(run, p, packageRoot);
  if (scope) return hold(scope);
  if (run.gate.storyChanges?.length) return hold('Story changes require a person approval');
  const ownership = await continuationOwnership(run, run.root, p);
  if (ownership) return hold(ownership);
  let snapshot = await gatePromptSnapshot(run, p);
  if (!storyCoverage(run)?.fingerprint) {
    let recovered;
    try { recovered = await deriveStoryCoverage(run, selected.storyDecision, p); }
    catch (error) { return hold(`saved Story approval coverage is missing: ${oneLine(error.message)}`); }
    snapshot = await gatePromptSnapshot(run, p);
    const changed = await changedStoryGate(run, area, 'check', p, [], snapshot, recovered.coverage, recovered.changes);
    if (changed) return hold('Story changes require a person approval');
    const scope = automaticPr1Scope(run, p, packageRoot), ownership = await continuationOwnership(run, run.root, p);
    if (scope || ownership) return hold(scope || ownership);
    snapshot = await gatePromptSnapshot(run, p);
    const changedAgain = await changedStoryGate(run, area, 'check', p, [], snapshot, recovered.coverage, recovered.changes);
    if (changedAgain) return hold('Story changes require a person approval');
    commitRun(run, p, latest => {
      if (automaticPr1Scope(latest, p, packageRoot)
        || !readPromptApprovals({commonDir: latest.commonDir}, p).some(row => sameFact(row, selected.storyDecision.evidence)))
        throw Object.assign(Error('Recorded Story coverage authority changed. Keep the current gate.'), {code: 'workflow_progress_refused'});
      latest.storyApproval = recovered.coverage;
    });
    selected.coverage = structuredClone(recovered.coverage);
  }
  const changed = await changedStoryGate(run, area, 'check', p, [], snapshot);
  if (changed) return hold('Story changes require a person approval');
  const contents = await worktreeContents(run, p);
  const check = fullCheckPass({root: run.root, since: run.promptReturn?.at ?? run.startedAt ?? 0,
    tests: contents.tests, stories: (storyCoverage(run).fingerprint.stories ?? []).filter(story => story.criteria.length).map(story => story.path),
    prompts: snapshot.map(row => row.path)}, p);
  if (!check.pass) return hold(`prompt check is not a full pass: ${check.problems.slice(0, 20).map(problem => `${problem.kind}: ${problem.path}: ${problem.detail}`).join('; ')}`);
  publicationGate = structuredClone(run.gate);
  p.inspectProgress();
  return automaticPr1(run, area, 'check', p, [], check, packageRoot, progressRecorded);
}, 'automatic-pr1.lock'));
async function automaticPr1(run, area, step, p, lines, check, packageRoot, progressRecorded = () => {}) {
  const ownership = await continuationOwnership(run, run.root, p);
  if (ownership) return fail(ownership);
  let snapshot, edits = [], approvalRecorded = false;
  const restoreApprovalEdits = () => {
    for (const edit of edits) {
      try { if (readFileSync(join(run.root, edit.path), 'utf8') === edit.next) (p.fs ?? { writeFileSync }).writeFileSync(join(run.root, edit.path), edit.text); } catch { /* Preserve a peer's replacement. */ }
    }
  };
  const refused = () => fail([...lines, 'The publication source changed or its check is incomplete. No automatic approval or source publication was made. Run done check again.'].join('\n'));
  // Readiness belongs to the prepared commit. Approval metadata is the only
  // permitted difference between that checked tree and the tree we publish.
  const automatic = {
    head: null,
    async prepare() {
      const scope = Object.hasOwn(run, 'automaticOrigin') && automaticPr1Scope(run, p, packageRoot);
      if (scope) return fail(scope);
      const checkedHead = await git(p, run.root, 'rev-parse', '--verify', 'HEAD^{commit}');
      snapshot = await gatePromptSnapshot(run, p);
      const changed = await changedStoryGate(run, area, step, p, lines, snapshot);
      if (changed) return changed;
      const contents = await worktreeContents(run, p);
      check = fullCheckPass({ root: run.root, since: run.promptReturn?.at ?? run.startedAt ?? 0, tests: contents.tests,
        stories: (storyCoverage(run).fingerprint.stories ?? []).filter(story => story.criteria.length).map(story => story.path),
        prompts: snapshot.map(row => row.path) }, p);
      if (!check.pass) return refused();
      try { edits = await approveGatePrompts(run, p, snapshot); }
      catch (error) { return fail(`Cannot approve the selected prompts: ${error.message}`); }
      const fs = p.fs ?? { writeFileSync };
      try {
        for (const edit of edits) {
          if (readFileSync(join(run.root, edit.path), 'utf8') !== edit.text) return refused();
          fs.writeFileSync(join(run.root, edit.path), edit.next);
        }
        await commitPublicationFiles(run, p, lines);
        const head = await git(p, run.root, 'rev-parse', '--verify', 'HEAD^{commit}');
        const paths = (await rawGit(p, run.root, 'diff', '--name-only', '-z', checkedHead, head)).split('\0').filter(Boolean);
        for (const path of paths) {
          const edit = edits.find(edit => edit.path === path);
          if (!edit || await rawGit(p, run.root, 'show', `${head}:${path}`) !== edit.next) {
            return await changedStoryGate(run, area, step, p, lines, await gatePromptSnapshot(run, p)) ?? refused();
          }
        }
        if (await rawGit(p, run.root, 'diff', '--summary', checkedHead, head)) return refused();
        automatic.head = head;
        const invalid = await automatic.validate();
        if (invalid) automatic.head = null;
        return invalid;
      } finally {
        // No journal or gate approval has been recorded on a failed prepare.
        if (!automatic.head) restoreApprovalEdits();
      }
    },
    async validate() {
      p.inspectProgress?.();
      if (Object.hasOwn(run, 'automaticOrigin')) {
        const refusal = automaticPr1Scope(run, p, packageRoot) || await continuationOwnership(run, run.root, p);
        if (refusal) return fail(refusal);
      }
      const head = await git(p, run.root, 'rev-parse', '--verify', 'HEAD^{commit}');
      const dirty = await rawGit(p, run.root, 'status', '--porcelain=v1', '-z', '--untracked-files=all');
      if (head !== automatic.head || dirty || await git(p, run.root, 'rev-parse', '--verify', 'HEAD^{commit}') !== automatic.head) {
        const changed = await changedStoryGate(run, area, step, p, lines, await gatePromptSnapshot(run, p));
        return changed ?? refused();
      }
      return null;
    },
    async authorize() {
      const invalid = await automatic.validate(); if (invalid) return invalid;
      if (Object.hasOwn(run, 'automaticOrigin')) {
        const refusal = automaticPr1Scope(run, p, packageRoot) || await continuationOwnership(run, run.root, p);
        if (refusal) return fail(refusal);
      }
      const record = { via: 'automatic-check-pass', basis: { storyEvidenceId: storyCoverage(run).evidenceId ?? null,
        batches: [...new Set(check.tests.map(item => item.batch))], headSha: automatic.head,
        ...(Object.hasOwn(run, 'automaticOrigin') ? {origin: 'automatic', automaticOrigin: run.automaticOrigin} : {}) } };
      const authority = Object.hasOwn(run, 'automaticOrigin') ? {
        async afterLock() {
          const refusal = await continuationOwnership(run, run.root, p);
          if (refusal) throw Error(refusal);
        },
        beforeCommit() {
          const refusal = automaticPr1Scope(run, p, packageRoot);
          if (refusal) throw Error(refusal);
        }
      } : null;
      try { await saveGateApproval(run, area, record, [], p, snapshot, false, authority); approvalRecorded = true; }
      catch (error) { return fail(`Approval failed: ${error.message}`); }
      return null;
    }
  };
  const selectedArea = run.area, selectedGate = structuredClone(run.gate), selectedQuestion = run.question, published = [];
  let failed;
  try { failed = await publishAreaPr(run, area, p, published, `run done ${step} again`, automatic); }
  finally { if (!approvalRecorded) restoreApprovalEdits(); }
  if (failed) return failed;
  const askCode = area.then === 'ask-code', at = p.now();
  commitRun(run, p, latest => {
    if (latest.area === selectedArea && sameGate(latest.gate, selectedGate)) {
      const parkedApproval = latest.parking?.blocker?.kind === 'person' && sameGate(latest.parking.personWait?.gate, selectedGate);
      latest.state = 'waiting'; latest.gate = askCode ? { id: p.randomUUID(), area: area.name, at, kind: 'ask-code' } : null;
      if (parkedApproval) latest.parking.personWait = {gate: latest.gate, question: latest.question ?? null};
    }
    if (equalFact(latest.question, selectedQuestion)) latest.question = null;
  });
  progressRecorded();
  const label = prLabel(run, area), url = prOf(run, area.name).url;
  const head = [...lines, ...edits.map(edit => `Approved ${edit.path} ${edit.proseSha256} (full check pass under the Story approval)`),
    `pdd recorded ${step}. The prompt check passed in full on the current prompts (${check.tests.length} test${check.tests.length === 1 ? '' : 's'}), so pdd opened ${label === 'the PR' ? 'the PR' : label} with no approval question (route automatic-check-pass).`, ...published];
  if (!askCode) return done([...head, `PR: ${url}`, 'pdd never merges.'].join('\n'));
  const shownGate = run.gate ? await showGate(run, p) : [];
  if (Object.hasOwn(run, 'automaticOrigin') && !automaticPromptReturn(run, p)) return done([...head, ...shownGate, `PR 1: ${url}`, automaticHandoff(run, p, packageRoot), 'PR 1 is open. Continue through the scoped automatic code gate.'].filter(Boolean).join('\n'));
  return afterPr1(run, area, p, [...head, ...shownGate], packageRoot);
}
// After PR 1 opens in a normal run: follow the code-or-stop choice saved with the Story approval; ask nothing.
async function afterPr1(run, area, p, head, packageRoot) {
  const url = prOf(run, area.name).url;
  if (run.through !== 'code' && !automaticPromptReturn(run,p)) return done([...head, `PR 1: ${url}`, `Stopped after PR 1, as the Story card said. Do not ask about the code PR. ${codeLater(run)}`].join('\n'));
  const started = await startCodeFromCard(run, area, p, packageRoot);
  return done([...head, `PR 1: ${url}`, started].join('\n'));
}
async function startCodeFromCard(run, area, p, packageRoot) {
  p.codeEntryContract=approvedStoryContract(run) ?? await storyContract(run,p);
  const review = await normalCodeReview(run, area, p);
  if (review) return review.message;
  const refuse = why => `pdd did not start the code PR: ${oneLine(why)} The run waits at the code gate. ${codeLater(run)}`;
  const pr1 = prOf(run, area.name);
  let state;
  try { state = await (p.readPrStatus ?? readWorkflowPrStatus)({ cwd: run.root, url: pr1.url }, p.commandPorts); }
  catch { return refuse('PR 1 state is unavailable.'); }
  if (!['open', 'merged'].includes(state.state)) return refuse(`PR 1 is ${state.state}.`);
  if (replayEnabled(run)) {
    try { const dirty = await unpublishedScenarios(run, p); if (dirty.length) return refuse(`Unpublished scenario edits remain: ${dirty.join(', ')}. Publish them in prompt space first.`); }
    catch { return refuse('Cannot verify published scenario bytes. Repair the scenario inventory.'); }
  }
  const drafts = await pr1Drafts(run, p);
  if (drafts.length) return refuse(approveFirst(run, drafts));
  const adopted = await adoptionFailure(run, p);
  if (adopted) return refuse(adopted);
  p.say('Making the code branch…');
  let based;
  try { based = await codeBranch(run, area, p, async () => {
    const changed=await codeEntryFailure(run,p);if(changed)throw Error(changed);
    await saveGateApproval(run,area,{via:automaticPromptReturn(run,p)?'prompt-reentry':'card-choice',basis:{storyEvidenceId:run.storyApproval?.evidenceId??null,...(automaticPromptReturn(run,p)?{priorCodeApprovalId:run.promptReturn.codeApprovalId}:{})}},[],p,run.gate?.promptSnapshot??[]);
  }); }
  catch (error) { if (error?.code === 'workflow_progress_refused') throw error; return refuse(error.message); }
  const branch = run.branch, prBase = run.prBase, selectedArea = run.area, selectedGate = structuredClone(run.gate), selectedQuestion = run.question;
  commitRun(run, p, latest => {
    latest.branch = branch; latest.prBase = prBase;
    if (equalFact(latest.question, selectedQuestion)) latest.question = null;
    if (latest.area === selectedArea) { latest.metricsOrigin = { ...(latest.metricsOrigin ?? { origin: 'unknown' }), requiredOutcome: 'code' }; if (sameGate(latest.gate, selectedGate)) latest.gate = null; latest.area = selectedArea + 1; latest.state = latest.question ? 'waiting' : 'running'; latest.doneAt = null; }
  });
  const next = run.areas[run.area];
  let chat;
  try { chat = await startNextChat(run, p, packageRoot); }
  catch (error) { if (error?.code === 'workflow_progress_refused') throw error; return `The person chose the code PR at the Story card.${based} The ${next.name} chat startup was not confirmed (${error.code ?? 'error'}). Start it: pdd workflow open ${run.number}`; }
  return [`The person chose the code PR at the Story card (route card-choice).${based}`,
    `Started area ${run.area + 1} of ${run.areas.length}: ${next.name} (${next.steps.join(', ')}) in a new chat: Herdr session pdd, tab "${chat.label}".`,
    `Watch it: pdd workflow open ${run.number}`, 'This chat\'s work is done. Stop here.'].join('\n');
}

// Record saved Runtime evidence without progressing the workflow or contacting external services.
async function recordEvidenceCommand({ ref, summaryFile, cwd }, ports) {
  const p = deps(ports), found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  let receipt, source, lines, association;
  try {
    if (!summaryFile || !lstatSync(resolve(cwd, summaryFile)).isFile() || lstatSync(resolve(cwd, summaryFile)).size > 2 * 1024 * 1024) throw Error('Supply a regular saved JSON file of at most 2 MiB.');
    receipt = JSON.parse(readFileSync(resolve(cwd, summaryFile), 'utf8'));
    if (receipt.schema === 'pdd.native-evidence-import.v1') {
      const prepared = prepareNativeEvidence({root:run.root,runDir:run.runDir,runId:run.runId,summaryFile:resolve(cwd,summaryFile)},
        {workspace:input=>readEvidenceEligibility(input,p)});
      const folder = join('evidence',p.randomUUID());
      mkdirSync(join(run.runDir,folder),{recursive:true,mode:0o700});
      const native = {...prepared.record,originals:prepared.record.originals.map((row,index)=> {
        const savedPath = join(folder,String(index));
        writeFileSync(join(run.runDir,savedPath),prepared.originals[index].bytes,{flag:'wx',mode:0o600});
        return {...row,savedPath};
      })};
      const at = p.now();
      writeFileSync(join(run.runDir,folder,'admission.json'),JSON.stringify(native,null,2)+'\n',{flag:'wx',mode:0o600});
      commitRun(run,p,latest=>{(latest.evidence??=[]).push({at,native});});
      return done(`Recorded native original evidence for ${run.repo}#${run.number}: profile ${prepared.assessment.profileState}; Story native proof ${prepared.assessment.storyNativeProof}. Originals and limits retained. Steps, gates and PRs are unchanged. This records evidence, not fresh execution or approval.`);
    }
    if (!/^[a-f0-9]{64}$/.test(receipt.source_sha256 ?? '') || !Array.isArray(receipt.rows) || !receipt.rows.length) throw Error('Saved check JSON needs source_sha256 and nonempty rows.');
    const tests = receipt.rows.map(row => row?.test);
    evidenceTests(tests);
    source = { kind: 'runtime-capture-v1', sha256: receipt.source_sha256, tests };
    const producer=realpathSync(receipt.repo);
    association=(run.evidenceAssociations??[]).find(a=>a.workspaceRoot===producer && selectionEqual(a.tests,tests) && a.source_sha256===source.sha256);
    // Re-import cannot change the stage of the same original result.
    const previous=[...(run.evidence??[])].reverse().find(e=>e.association && sameFact(e.receipt,receipt));
    if(previous && (!association || previous.association.stage!==association.stage || !sameFact(previous.association.sourceAnchor,association.sourceAnchor)))
      throw Error('The original evidence stage is no longer registered; it cannot be relabelled.');
    let root=run.root;
    if(association)root=checkedAssociation(run,association);
    else {
      if(producer!==realpathSync(run.root))throw Error('The evidence belongs to a different repository/worktree without a registered association.');
      if(!matchesSource({source},run.root,null))throw Error('The saved source does not match the current selected files. Read a compatible receipt or run a fresh selected check.');
    }
    const found = findTests({ root });
    const rows = receipt.rows.map(row => {
      const test = found.tests.find(test => test.path === row.test);
      if (!test || test.story !== row.story || !['passed', 'failed', 'refused', 'not_run', 'unknown', 'queued', 'running'].includes(row.state))
        throw Error('Evidence row Story/state does not match its selected test.');
      return { ...row, phase: 'server', criteria_total: test.doc?.criteria?.length ?? 0 };
    });
    const expected = new Map(storyLines(rows));
    lines = rows.map(row => row.summary_line);
    // A saved result of an older pdd says `Runtime check`: read its label as `Prompt tests` before the compare.
    const label = line => typeof line === 'string' ? line.replace(LABEL_START, PROMPT_TESTS_LABEL) : line;
    if (rows.some(row => label(row.summary_line) !== expected.get(row.story))) throw Error('Evidence summary_line does not match its structured Story results.');
  } catch (error) { return fail(`Evidence not recorded: ${oneLine(error.message)}`); }
  const reports=receipt.rows.flatMap(row=>typeof row.report_url==='string' && /^https?:\/\/[^\s<>\x22\x27`]+$/.test(row.report_url)?[`Report (${row.story}): ${row.report_url}`]:[]);
  const evidence={at:p.now(),summary:[...new Set([...lines,...reports])].join('\n'),source,receipt,...(association?{association:structuredClone(association)}:{})};
  commitRun(run,p,latest=>{
    if(!eligibleEvidence(latest,evidence,{stage:association?.stage,fingerprint:null}))throw Error('The selected evidence source or association changed before saving.');
    (latest.evidence??=[]).push(evidence);
  });
  return done(`Recorded source-verified saved evidence for ${run.repo}#${run.number}. Steps, gates and PRs are unchanged. This records evidence, not fresh execution or approval.`);
}

// pdd's own results for a run (pdd test, pdd lint, pdd workflow prove). A read problem gives no results, never a stop.
const readOwnResults = (run, p) => (p.readRunResults ?? readRunResults)({ root: run.root, runDir: run.runDir, runId: run.runId, since: run.promptReturn?.at ?? run.startedAt ?? 0, baseBranch: run.baseBranch ?? null }, { env: p.env, workspace:input=>readEvidenceEligibility(input,p) });
function ownResults(run, p) {
  try { return readOwnResults(run, p); }
  catch { return []; }
}
// The steps whose done output shows pdd's own results, or a visible "no pdd result" warning.
const PROOF_STEPS = ['check', 'try', 'verify'];
// Repair ceiling (#3041): in an Autopilot run, a repair round is a real return to an earlier
// step after a failure: a `done` for a step that clears later recorded steps of its area
// (build again after verify, formal or review). A retry of a step with nothing recorded after
// it (a publication, claim or push retry) is not a round. A later step of the area (a check
// such as verify) recorded again on unchanged or unknown worktree content is not a round either. After
// 5 rounds in one area, pdd refuses another, records the stop as `stuck`, and refuses every
// later `done` of that run. Manual runs keep their skill's own repair rule and save no count.
const REPAIR_ROUNDS = 5, REPAIR_REFUSED = Symbol('repair refused');
const INTEGRATION_ROUNDS = 2;
const integrationLimitReason = name => `Base integration limit reached in ${name}: take the stuck path`;
const integrationRefusal = (name, step, number) => `pdd refused ${step}: the ${name} area has had ${INTEGRATION_ROUNDS} base integration rounds. ${integrationLimitReason(name)}. Keep the claim, progress and failed evidence. Do not retry. A person can remove pdd:stuck and pdd:working, then run pdd workflow cancel ${number}; a new run has fresh counters.`;

async function integrationSource(run, p) {
  try {
    if (await rawGit(p, run.root, 'status', '--porcelain', '--untracked-files=all')) return null;
    const head = (await rawGit(p, run.root, 'rev-parse', '--verify', 'HEAD^{commit}')).trim();
    const base = (await rawGit(p, run.root, 'merge-base', head, `refs/remotes/origin/${run.baseBranch}`)).trim();
    const tree = (await rawGit(p, run.root, 'rev-parse', `${head}^{tree}`)).trim();
    return [head, base, tree].every(commitSha) ? { head, base, tree } : null;
  } catch { return null; }
}
function accountingStep(run, area, step) {
  // Integration may have removed this result from current evidence. Its last
  // real snapshot still anchors budget decisions; it is never a fresh result.
  return run.done[step] ?? (run.integrationSources?.[area.name]?.length
    ? run.stepHistory?.findLast(row => row.step === step && row.record.area === area.name)?.record : null);
}
function integrationBaseline(run, area, step) {
  // Preserve the legacy unknown-snapshot guard for an already recorded step.
  const previous = accountingStep(run, area, step);
  if (previous && !previous.integrationSource) return null;
  const records = [...(run.stepHistory ?? []).filter(row => row.record.area === area.name).map(row => row.record),
    ...Object.values(run.done).filter(record => record.area === area.name)];
  const newest = records.filter(record => record.integrationSource
    && [record.integrationSource.head, record.integrationSource.base, record.integrationSource.tree].every(commitSha))
    .sort((a, b) => a.at - b.at).at(-1)?.integrationSource;
  return newest ?? run.integrationSources?.[area.name]?.at(-1) ?? null;
}
async function baseIntegration(run, area, step, source, p) {
  const from = integrationBaseline(run, area, step);
  if (!source || !from || ![from.head, from.base, from.tree].every(commitSha)
    || from.base === source.base || !area.steps.includes(step)) return null;
  try {
    await rawGit(p, run.root, 'merge-base', '--is-ancestor', from.base, source.base);
    await rawGit(p, run.root, 'merge-base', '--is-ancestor', from.head, source.head);
    const merged = (await rawGit(p, run.root, 'merge-tree', '--write-tree', from.head, source.base)).trim();
    if (merged !== source.tree) return null;
    return { reason: `Saved base ${run.baseBranch} advanced from ${from.base} to ${source.base}; the issue tree is unchanged by the merge.`, from, to: source };
  } catch { return null; }
}
function accountedIntegration(run, area, source) {
  return Boolean(source && run.integrationSources?.[area.name]?.some(saved => saved.tree === source.tree));
}
const repairLimitReason = name => `Repair limit reached in ${name}: take the stuck path`;
// The way out is a person's: a stuck run is still active, so a new automatic start waits until it is cancelled.
const repairRefusal = (name, step, rounds, number) => `pdd refused ${rounds ? 'another repair round' : `${step}`}: the ${name} area of this Autopilot run has had ${REPAIR_ROUNDS} repair rounds. pdd did not record ${step}; the run is stuck ("${repairLimitReason(name)}"). Take the stuck path: add pdd:stuck, write one comment with the cause, send one stuck alert, keep the claim and progress, and let the coordinator continue with other issues. Do not retry it. To let Autopilot try again, a person removes pdd:stuck and pdd:working, then runs pdd workflow cancel ${number} in the checkout that holds the stuck run; the next tick starts a new run with a fresh repair count.`;
function repairRound(run, area, step, worktree) {
  const previous = accountingStep(run, area, step);
  if (!Object.hasOwn(run, 'automaticOrigin') || !area.steps.includes(step) || !previous) return null;
  const index = area.steps.indexOf(step);
  if (!area.steps.slice(index + 1).some(item => run.done[item])) return null;
  // A later step on unchanged content is a retry, not a round. An unknown fingerprint (now or when last recorded) counts as no change.
  const recorded = previous.worktreeSha256;
  if (index > 0 && (typeof worktree !== 'string' || typeof recorded !== 'string' || recorded === worktree)) return null;
  const used = Number.isSafeInteger(run.repairRounds?.[area.name]) ? run.repairRounds[area.name] : 0;
  return used >= REPAIR_ROUNDS ? REPAIR_REFUSED : used + 1;
}
function canRefreshCodeReview(run, step) {
  const area = run.areas[run.area];
  return run.state === 'completed' && run.doneAt === 'PR 1'
    && area?.then === 'ask-code' && run.gate?.kind === 'ask-code'
    && run.gate.area === area.name && Boolean(prOf(run, area.name))
    && area.steps.includes(step) && area.steps.every(item => run.done[item]);
}
async function refreshCompletedCodeReview(run, step, p, packageRoot = PACKAGE_ROOT) {
  const selectedArea = run.area, selectedGate = structuredClone(run.gate);
  try {
    // Inspect before the short owned update. A failed inspection must retain
    // the previous review and cannot turn an ended run into ordinary progress.
    const snapshot = await gatePromptSnapshot(run, p);
    const question = await askCodeLines(run, run.areas[run.area], p);
    commitRun(run, p, latest => {
      if (!canRefreshCodeReview(latest, step) || latest.area !== selectedArea
        || ['id','area','kind','at'].some(key => latest.gate?.[key] !== selectedGate[key]))
        throw Error('The run ended or the gate changed, look again.');
      latest.gate.promptSnapshot = snapshot;
    });
    if (run.storyApproval && normalRun(run, p) && run.through === 'code') {
      protectProgress(run, p);
      const changed = await changedStoryGate(run, run.areas[run.area], step, p, snapshotLines(snapshot));
      if (changed) return doneWithRequests(changed, run, p);
      return doneWithRequests(await afterPr1(run, run.areas[run.area], p, snapshotLines(snapshot), packageRoot), run, p);
    }
    return doneWithRequests(done([...snapshotLines(snapshot), ...question].join('\n')), run, p);
  } catch (error) {
    return fail(`Cannot refresh the code-choice review: ${causeText(error?.stderr || error?.detail || error?.message) || causeOf(error)}. Repair the selection or inspect the current run and gate, then run done again and ask the person again.`);
  }
}
async function stepDoneCommand({ step, summary, skipped, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const run = await runForWorktree(cwd, p);
  if (!run) return fail('pdd workflow done works only in a run worktree. cd to the worktree that pdd made for this run.');
  if (run.state === 'cancelled') return ['replaced','handed-over'].includes(run.cancelled?.state) ? fail(stoppedRunMessage(run)) : done(stoppedRunMessage(run));
  if (run.state === 'completed') return canRefreshCodeReview(run, step)
    ? refreshCompletedCodeReview(run, step, p, packageRoot) : done(`The run for #${run.number} is complete. Stop.`);
  protectProgress(run,p);
  const area = run.areas[run.area], lines = [], normal = normalRun(run, p), automaticReturn = automaticPromptReturn(run,p);
  // After the repair limit, the run is stuck: no step of it is recorded, so it cannot go on to open a PR.
  if (Object.hasOwn(run, 'automaticOrigin') && run.repairLimit) return fail(repairRefusal(run.repairLimit.area, step, false, run.number));
  if (Object.hasOwn(run, 'automaticOrigin') && run.integrationLimit) return fail(integrationRefusal(run.integrationLimit.area, step, run.number));
  const worktree = Object.hasOwn(run, 'automaticOrigin') ? gitFingerprint(run.root) : null;
  const source = Object.hasOwn(run, 'automaticOrigin') ? await integrationSource(run, p) : null;
  const integration = source ? await baseIntegration(run, area, step, source, p) : null;
  const accounted = accountedIntegration(run, area, source);
  const chargeIntegration = integration && integration.from.tree !== source.tree && !accounted;
  if (chargeIntegration && (run.integrationRounds?.[area.name] ?? 0) >= INTEGRATION_ROUNDS) {
    commitRun(run, p, latest => {
      if (ended(latest) || latest.area !== run.area || gitFingerprint(run.root) !== worktree || !equalFact(integrationBaseline(latest, area, step), integration.from)) throw Object.assign(Error('The run changed; look again.'), { code: 'workflow_progress_refused' });
      latest.state = 'stuck'; latest.parkReason = integrationLimitReason(area.name); latest.integrationLimit = { area: area.name, step, at: p.now() };
    });
    return fail(integrationRefusal(area.name, step, run.number));
  }
  if (!integration && !accounted && repairRound(run, area, step, worktree) === REPAIR_REFUSED) {
    commitRun(run, p, latest => {
      if (ended(latest) || latest.area !== run.area || repairRound(latest, area, step, worktree) !== REPAIR_REFUSED) throw Object.assign(Error('The run changed; look again.'), { code: 'workflow_progress_refused' });
      latest.state = 'stuck'; latest.parkReason = repairLimitReason(area.name); latest.repairLimit = { area: area.name, step, at: p.now() };
    });
    return fail(repairRefusal(area.name, step, true, run.number));
  }
  if (await reopenChangedStory(run,p)) return done(`The Story or expected contract changed. Finish the Story steps and show its approval gate again. PR 1 remains the prompt branch. Run pdd workflow open ${run.number}.`);
  if (run.promptReturn && !area.steps.includes(step) && run.areas.slice(run.area+1).some(item=>item.steps.includes(step)))
    return fail('This step belongs to a later area. Finish the current prompt work first.');
  if (!area.steps.includes(step)) lines.push(`warning: "${step}" is not a step of the ${area.name} area (${area.steps.join(', ')}). pdd recorded it anyway.`);
  else {
    const before = area.steps.slice(0, area.steps.indexOf(step)).filter(item => !run.done[item] && !area.optional.includes(item));
    if (before.length) lines.push(`warning: ${before.join(', ')} ${before.length > 1 ? 'are' : 'is'} not done yet. pdd recorded ${step} anyway.`);
  }
  const observedQuestion=run.question, observedGate=run.gate;
  const reason = skipped === undefined ? null : keepLines(skipped) || 'no reason given';
  const record = { at: p.now(), summary: keepLines(reason === null ? summary : [`skipped: ${reason}`, summary].filter(Boolean).join('\n')), area: area.name,
    ...(reason === null ? {} : { skipped: { reason } }), ...(PROOF_STEPS.includes(step) ? { pddResults: ownResults(run, p) } : {}),
    ...(typeof worktree === 'string' ? { worktreeSha256: worktree } : {}),
    ...(source ? { integrationSource: source } : {}), ...(integration ? { integration } : {}) };
  if (run.workflow === 'bug' && step === 'reproduce' && reason === null) {
    try {
      const note = join(run.runDir, 'reproduce.md');
      let text = record.summary;
      try {
        if (!lstatSync(note).isFile()) throw Object.assign(Error('reproduce.md must be a regular file.'), { code: 'bug-cause-invalid' });
        text = readFileSync(note, 'utf8');
      } catch (error) { if (error.code !== 'ENOENT') throw error; }
      const result = await recordBugCause({ text, repository: run.repo, number: run.number, root: run.root }, p);
      if (result.json) record.bugCause = JSON.parse(result.json);
    } catch (error) { return fail(`${error.code ?? 'bug-cause-unavailable'}: ${error.message}`); }
  }
  if (PROOF_STEPS.includes(step) && reason === null) {
    const usable = record.pddResults.some(usableResult), shown = usable || !record.pddResults.length ? resultLines(record.pddResults) : [...resultLines(record.pddResults), noResultLine()];
    lines.push(...(usable ? ['pdd recorded its own results with this step:'] : ['warning: pdd has no result of its own for this run yet. pdd recorded the step with the label "no pdd result".']), ...shown,
      'Your summary is saved as an agent note, apart from pdd\'s results.');
  }
  if (reason !== null) lines.push(`pdd recorded that ${step} was skipped. Reason (agent note): ${oneLine(reason)}`);
  const hasRuntime=runtimeLines(record.summary).length>0;
  if(hasRuntime)record.source={kind:'git-content-v1',sha256:gitFingerprint(run.root)};
  const replay=area.replay_evidence===REPLAY_POLICY && (area.steps.some(item=>item!==step&&!run.done[item]) || area.gate!=='pr' || area.before==='approve'&&!prOf(run,area.name))?await currentReplayEvidence(run,p):null;
  if(replay){record.replayEvidence=replay;lines.push(formatReplayEvidence(replay,{rules:await rulesToCheck(run,p,record.summary)}));}
  if (run.workflow === 'small-change' && !askArea(run) && ['scope','change','verify','formal'].includes(step))
    record.smallChange = {checklist: readSmallChangeChecklist(run), formal: readFormalEvidence(run)};
  const applyDone=latest=>{
    if (integration || accounted) {
      if (gitFingerprint(run.root) !== worktree || accountedIntegration(latest, area, source) !== accounted
        || integration && !equalFact(integrationBaseline(latest, area, step), integration.from)) throw Object.assign(Error('The run changed; look again.'), { code: 'workflow_progress_refused' });
    }
    if (chargeIntegration) {
      const used = latest.integrationRounds?.[area.name] ?? 0;
      if (used >= INTEGRATION_ROUNDS) throw Object.assign(Error('The run changed; look again.'), { code: 'workflow_progress_refused' });
      latest.integrationRounds = { ...latest.integrationRounds, [area.name]: used + 1 };
      latest.integrationSources = { ...latest.integrationSources, [area.name]: [...(latest.integrationSources?.[area.name] ?? []), source] };
      lines.push(`Base integration round ${used + 1} of ${INTEGRATION_ROUNDS} in the ${area.name} area. ${integration.reason}`);
    }
    const round=integration || accounted ? null : repairRound(latest,area,step,worktree);
    if(round===REPAIR_REFUSED)throw Object.assign(Error('The run changed; look again.'),{code:'workflow_progress_refused'});
    if(round){latest.repairRounds={...latest.repairRounds,[area.name]:round};lines.push(`Repair round ${round} of ${REPAIR_ROUNDS} in the ${area.name} area of this Autopilot run.`);}
    endRuntimeWait(latest);
    if (reason === null && latest.environmentRetry?.area === latest.area && latest.environmentRetry.step === step) { delete latest.environmentRetry; delete latest.stuckCause; }
    if(equalFact(latest.question,observedQuestion))latest.question=null;
    const later=area.steps.includes(step) && (latest.done[step] || round)?area.steps.slice(area.steps.indexOf(step)+1).filter(item=>latest.done[item]):[];
    // Integration can first return through a later step, such as a failed PR-open
    // retry. Earlier records on the old tree are stale too; keep their identities
    // in history and let the ordinary next-step selection request fresh records.
    const stale = integration && integration.from.tree !== source.tree
      ? Object.keys(latest.done).filter(item => latest.done[item].integrationSource?.tree
        && latest.done[item].integrationSource.tree !== source.tree) : [];
    if (Object.hasOwn(latest, 'automaticOrigin')) {
      const replaced = new Set([...(latest.done[step] ? [step] : []), ...later, ...stale]);
      for (const item of replaced) (latest.stepHistory ??= []).push({ step: item, record: latest.done[item], supersededAt: record.at });
    }
    // A step that pdd skipped itself is cleared without a warning; pdd skips it again below.
    const told=later.filter(item=>latest.done[item]?.skipped?.by!=='pdd');
    for(const item of new Set([...later, ...stale]))delete latest.done[item];
    const earlierStale = stale.filter(item => item !== step && !later.includes(item));
    if (earlierStale.length) lines.push(`Source changed: pdd cleared ${earlierStale.join(', ')}; record those steps again on the integrated tree.`);
    if(told.length)lines.push(`warning: ${step} ran again after ${told.join(', ')}. pdd cleared ${told.length>1?'those steps':'that step'}; run ${told.length>1?'them':'it'} again.`);
    if(hasRuntime)(latest.runtimeHistory??=[]).push({...record,step});
    // pdd's own pdd test results, once per batch, so a later partial check keeps the Stories of an earlier one.
    for(const result of record.pddResults??[])if(result.kind==='pdd test'&&!(latest.pddHistory??=[]).some(item=>item.batch===result.batch))latest.pddHistory.push(result);
    if(replay)latest.replayEvidence=replay;
    latest.done[step]=record;
  };
  let next, currentArea, autoSkipped=false;
  const gateAt=p.now();
  commitRun(run,p,latest=>{
    applyDone(latest);
    next=area.steps.find(item=>!latest.done[item]);
    // Normal runs (#2962): the optional try step before PR 1 is not asked; the person can ask for it at the Story card.
    if((normal||automaticReturn)&&next==='try'&&step!=='try'&&area.optional.includes('try')&&area.before==='approve'){
      latest.done.try={at:p.now(),summary:`skipped: ${TRY_SKIP}`,area:area.name,skipped:{reason:TRY_SKIP,by:'pdd'}};
      autoSkipped=true;
      next=area.steps.find(item=>!latest.done[item]);
    }
    currentArea=latest.areas[latest.area]?.name===area.name;
    if(currentArea && equalFact(latest.gate,observedGate)){
      if(next){latest.state=latest.question?'waiting':'running';latest.gate=null;}
      else if(area.gate==='pr'&&area.before==='approve'&&(!prOf(latest,area.name)||latest.promptReturn&&(normal||automaticReturn)&&storyCoverage(latest))){latest.gate={id:p.randomUUID(),area:area.name,at:gateAt,kind:'approve-pr'};latest.state='waiting';}
      else if(area.gate!=='pr'){latest.gate={id:p.randomUUID(),area:area.name,at:gateAt,kind:'approve'};latest.state='waiting';}
    }
  });
  if(!currentArea)return doneWithRequests(done(`pdd recorded ${step}.`),run,p);
  if(autoSkipped)lines.push(`pdd skipped the optional try step (${TRY_SKIP}). Do not ask the person about it.`);
  if (next) {
    lines.push(`Saved base: ${run.baseBranch}. Use this saved base; never take a base from documents.`, `pdd recorded ${step}.`, area.optional.includes(next)
      ? `Next step: ${next} (optional). Ask the person if they want it. If they do not, run: ${p.pdd} workflow done ${next} --summary "skipped"`
      : `Next step: ${next}.`, `When it is done, run: ${p.pdd} workflow done ${next} --summary "one line"`);
    return doneWithRequests(done(lines.join('\n')), run, p);
  }
  // Try before PR 1 (#13): the person tries the result and approves before pdd opens the area's PR.
  if (area.gate === 'pr' && area.before === 'approve' && (!prOf(run, area.name) || (normal || automaticReturn) && storyCoverage(run))) {
    const contents = await worktreeContents(run, p);
    lines.push(...await showGate(run, p));
    if (normal || automaticReturn) {
      const routed = await normalPromptGate(run, area, step, p, lines, contents, packageRoot);
      if (routed) return doneWithRequests(routed, run, p);
    }
    lines.push(`pdd recorded ${step}. The ${area.name} area is done; pdd opens ${prLabel(run, area)} after the person approves.`,
      nothingToTry(run, area, contents)
        ? 'Gate: show the person the Prompt tests line of each Story (one per Story: ✓, ✗ or no verdict) with the report link, if there is one. There is nothing to try. Ask them to approve or ask for changes. Stop. Do not approve for them.'
        : 'Gate: show the person the Prompt tests line of each Story (one per Story: ✓, ✗ or no verdict) with the report link, and simulation details (the Try link when it opens a page). Ask them to try it, then approve or ask for changes. Stop. Do not approve for them.',
      ...(prLabel(run, area) === 'PR 1' ? [`Tell the person what PR 1 holds, in these words: "${holdsLine(contents)}"`] : []),
      approvalGuide(run, p.pdd),
      'If they ask for changes, revise in this chat, run done again for the step you changed, and ask again.');
    return doneWithRequests(done(lines.join('\n')), run, p);
  }
  if (area.gate === 'pr') {
    return doneWithRequests(await finishPr(run,area,step,p,lines),run,p);
  }
  lines.push(...await showGate(run, p));
  if (run.area === storyGateIndex(run)) lines.push('You may offer pdd simulate <story> before the check: it automatically opens a shell for a command-line program, localhost with an example request for HTTP routes, the Simulator page for screens, or Form for typed operations. Use pdd simulate for the whole project.');
  const automatic = automaticHandoff(run, p, packageRoot);
  if (!automatic && normal && area.gate === 'approve' && run.area === storyGateIndex(run)) {
    const changed = await changedFiles(run, p), gateId = run.gate?.id, storySnapshot = storyFingerprint({ root: run.root, changed });
    commitRun(run, p, latest => { if (latest.gate && latest.gate.id === gateId) latest.gate.storySnapshot = storySnapshot; });
    lines.push(`pdd recorded ${step}. The ${area.name} area is done.`, await cardText(run, p), cardGate, approvalGuide(run, p.pdd),
      'If they ask for changes, revise in this chat, run done again for the step you changed, and show the new card.');
    return doneWithRequests(done(lines.join('\n')), run, p);
  }
  lines.push(`pdd recorded ${step}. The ${area.name} area is done.`,
    ...(automatic ? [automatic, 'Gate: show the result and follow the scoped automatic overlay and owner handoff; preserve required human decisions.'] : ['Gate: show the person the result, ask them to approve it or ask for changes, and stop. Do not approve for them.', approvalGuide(run, p.pdd), 'If they ask for changes, revise in this chat, run done again for the step you changed, and ask again.']));
  return doneWithRequests(done(lines.join('\n')), run, p);
}

// The code area works on <branch>-code: on PR 1's head while PR 1 is open (PR 2 stacks on it), else on the merged saved base branch.
async function codeBranch(run, area, p, acceptSource) {
  const pr1 = prOf(run, area.name), name = `${pr1.branch}-code`;
  const state = await (p.readPrStatus ?? readWorkflowPrStatus)({ cwd: run.root, url: pr1.url }, p.commandPorts);
  if (!['open', 'merged'].includes(state.state)) throw Error(`PR 1 is ${state.state}, so pdd cannot tell where the code branch should start.`);
  const fetch = async ref => {
    try {
      const reply = await p.execFile('git', ['fetch', 'origin', `refs/heads/${ref}:refs/remotes/origin/${ref}`], { cwd: run.root });
      if (reply.code !== undefined && reply.code !== 0) throw Error('fetch rejected');
    } catch { throw Error(`Could not fetch ${ref} from origin. No code branch was created; try again when the remote branch is available.`); }
  };
  const upstream=state.state==='merged'?run.baseBranch:pr1.branch;
  await fetch(upstream);
  const source = await git(p,run.root,'rev-parse','--verify',`refs/remotes/origin/${upstream}^{commit}`);
  if (!commitSha(source)) throw Error('The fetched prompt source is unavailable.');
  const contract = await storyContract(run,p,source);
  const expected = run.promptReturn ? approvedStoryContract(run) : run.storyApproval ? approvedStoryContract(run) ?? p.codeEntryContract : p.codeEntryContract ?? await storyContract(run,p);
  const localHead = await git(p,run.root,'rev-parse','--verify','HEAD^{commit}');
  let sourceEdits = (await rawGit(p,run.root,'diff','--name-only','-z',localHead,source)).split('\0').filter(Boolean);
  if (state.state === 'merged') {
    // The saved base also carries other runs. Compare byte changes only for
    // PR 1's paths and anchored scenarios; the contract check below still
    // covers all saved approved Story paths, including deletions.
    const publishedPaths = new Set(Array.isArray(pr1.sourcePaths) ? pr1.sourcePaths
      : (await rawGit(p,run.root,'diff','--name-only','-z',run.baseSha,localHead)).split('\0').filter(Boolean));
    for (const vector of run.replayBaseline?.vectors ?? []) publishedPaths.add(vector.path);
    sourceEdits = sourceEdits.filter(path=>publishedPaths.has(path));
  }
  const scenarioEdits = [];
  for (const path of sourceEdits.filter(path=>path.endsWith('.json'))) {
    const saved = run.replayBaseline?.vectors?.some(vector=>vector.path===path);
    let scenario = saved;
    for (const ref of [localHead,source]) {
      try { scenario ||= isScenario(await rawGit(p,run.root,'show',`${ref}:${path}`)); } catch { /* Absence is a changed source too. */ }
    }
    if (scenario) scenarioEdits.push(path);
  }
  // A peer's new specification belongs on PR 1. Never admit it by checking
  // the old local files and then merging a moving remote ref into code.
  const changedSpecification = contract !== expected || scenarioEdits.length || sourceEdits.some(path=>path.endsWith('.prompt.md'));
  if (changedSpecification) {
    if (state.state === 'open') {
      try { await rawGit(p,run.root,'merge','--ff-only',source); }
      catch (error) { await reopenChangedStory(run,p,expected,contract); throw error; }
    }
    if (await reopenChangedStory(run,p,expected,contract)) throw Error('The fetched Story or expected contract changed. Finish the Story area and show its gate again.');
    resetPromptChecks(run,p);
    throw Error('The fetched prompt source changed. Run prompt checks and publish PR 1 again before entering code.');
  }
  const failure = await codeEntryFailure(run,p);
  if (failure) throw Error(failure);
  const returned = Boolean(run.promptReturn);
  let switched = false;
  try {
    if (returned) {
      await git(p,run.root,'switch','-q',name); switched = true;
      await rawGit(p,run.root,'merge','--no-edit',source);
    } else {
      await git(p,run.root,'switch','-q','-c',name,source); switched = true;
    }
    p.validateCodeSource = async () => {
    // Existing code commits must not override the validated contract, prompt
    // tree or scenario bytes. A merge conflict and an unsafe resolved merge
    // both keep the saved workflow in prompt space with no new code decision.
      if (await storyContract(run,p) !== contract) throw Error('The code merge changes the approved Story contract. Return to PR 1 and repair the code merge.');
    if (await rawGit(p,run.root,'diff','--name-only','-z',source,'--','*.prompt.md')) throw Error('The code merge changes prompts. Repair them through PR 1.');
    for (const path of gitFiles(run.root).filter(path=>path.endsWith('.json'))) {
      let scenario = run.replayBaseline?.vectors?.some(vector=>vector.path===path);
      try { scenario ||= isScenario(readFileSync(join(run.root,path),'utf8')); } catch { /* The contract reader handles malformed anchored files. */ }
      if (scenario && await rawGit(p,run.root,'diff','--name-only','-z',source,'HEAD','--',path)) throw Error('The code merge changes scenario bytes. Repair them through PR 1.');
    }
      const untracked=(await rawGit(p,run.root,'ls-files','--others','--exclude-standard','-z')).split('\0');
      if (untracked.some(path=>path.endsWith('.prompt.md'))) throw Error('Unpublished prompts remain. Repair them through PR 1.');
    };
    await p.validateCodeSource();
    await acceptSource();
  } catch (error) {
    if (switched) {
      await rawGit(p,run.root,'merge','--abort').catch(()=>{});
      await git(p,run.root,'switch','-q',pr1.branch);
      if (!returned) await rawGit(p,run.root,'branch','-d',name).catch(()=>{});
    }
    throw Error(`${oneLine(error.message)} Resolve code conflicts on the code branch, return to PR 1, then retry the code gate.`);
  }
  run.prBase=upstream;
  run.branch = name;
  return state.state === 'merged' ? ` PR 1 is merged, so the code branch ${name} starts from ${run.baseBranch}.`
    : ` The code branch ${name} starts from PR 1, and PR 2 will be stacked on it.`;
}

// A run whose saved config folder is gone cannot start or resume a chat (the agent stops at once), so pdd refuses first.
function missingHome(run, env) {
  const dir = expandHome(run.configDir, env), variable = homeVariable(run.agent);
  return dir && !isFolder(dir) ? `This run uses ${variable} "${dir}", but that folder does not exist. Make that folder, or cancel the run (pdd workflow cancel ${run.number}) and start it again with the right ${variable}.` : null;
}

// At the code gate of an open PR 1, PR 1 must hold what the person approved (0.1.6 testers: pdd approve commits nothing,
// and an approval committed by hand went to PR 2 while PR 1 still said "Draft prompts"). pdd commits each PR 1 draft prompt
// that is approved in the worktree now, pushes the worktree's new commits to PR 1 (a fast-forward only; pdd never forces),
// and updates the "Draft prompts" line of PR 1's description. When it cannot, it says the exact commands to run.
async function syncPr1(run, p) {
  const pr1 = prOf(run, askArea(run).name), before = await pr1Drafts(run, p);
  if (run.state === 'completed' || !pr1 || run.branch !== pr1.branch) return { drafts: before, lines: [] };
  if ((await (p.readPrStatus ?? readWorkflowPrStatus)({ cwd: run.root, url: pr1.url }, p.commandPorts)).state !== 'open') return { drafts: before, lines: [] };
  try { await requireExistingDraft(run, pr1, p); }
  catch (error) { if(error?.code==='workflow_progress_refused')throw error;return {failed:error.message}; }
  const approved = before.filter(path => {
    try { const found = statuses(readFileSync(join(run.root, path), 'utf8')); return found.includes('approved') && !found.includes('draft'); } catch { return false; }
  });
  const go = `cd ${shell(run.root)} && `, again = (run.decisions ?? []).some(decision => decision.gateId === run.gate?.id && decision.evidence) ? approvalRetry(run, p.pdd) : approvalGuide(run, p.pdd), what = approved.length ? `your approval of ${listed(approved)}` : null;
  if (approved.length) {
    try { await git(p, run.root, 'commit', '-q', '-m', `Approve ${approved.join(', ')}`, '--', ...approved); }
    catch { return { failed: `pdd could not commit ${what}. Run: ${go}git commit -m ${shell(`Approve ${approved.join(', ')}`)} -- ${approved.map(shell).join(' ')}\n${again}` }; }
  }
  try { await p.execFile('git', ['fetch', 'origin', run.branch], { cwd: run.root }); } catch { /* The last fetched PR 1 head decides. */ }
  const remote = `refs/remotes/origin/${run.branch}`;
  let ahead = 0, behind = false;
  try { ahead = Number(await git(p, run.root, 'rev-list', '--count', `${remote}..HEAD`)) || 0; behind = Number(await git(p, run.root, 'rev-list', '--count', `HEAD..${remote}`)) > 0; } catch {
    if (replayEnabled(run)) return {failed:`Cannot verify the published prompt-space head. Fetch the prompt branch and ${approvalGuide(run, p.pdd)}.`};
    ahead = 0;
  }
  const entryFailure=await codeEntryFailure(run,p);if(entryFailure)return {failed:entryFailure};
  if (behind && replayEnabled(run)) return {failed:`The prompt branch is behind its published head. Update the worktree from origin/${run.branch}, then ${approvalGuide(run, p.pdd)}.`};
  const rememberHead = async () => {
    const observed = await readPublishedPr1(run,pr1,p);
    commitRun(run,p,latest=>{const pr=latest.pr.find(pr=>pr.url===pr1.url&&pr.stage===pr1.stage);if(pr)pr.publishedHeadSha=observed.headSha;});
  };
  if (!ahead && !behind) {
    try { await rememberHead(); }
    catch (error) { if(error?.code==='workflow_progress_refused')throw error;return {failed:`${oneLine(error.message)} Check the published PR 1 head, then ${again}`}; }
    const changed=await refreshReplayBaseline(run,p,true);if(changed)return {failed:changed};
  }
  if (ahead && behind && what) return { failed: `PR 1 has commits that this worktree does not have, so pdd did not push ${what}. Run: ${go}git pull --rebase origin ${shell(run.branch)} && git push origin HEAD:refs/heads/${run.branch}\n${again}` };
  if (!ahead || behind) {
    const drafts = approved.length ? await pr1Drafts(run, p) : before;
    return { drafts, lines: await draftDescription(run, pr1, drafts, p) };
  }
  const adoption=await adoptionFailure(run,p);if(adoption)return {failed:adoption};
  const pushedHead = await git(p,run.root,'rev-parse','--verify','HEAD^{commit}');
  const pending = await draftDescription({...run, publicationPending:true}, pr1, before, p);
  if (pending.some(line => line.startsWith('warning:'))) return { failed: `${pending.join('\n')} No source was pushed. ${again}` };
  try { await rawGit(p,run.root,'push','origin',`${pushedHead}:refs/heads/${run.branch}`); }
  catch { return { failed: `pdd could not push ${what ?? `the worktree's new commit${ahead > 1 ? 's' : ''}`} to PR 1. Run: ${go}git push origin HEAD:refs/heads/${run.branch}\n${again}` }; }
  if (await git(p,run.root,'rev-parse','--verify','HEAD^{commit}') !== pushedHead) return { failed: 'Source was pushed; the local head changed. PR 1 stays publication-pending; retry from the pushed source.' };
  try { await rememberHead(); }
  catch (error) { if(error?.code==='workflow_progress_refused')throw error;return {failed:`${oneLine(error.message)} Source was pushed; PR 1 publication remains unconfirmed. ${again}`}; }
  const changed=await refreshReplayBaseline(run,p,true);if(changed)return {failed:changed};
  const drafts = await pr1Drafts(run, p);
  return { drafts, lines: [what ? `pdd committed ${what} and pushed it to PR 1.` : `pdd pushed ${ahead} new commit${ahead > 1 ? 's' : ''} from the worktree to PR 1.`, ...await draftDescription(run, pr1, drafts, p)] };
}

// PR 1's description names its draft prompts; after a push to PR 1 that line must say the new truth. A failure only warns.
async function draftDescription(run, pr1, drafts, p) {
  try {
    await requireExistingDraft(run, pr1, p);
    const body = JSON.parse(String((await p.execFile('gh', ['pr', 'view', pr1.url, '--json', 'body'], { cwd: run.root })).stdout ?? '')).body;
    if (typeof body !== 'string') throw Error('PR 1 description unavailable.');
    const old = body.split('\n').find(line => line.startsWith('Draft prompts: '));
    const draftBody = !old ? body : drafts.length ? body.replace(old, draftLine(drafts)) : body.replace(`\n\n${old}`, '').replace(old, '');
    const area = askArea(run), evidence = await publicationEvidence(run, area, p), marker = `<!-- pdd-workflow:${run.runId}:${area.name} -->`;
    if (evidence.lines.some(line => line.includes('pdd-workflow:')) || String(draftBody).replace(marker, '').includes('pdd-workflow:')) throw Error('Remove supplied workflow ownership markers.');
    // #3042: a readable description keeps pdd's body in its Details section; an older description is all pdd body and
    // gets the readable part now. The readable part is made again from the current records.
    const inside = detailsOf(String(draftBody).replace(marker, ''));
    const head = run.branch === pr1.branch ? 'HEAD' : `refs/remotes/origin/${pr1.branch}`;
    let headSha = '';
    try { headSha = await git(p, run.root, 'rev-parse', '--verify', `${head}^{commit}`); } catch { /* The checker verdict stays unknown. */ }
    const facts = await readableFacts(run, area, p, evidence, { drafts, published: await publishedChecks(run, pr1, headSha, p), base: pr1.base, head });
    const readable = readableTopText(facts, run);
    // The facts are saved with PR 1's head, so that status can refresh its top later; a pending body is not saved.
    const remember = () => { if (!run.publicationPending && commitSha(headSha)) commitRun({ ...run }, p, latest => { const pr = latest.pr.find(item => item.url === pr1.url && item.stage === pr1.stage); if (pr) pr.readable = savedReadable(facts, headSha); }); };
    const opening = `${readable.text.trimEnd()}\n\n${DETAILS_OPEN}\n\n${TOP_NOTE}\n\n`;
    const closing = `${readable.notes.length ? `\n\n${readable.notes.join('\n')}` : ''}\n\n</details>${inside?.after ? `\n\n${inside.after}` : ''}`;
    const owned = /^(?:Check evidence: publication-pending|Agent note — not checked by pdd: (?:Not fixed yet:|Not checked:|Defect:|Not caught because:|Proof \(defect fixed\):|Proof \(gap closed\):|Review:|Verdict:|Before[ :])|Not fixed yet:|Not checked:|Defect:|Not caught because:|Proof \(defect fixed\):|Proof \(gap closed\):|Old-code proof:|Tests vs base:|Review:|Evidence omitted:)/;
    const reference = new RegExp(`^(?:Part of|Closes|Refs) #${run.number}$`);
    const rows = (inside ? inside.details : String(draftBody).replace(marker, '')).split('\n');
    let at = 0;
    const labelledTop = [];
    while (at < rows.length && owned.test(rows[at])) {
      if (/^Agent note — not checked by pdd: (?:Verdict:|Before[ :])/.test(rows[at])) labelledTop.push(rows[at]);
      at++;
    }
    while (at < rows.length && !rows[at].trim()) at++;
    const headerStart = at;
    while (at < rows.length && new RegExp(String.raw`^(?:pdd result: |Agent note — not checked by pdd: (?:Verdict:|Before[ :]|${PROMPT_TESTS_WORDS}|Report(?: \([^)]*\))?:)|Verdict:|Before |Before:|${PROMPT_TESTS_WORDS}|Report(?: \([^)]*\))?:)`).test(rows[at])) at++;
    const priorTop = rows.slice(headerStart, at);
    const ordinaryTop = [...ownLines(run, evidence), ...new Set([...labelledTop, ...priorTop.filter(line => /^(?:Agent note — not checked by pdd: )?(?:Verdict:|Before[ :])/.test(line)).map(line => line.startsWith(`${AGENT_NOTE}: `) ? line : `${AGENT_NOTE}: ${line}`)].map(closingInert)), ...publicationRuntime(run, p.env, 'pr1')];
    const introduction = [];
    while (at < rows.length && !rows[at].trim()) at++;
    if (reference.test(rows[at] ?? '')) {
      at++;
      while (at < rows.length && !rows[at].trim()) at++;
      // An older description's one-line introduction goes: the readable part's Next line says what comes next.
      if (/^PR 1 of this run:/.test(rows[at] ?? '')) {
        at++;
        while (at < rows.length && !rows[at].trim()) at++;
      }
      while (at < rows.length && (/^Approved in (?:chat|terminal|area chat): /.test(rows[at]) || /^Evidence omitted: \d+ approval evidence records omitted\./.test(rows[at]))) at++;
      while (at < rows.length && !rows[at].trim()) at++;
    }
    // pdd's own full step summaries (with their cut notice) leave the rest; they come back fitted like a new PR body.
    const remaining = rows.slice(at), overview = remaining.indexOf('## Steps');
    // Only the runner's contiguous overview is rewritten. Reviewer examples and
    // fenced prose elsewhere retain their exact text.
    if (overview >= 0) for (let index = overview + 1; /^- \*\*[^*]+\*\*:/.test(remaining[index] ?? ''); index++) {
      if (!remaining[index].includes(AGENT_NOTE)) remaining[index] = noteRuntime(remaining[index]).replace(/(:) /, `$1 ${AGENT_NOTE}: `);
    }
    const rest = [...introduction, ...remaining], start = rest.indexOf(FULL_SUMMARIES), end = start < 0 ? -1 : rest.indexOf('</details>', start);
    const from = end < 0 ? -1 : start >= 2 && !rest[start - 1] && SHORTENED.test(rest[start - 2]) ? start - 2 : start;
    const steps = from < 0 ? [] : prSteps(run, area), texts = Object.fromEntries(steps.map(step => [step, keepLines(cleanSummary(run, step))]));
    const reserved = from < 0 ? 0 : characters(fullSummaries(steps, texts, 0).join('\n')) + 2;
    const safeRemainder = hideLocalPaths(redactTry((from < 0 ? rest : [...rest.slice(0, from), SLOT, ...rest.slice(end + 1)]).join('\n')), run);
    const footer = `${closing}\n\n${marker}\n`;
    const approvalLines = (evidence.approvalLines ?? []).map(line => hideLocalPaths(redactTry(line), run));
    const room = BODY_BUDGET - characters(opening) - characters(footer) - characters(evidence.issueReference) - characters(ordinaryTop.join('\n')) - 8;
    const { lifted, approvals } = publicationFit(evidence.lines.map(line => hideLocalPaths(redactTry(line), run)), approvalLines, Math.max(0, room - Math.min(1000, characters(safeRemainder) + reserved)), p.env);
    const leading = opening + [...lifted, ...(lifted.length ? [''] : []), ...ordinaryTop, ...(ordinaryTop.length ? [''] : []), evidence.issueReference, '', ...approvals, ...(approvals.length ? [''] : []), ''].join('\n');
    const fitted = verifyFit(safeRemainder, BODY_BUDGET - characters(leading) - characters(footer) - reserved, p.env, true);
    const placed = section => { const text = section.join('\n'); return fitted.includes(SLOT) ? fitted.replace(SLOT, () => text) : `${fitted}\n\n${text}`; };
    const nextBody = from < 0 ? `${leading}${fitted}${footer}` : withSummaries(steps, texts, section => `${leading}${placed(section)}${footer}`, BODY_BUDGET);
    // Only the time of the status line changed: nothing to write.
    if (nextBody === body || sameReadableTop(nextBody, body)) { remember(); return []; }
    const reply = await p.execFile('gh', ['pr', 'edit', pr1.url, '--body-file', '-'], { cwd: run.root, input: nextBody });
    if (reply.code !== undefined && reply.code !== 0) throw Object.assign(Error('PR 1 description update failed.'), { code: reply.code });
    remember();
    return [`pdd updated the PR 1 description: ${drafts.length ? `draft prompts left: ${drafts.join(', ')}` : 'no draft prompts are left'}.`];
  } catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return [`warning: pdd could not update the PR 1 description (${error.code ?? 'error'}). ${run.publicationPending ? 'No source was pushed.' : 'The PR retains its previous evidence; after a source push it stays publication-pending.'}`]; }
}

// A terminal in the run's own chat pane (Herdr session pdd) belongs to the chat; a person's other Herdr tab does not.
const chatPane = (run, env) => env.HERDR_PANE_ID && /[\\/]sessions[\\/]([^\\/]+)[\\/][^\\/]+$/.exec(String(env.HERDR_SOCKET_PATH ?? ''))?.[1] === PDD_HERDR_SESSION
  ? (run.chats ?? []).find(chat => chat.paneId === env.HERDR_PANE_ID) ?? null : null;

function armCurrentAutomaticChat(run, p) {
  if (!run.automaticOrigin) return;
  let coordinatorPaneId;
  try {
    const id = createHash('sha256').update(realpathSync(run.sourceRoot)).digest('hex').slice(0, 20);
    const folder = p.autopilotStateRoot ?? join(p.env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
    const state = JSON.parse(readFileSync(join(folder, `${id}.json`), 'utf8'));
    if (state.enabled) coordinatorPaneId = state.paneId;
  } catch {}
  if (!coordinatorPaneId && /[\\/]sessions[\\/]pdd-autopilot[\\/]/.test(String(p.env.HERDR_SOCKET_PATH ?? ''))) coordinatorPaneId = p.env.HERDR_PANE_ID;
  if (!armSavedWorkerCompletion(run, coordinatorPaneId, p)) p.say(`Automatic completion observer unavailable. After positive completion evidence, run pdd workflow yield ${run.number}.`);
  else p.say(`If automatic completion observation becomes unavailable, inspect the worker and run pdd workflow yield ${run.number} after positive completion evidence.`);
}

async function startNextChat(run, p, packageRoot) {
  if (run.parking) commitRun(run, p, fresh => {fresh.parking.phase = 'waking';});
  const area = run.areas[run.area], original = structuredClone(run);
  let prior = lastChat(run, area.name);
  if (run.promptReturn && prior) {
    // Re-entry keeps native session custody. Never launch a second agent over
    // the saved pane when revisiting an area that already has a chat.
    const observed=structuredClone(prior);
    await openChat({run,chat:observed},{...p,isTTY:false});
    if (!saveChatObservations(original,prior,observed,p)) throw Error('The returned area chat changed. Open the current area again.');
    if (Number.isFinite(observed.resumedAt) && launchAnchor(observed) !== launchAnchor(prior)) {
      const saved=readRun(run.runDir);
      if (saved?.runId===run.runId && saved.area===run.area && launchAnchor(lastChat(saved,area.name))===launchAnchor(observed)) armCurrentAutomaticChat(saved,p);
    }
    await deliverRequest(run,await areaMessage(run,run.area,p,packageRoot),p,true);
    return observed;
  }
  const reusedPane = Boolean(prior?.paneId);
  p.say(`Starting the ${area.name} chat in Herdr…`);
  // The starting identity is saved before the native launch. A failed save or an ended run sends nothing.
  const checkpoint = async (chat, layout) => {
    if (layout && run.parking) layout.phase = 'open';
    const latest = readRun(run.runDir);
    if (latest && ended(latest)) throw Object.assign(Error(`The run ended (${latest.state}). Stop working on it.`), { code: 'workflow_progress_refused' });
    if (!saveChatObservations(original, prior, chat, p, { checkpoint: true, layout }))
      throw Object.assign(Error('The run changed before the chat launch, so pdd sent nothing.'), { code: 'chat_checkpoint_refused' });
    if (chat) prior = structuredClone(chat);
  };
  const endedMeanwhile = () => {
    const latest = readRun(run.runDir);
    if (latest?.runId === run.runId && ended(latest)) throw Object.assign(Error(`The run ended (${latest.state}). Stop working on it.`), { code: 'workflow_progress_refused' });
  };
  try {
    const chat = await startChat({ run, area: area.name, message: await areaMessage(run, run.area, p, packageRoot) }, { ...p, checkpoint });
    run.chats.push(chat);
    // Cancel closes the saved starting chat; a late launch reply cannot report a started chat in an ended run.
    const saved = saveChatObservations(original, prior, chat, p);
    if (!saved) endedMeanwhile();
    if (saved && !chat.startUnconfirmed && run.parking) commitRun(run, p, fresh => {delete fresh.parking;});
    if (saved && !chat.startUnconfirmed && !reusedPane) armCurrentAutomaticChat(run, p);
    return run.chats.at(-1);
  } catch (error) {
    if (['workflow_progress_refused', 'workflow_run_save_failed'].includes(error?.code)) throw error;
    if (error.chat?.area === area.name) run.chats.push(error.chat);
    saveChatObservations(original, prior, error.chat, p, { error, phase: 'start' });
    throw error;
  }
}

function reviewSha256(text) {
  for (const block of interfaceBlocks(text)) text = text.replace(block[0], '');
  return createHash('sha256').update(text.replace(/\s+/g, ' ').trim()).digest('hex');
}
function samePromptReview(current, saved) {
  return Array.isArray(saved) && current.length === saved.length && current.every((row, index) => {
    const prior = saved[index];
    return row.path === prior.path && (prior.reviewSha256 === undefined
      ? row.proseSha256 === prior.proseSha256 : row.reviewSha256 === prior.reviewSha256);
  });
}
async function gatePromptSnapshot(run, p) {
  const fs = p.fs ?? { lstatSync, realpathSync, readFileSync };
  const paths = new Set((await changedFiles(run, p, true)).filter(path => path.endsWith('.prompt.md')));
  if (run.gate?.kind === 'ask-code') {
    const pr1 = prOf(run, run.gate.area);
    if (pr1) {
      const base = run.promptReturn ? await git(p,run.root,'merge-base',pr1.branch,`refs/remotes/origin/${run.baseBranch}`) : run.baseSha;
      for (const path of (await rawGit(p, run.root, 'diff', '--name-only', '-z', `${base}...${pr1.branch}`)).split('\0')) if (path.endsWith('.prompt.md')) paths.add(path);
      if (run.promptReturn) for (const path of run.storyApproval?.prompts ?? []) paths.add(path);
    }
  }
  const rows = [];
  for (const path of [...paths].sort()) {
    const file = resolve(run.root, path);
    if (!file.startsWith(resolve(run.root) + '/')) throw Error(`Cannot inspect unsafe prompt: ${path}`);
    let stat;
    try { stat = fs.lstatSync(file); } catch (error) { if (error.code === 'ENOENT') continue; throw error; }
    if (!stat.isFile() || fs.realpathSync(file) !== file) throw Error(`Cannot inspect unsafe prompt: ${path}`);
    const text = fs.readFileSync(file, 'utf8');
    rows.push({ path, proseSha256: proseSha256(text), reviewSha256: reviewSha256(text) });
  }
  return rows;
}
const snapshotLines = snapshot => snapshot.length ? snapshot.map(row => `Prompt: ${row.path} ${row.proseSha256}`) : ['Selected prompts: none.'];
async function showGate(run, p) {
  const observedGate=structuredClone(run.gate);
  try {
    const snapshot=await gatePromptSnapshot(run,p);
    const contract=storyApprovalGate(run,run.areas[run.area]) ? await storyContract(run,p) : null;
    const storyPaths=contract!==null ? await storyContractPaths(run,p) : null;
    const storySnapshot=contract!==null ? storyFingerprint({root:run.root,changed:await changedFiles(run,p)}) : null;
    let applied=false;
    commitRun(run,p,latest=>{if(latest.gate&&equalFact(latest.gate,observedGate)){latest.gate.promptSnapshot=snapshot;if(contract!==null){latest.gate.storyContract=contract;latest.gate.storyPaths=storyPaths;latest.gate.storySnapshot=storySnapshot;}applied=true;}});
    return applied ? [...snapshotLines(snapshot),...(contract!==null ? [`Story contract: ${contract}`] : [])] : [];
  } catch (error) {
    commitRun(run,p,latest=>{if(latest.gate&&equalFact(latest.gate,observedGate)){delete latest.gate.promptSnapshot;delete latest.gate.storyContract;}});
    return [`Cannot show selected prompts: ${error.message}. Repair the selection, show the gate again and ask the person again.`];
  }
}
// Validate the complete selection before mutating any prompt or the journal.
async function approveGatePrompts(run, p, snapshot = null) {
  const fs = p.fs ?? { lstatSync, realpathSync, readFileSync, writeFileSync };
  snapshot ??= await gatePromptSnapshot(run, p);
  const paths = snapshot.map(row => row.path);
  const edits = [];
  for (const path of paths) {
    const file = join(run.root, path);
    let stat;
    try { stat = fs.lstatSync(file); } catch (error) { if (error.code === 'ENOENT') continue; throw error; }
    if (!stat.isFile() || fs.realpathSync(file) !== file) throw Error(`Cannot approve unsafe prompt: ${path}`);
    const text = fs.readFileSync(file, 'utf8'), blocks = interfaceBlocks(text);
    if (!blocks.length) continue;
    if (blocks.length !== 1) throw Error(`${path} must have one Runtime interface block.`);
    let iface;
    try { iface = JSON.parse(blocks[0][1]); } catch { throw Error(`${path} has invalid Runtime interface JSON.`); }
    const problems = interfaceSchemaProblems(iface);
    if (problems.length) throw Error(`${path}: ${problems.map(item => `${item.code} ${item.pointer} ${item.rule}`).join('; ')}`);
    const hash = proseSha256(text);
    if (iface.status === 'approved' && iface.prose_sha256 === hash) continue;
    if (!['draft','approved'].includes(iface.status)) throw Error(`${path} has an invalid approval status.`);
    const next = approvePromptText(text);
    if (!next) throw Error(`${path}: add "prose_sha256": "" to the Runtime interface before approval.`);
    edits.push({ path, text, next, proseSha256: hash });
  }
  readPromptApprovals(await promptApprovalContext(run, p), p);
  return edits;
}
async function codeEntryFailure(run,p) {
  const storyAdvice=()=>`The Story or expected contract changed. Finish the Story area and show its gate again: pdd workflow open ${run.number}.`;
  if (await reopenChangedStory(run,p,p.codeEntryContract)) return storyAdvice();
  let dirty=[];
  if (replayEnabled(run)) {
    try { dirty=await unpublishedScenarios(run,p); }
    catch { return 'Cannot verify published scenario bytes. Repair the scenario inventory.'; }
  }
  // Scenario inspection itself awaits Git. A contract change wins over dirty bytes.
  if (await reopenChangedStory(run,p,p.codeEntryContract)) return storyAdvice();
  if (dirty.length) return `Unpublished scenario edits remain: ${dirty.join(', ')}. Publish them in prompt space first.`;
  return null;
}
async function saveGateApproval(run, area, record, edits, p, snapshot = run.gate?.promptSnapshot, deferDecision = false, authority = null) {
  // An id-less legacy gate gets a current identity only; timestamps never authorize reuse.
  if (run.gate && !run.gate.id) { const id=p.randomUUID(); commitRun(run,p,latest=>{if(latest.gate)latest.gate.id??=id;}); }
  const gateId = run.gate?.id ?? p.randomUUID(), gateAt = run.gate?.at;
  const existing = [...run.decisions].reverse().find(decision => decision.gateId === gateId && decision.evidence);
  if (existing && !edits.length && (!record.basis?.headSha || existing.evidence?.basis?.headSha === record.basis.headSha) && (!storyApprovalGate(run,area) || existing.storyContract===run.gate?.storyContract)) { run.approvalRecord = { ...(run.approvalRecord?.gateId === gateId ? run.approvalRecord : {}), gateId, kind: existing.via, area: area.name, at: existing.at, evidence: existing.evidence }; return deferDecision ? {decision:existing,approvalRecord:run.approvalRecord,alreadySaved:true} : existing; }
  const at = p.now(), evidence = { id: p.randomUUID(), route: record.via, actor: approvalActor(p.env), at, words: record.text ?? null,
    prompts: (snapshot ?? edits).map(({path,proseSha256}) => ({path,proseSha256})), ...(record.basis ? { basis: record.basis } : {}) };
  p.inspectProgress?.();
  const fs = p.fs ?? { writeFileSync }, changed = [];
  try {
    for (const edit of edits) { changed.push(edit); fs.writeFileSync(join(run.root, edit.path), edit.next); }
    await recordPromptApproval({ ...await promptApprovalContext(run, p), evidence }, { ...p, afterApprovalLock: authority?.afterLock,
      beforeApprovalCommit: () => { p.inspectProgress?.(); authority?.beforeCommit(); } });
  } catch (error) {
    const left = [];
    for (const edit of changed.reverse()) { try { fs.writeFileSync(join(run.root, edit.path), edit.text); } catch { left.push(edit.path); } }
    throw Error(`${error.message}${left.length ? ` Rollback failed for: ${left.join(', ')}.` : ''}`);
  }
  if (storyApprovalGate(run,area) && await storyContract(run,p)!==run.gate?.storyContract) throw Error('The Story contract changed before its decision. Show the Story gate again.');
  if (area.then==='ask-code' && run.gate?.kind==='ask-code') {
    const changed=await codeEntryFailure(run,p);
    if (changed) throw Error(changed);
  }
  const decision = { gateId, stage: area.name, decision: 'approve', via: record.via, at, gateAt, ...(record.text !== undefined ? {text: record.text} : {}), ...(storyApprovalGate(run,area) ? {storyContract:run.gate?.storyContract,storyPaths:run.gate?.storyPaths,storyCoverage:{fingerprint:run.gate?.storySnapshot,prompts:(snapshot??[]).map(row=>row.path),evidenceId:evidence.id}} : {}), evidence };
  const approvalRecord = { gateId, kind: record.via, area: area.name, at, ...(record.via === 'chat' ? { userMessage: record.text, userMessageAt: record.at, sessionId: record.sessionId } : {}), evidence };
  if (deferDecision) return {decision,approvalRecord};
  await p.validateCodeSource?.();
  commitRun(run,p,latest=>{latest.decisions.push(decision);latest.approvalRecord=approvalRecord;});
  return decision;
}
async function approveRunCommand({ ref, cwd, said: approvalWords, draft = false, through, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  if (typeof draft !== 'boolean') return fail('Draft publication must be a Boolean.');
  if (through !== undefined && !THROUGH.includes(through)) return fail(throughWords);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run, area = run.areas[run.area], label = `${run.repo}#${run.number} "${oneLine(run.issue.title)}"`;
  if (explicitlyStopped(run, p)) return fail('Automatic continuation refused: Autopilot is stopped. Start Autopilot and retry.');
  const ownershipFailure = await continuationOwnership(run, cwd, p);
  if (ownershipFailure) return fail(ownershipFailure);
  if (run.draft !== undefined && typeof run.draft !== 'boolean') return fail('The saved draft publication policy must be a Boolean.');
  const strengthening = draft && run.draft !== true;
  const draftStage = run.areas.slice(run.area).find(item => item.gate === 'pr');
  const draftEligibility = latest => latest.gate && latest.gate.area === area.name
    && area.steps.every(step => latest.done[step]) && draftStage && !prOf(latest, draftStage.name)
    && (latest.gate.kind === 'approve' && area.gate === 'approve' || latest.gate.kind === 'approve-pr' && area.before === 'approve');
  if (strengthening && !draftEligibility(run)) return fail('Draft publication can be requested only at a ready unpublished approval gate. The run and existing PRs are unchanged.');
  if (area.then==='ask-code' && !run.promptReturn) p.codeEntryContract=await storyContract(run,p);
  if (await reopenChangedStory(run,p)) return fail(`The Story or expected contract changed. Finish the Story area and show its gate again: pdd workflow open ${run.number}.`);
  const selectedQuestion=run.question,selectedGate=run.gate,selectedArea=run.area;
  const askCode = area.then === 'ask-code', beforePr = run.gate?.kind === 'approve-pr';
  if (ended(run) && !(askCode && run.gate?.kind === 'ask-code')) return fail(`The run for ${run.repo}#${run.number} is ${run.state}. There is nothing to approve.`);
  if (area.gate === 'pr' && !askCode && !beforePr) return fail(`Nothing to approve for #${run.number}: the ${area.name} area ends with ${prLabel(run, area)}, which pdd opens after its last step.${prOf(run, area.name) ? ` ${prLabel(run, area) === 'the PR' ? 'PR' : prLabel(run, area)}: ${prOf(run, area.name).url}` : ''}`);
  const approvalRecorded=protectProgress(run,p,{approval:true});
  const invocationAt=p.now();
  const missing = missingHome(run, p.env);
  if (missing) return fail(missing);
  const agent = isAgentSession(p.env), pane = chatPane(run, p.env), viaChat = agent || !p.isTTY || Boolean(pane);
  let policy;
  try { policy = readApprovalPolicy({root: run.sourceRoot}, p); }
  catch (error) { return fail(error.message); }
  if (policy.strictApprovals && (approvalWords !== undefined || viaChat)) return fail(`Only the person can approve in a terminal. Run pdd workflow approve ${run.number} in a normal terminal.`);
  // Normal runs (#2962): the Story approval saves the Story fingerprint and the code-or-stop choice of the card.
  const normal = !policy.strictApprovals && !Object.hasOwn(run, 'automaticOrigin');
  const storyGate = run.gate?.kind === 'approve' && run.area >= 0 && run.area === storyGateIndex(run);
  if (through !== undefined && (!normal || !(storyGate || beforePr && run.gate?.storyChanges?.length))) return fail('--through applies only at the Story gate or the prompt PR gate of a normal run, not in strict mode or an automatic run. Nothing changed.');
  if (approvalWords === undefined && viaChat) return fail(approvalGuide(run, p.pdd));
  try { if (approvalWords !== undefined) approvalWords = await readSaidWords(approvalWords, p); p.inspectProgress(); } catch (error) { return fail(error.message); }
  if (approvalWords !== undefined && (!run.gate || area.steps.some(step => !run.done[step]))) return fail('The gate is not ready. Finish its steps and run done first.');
  if(!beforePr){const adoptedFailure=await adoptionFailure(run,p);if(adoptedFailure)return fail(adoptedFailure);}
  if (askCode && run.gate?.kind === 'ask-code') {
    const review = await normalCodeReview(run, area, p);
    if (review) return review;
    const pr1 = prOf(run, area.name);
    if (!pr1) return fail('PR 1 is unavailable; no approval was recorded.');
    let state;
    try { state = await (p.readPrStatus ?? readWorkflowPrStatus)({cwd:run.root,url:pr1.url}, p.commandPorts); }
    catch { return fail('PR 1 state is unavailable; no approval was recorded.'); }
    if (!['open','merged'].includes(state.state)) {
      const retry = (run.decisions ?? []).some(decision => decision.gateId === run.gate.id && decision.evidence) ? approvalRetry(run, p.pdd) : approvalGuide(run, p.pdd);
      return fail(`PR 1 is ${state.state}, so pdd cannot tell where the code branch should start. No approval was recorded. Check PR 1, then ${retry}`);
    }
  }
  if (askCode && run.gate?.kind === 'ask-code' && replayEnabled(run)) {
    try { const dirty = await unpublishedScenarios(run,p); if (dirty.length) return fail(`Unpublished scenario edits remain: ${dirty.join(', ')}. Publish them in prompt space first.`); }
    catch { return fail('Cannot verify published scenario bytes. Repair the scenario inventory.'); }
  }
  // A normal run's Story approval covers the card that the gate showed: a later Story or test change shows it again.
  if (normal && run.gate?.storySnapshot && (storyGate || beforePr)) {
    const late = fingerprintChanges(run.gate.storySnapshot, storyFingerprint({ root: run.root, changed: await changedFiles(run, p) }));
    if (late.length) return fail(`The Story or its test cases changed after pdd showed the card (${late.slice(0, 3).join('; ')}). Run done again for the step you changed, show the new card and ask the person again.`);
  }
  let edits = [];
  try {
    if (run.gate && area.steps.every(step => run.done[step])) {
      const current = await gatePromptSnapshot(run, p);
      if (approvalWords !== undefined && !samePromptReview(current, run.gate.promptSnapshot)) return fail('The selected prompts changed or this gate has no saved review. Show the gate again with done and ask the person again.');
      if (area.gate === 'approve') {
        const contract = await storyContract(run,p);
        if (approvalWords !== undefined && contract !== run.gate.storyContract) return fail('The Story or scenario contract changed or has no saved review. Show the gate again with done and ask the person again.');
        if (approvalWords === undefined) {
          p.say(`Story contract: ${contract}`);
          commitRun(run,p,latest=>{latest.gate.storyContract=contract;});
        }
      }
      edits = await approveGatePrompts(run, p);
      if (approvalWords === undefined) { p.say(snapshotLines(current).join('\n')); commitRun(run,p,latest=>{latest.gate.promptSnapshot=current;}); }
    } else {
      readPromptApprovals(await promptApprovalContext(run, p), p);
      // A terminal may confirm an incomplete legacy gate. Bind its current
      // contract before that confirmation; --said still requires a shown gate.
      if (approvalWords === undefined && area.gate === 'approve' && run.gate) {
        const contract = await storyContract(run,p), paths = await storyContractPaths(run,p);
        p.say(`Story contract: ${contract}`);
        commitRun(run,p,latest=>{latest.gate.storyContract=contract;latest.gate.storyPaths=paths;});
      }
    }
  } catch (error) { return fail(error.message); }
  let carried = [], synchronized = false;
  if (askCode && run.gate?.kind === 'ask-code' && approvalWords === undefined && !edits.length) {
    const carry = await syncPr1(run, p);
    if (carry.failed) return fail(carry.failed);
    carried.push(...carry.lines);
    synchronized = true;
  }
  if (!run.gate) {
    const why = `The ${area.name} area of #${run.number} is not at its gate yet (not done: ${area.steps.filter(step => !run.done[step]).join(', ')}).`;
    if (viaChat) return fail(`${why} Finish the steps and run done first.`);
    if (!await confirm(p, `${why} Approve anyway? (y/N) `)) return fail('Not approved. The run is unchanged.');
  }
  let record;
  if (approvalWords !== undefined) record = { via: 'said', text: approvalWords };
  else {
    if (!await confirm(p, beforePr ? `Approve the ${area.name} area and all selected draft prompts and open ${prLabel(run, area) === 'the PR' ? 'the PR' : prLabel(run, area)} for ${label}? (y/N) `
      : askCode ? `Make the code PR now and approve the code gate and all selected draft prompts for ${label}? PR 1: ${prOf(run, area.name)?.url} (y/N) ` : `Approve the ${area.name} area and all selected draft prompts for ${label}? (y/N) `)) return fail([...carried, 'Not approved. The run is unchanged.'].join('\n'));
    record = { via: 'terminal' };
  }
  let releaseAdmission;
  const admitApproval = async () => {
    if (!Object.hasOwn(run, 'automaticOrigin')) return null;
    try {
      const context = await gitContext(run.sourceRoot, p);
      if (!context) return 'Automatic continuation refused: admission lock is unavailable.';
      const dir = join(context.commonDir, 'pdd');
      mkdirSync(dir, { recursive: true });
      releaseAdmission = acquireRunLock(dir, 'autopilot-admission.lock');
      if (explicitlyStopped(run, p)) return 'Automatic continuation refused: Autopilot is stopped. Start Autopilot and retry.';
      return null;
    } catch { return 'Automatic continuation refused: admission lock is unavailable.'; }
  };
  try {
  const admissionFailure = await admitApproval();
  if (admissionFailure) return fail(admissionFailure);
  p.inspectProgress();
  let approvalSnapshot = run.gate?.promptSnapshot;
  try {
    if (area.gate === 'approve' && run.gate && (!run.gate.storyContract || await storyContract(run,p) !== run.gate.storyContract)) return fail('The Story or scenario contract changed. Show the gate again with done and ask the person again.');
    if (approvalSnapshot) {
      const current = await gatePromptSnapshot(run, p);
      if (!samePromptReview(current, approvalSnapshot)) return fail('The selected prompts changed. Show the gate again and ask the person again.');
      approvalSnapshot = current;
      edits = await approveGatePrompts(run, p, current);
    }
  } catch (error) { return fail(`Cannot inspect selected prompts: ${error.message}. Show the gate again and ask the person again.`); }
  if (askCode && run.gate?.kind === 'ask-code') {
    const review = await normalCodeReview(run, area, p);
    if (review) return review;
  }
  let reviewedStory = null;
  if (normal && run.gate?.storySnapshot && (storyGate || beforePr)) {
    reviewedStory = storyFingerprint({root:run.root,changed:await changedFiles(run,p)});
    if (fingerprintChanges(run.gate.storySnapshot,reviewedStory).length)
      return fail('The Story or its expected cases changed during approval. Show the new card with done and ask again.');
  }
  if (askCode && !beforePr) {
    const changed=await codeEntryFailure(run,p);
    if (changed) return fail(changed);
  }
  let saved, pendingCodeApproval;
  try {
    if (askCode && !beforePr && run.gate) pendingCodeApproval=await saveGateApproval(run,area,record,edits,p,approvalSnapshot,true);
    else if (beforePr || !askCode) saved=await saveGateApproval(run,area,record,edits,p,approvalSnapshot);
  }
  catch (error) { return fail(`Approval failed: ${error.message}`); }
  if (strengthening) {
    try {
      commitRun(run,p,latest=>{
        if (latest.draft !== undefined && typeof latest.draft !== 'boolean') throw Error('The saved draft publication policy must be a Boolean.');
        if (!draftEligibility(latest)) throw Error('The draft publication gate is no longer ready and unpublished.');
        latest.draft = true;
      });
    } catch (error) { return fail(`Draft publication policy was not saved: ${error.message}`); }
  }
  carried.push(...edits.map(edit => `Approved ${edit.path} ${edit.proseSha256}`));
  if (askCode && run.gate?.kind === 'ask-code') {
    const carry = synchronized ? { drafts: await pr1Drafts(run, p), lines: await draftDescription(run, prOf(run, area.name), await pr1Drafts(run, p), p) } : await syncPr1(run, p);
    if (carry.failed) return fail(carry.failed);
    if (carry.drafts.length) return fail(approveFirst(run, carry.drafts));
    carried.push(...carry.lines);
  } else if (approvalWords !== undefined && askArea(run) && prOf(run, askArea(run).name)) carried.push(...await draftDescription(run, prOf(run, askArea(run).name), await pr1Drafts(run, p), p));
  const said = record.text !== undefined ? ` The person wrote: "${oneLine(record.text).slice(0, 300)}".` : '';
  if (beforePr) {
    // Try before PR 1 (#13): the approval opens the area's PR; the code question comes after it.
    const refreshed = normal && run.storyApproval && storyGateIndex(run) >= 0 ? { gateId: saved?.gateId ?? selectedGate?.id ?? null, evidenceId: saved?.evidence?.id ?? null, at: invocationAt,
      fingerprint: reviewedStory ?? storyFingerprint({ root: run.root, changed: await changedFiles(run, p) }), prompts: (approvalSnapshot ?? []).map(row => row.path) } : null;
    if (refreshed) {
      commitRun(run, p, latest => {
        latest.storyApproval = refreshed;
        if (through !== undefined) latest.through = through;
        latest.gate = { ...latest.gate, id: p.randomUUID(), storySnapshot: refreshed.fingerprint };
        delete latest.gate.storyChanges;
        if (equalFact(latest.question, selectedQuestion)) latest.question = null;
      });
      approvalRecorded();
      return normalPromptGate(run, area, 'check', p, [...carried, `Recorded the Story approval.${said}`], await worktreeContents(run, p), packageRoot);
    }
    const lines = [], failed = await publishAreaPr(run, area, p, lines, approvalRetry(run, p.pdd));
    if (failed) return failed;
    const at = invocationAt, url = prOf(run, area.name).url;
    const observedQuestion=selectedQuestion;
    commitRun(run,p,latest=>{
      if(latest.area===selectedArea&&sameGate(latest.gate,selectedGate)){latest.state='waiting';latest.gate=askCode?{id:p.randomUUID(),area:area.name,at,kind:'ask-code'}:null;}
      if(equalFact(latest.question,observedQuestion))latest.question=null;
    });
    approvalRecorded();
    const shownGate = run.gate ? await showGate(run, p) : [];
    const head = [...carried, ...shownGate, `Approved the ${area.name} area of ${label}.${said} pdd opened ${prLabel(run, area) === 'the PR' ? 'the PR' : prLabel(run, area)}.`, ...lines];
    if (!askCode) return done([...head, `PR: ${url}`, 'pdd never merges.'].join('\n'));
    if (approvalWords !== undefined) return done([...head, `PR 1: ${url}`, `Stopped at PR 1. ${codeLater(run)}`].join('\n'));
    if (viaChat) return done([...head, ...await askCodeLines(run, area, p)].join('\n'));
    // A draft prompt in PR 1: pdd does not offer the code PR, and says how to approve the prompt first.
    const drafts = await pr1Drafts(run, p);
    if (drafts.length) {
      const notice = await deliverRequest(run, `pdd opened PR 1: ${url}. The person approved it in their terminal. PR 1 has draft prompts, so the code PR waits. Tell them exactly: "PR 1 is open: ${url}. ${approveFirst(run, drafts)}" Then stop.
${approvalGuide(run)}`, p, true);
      return done([...head, `PR 1: ${url}`, approveFirst(run, drafts), ...noticeWarnings(notice)].join('\n'));
    }
    releaseAdmission?.(); releaseAdmission = null;
    if (!await confirm(p, `Make the code PR now and approve the code gate and all selected draft prompts for ${label}? PR 1: ${url} (y/N) `)) {
      const notice = await deliverRequest(run, `pdd opened PR 1: ${url}. The person approved it in their terminal and stops here for now. Tell them exactly: "PR 1 is open: ${url}. ${codeLater(run)}" Then stop.
${approvalGuide(run)}`, p, true);
      return done([...head, `PR 1: ${url}`, `Stopped at PR 1. ${codeLater(run)}`, ...noticeWarnings(notice)].join('\n'));
    }
  }
  if (beforePr && askCode && !releaseAdmission) {
    const admissionFailure = await admitApproval();
    if (admissionFailure) return fail(admissionFailure);
  }
  if (beforePr && askCode) saved = null;
  if (!saved && !askCode) {
    try { saved = await saveGateApproval(run, area, record, edits, p); }
    catch (error) { return fail(`Approval failed: ${error.message}`); }
  }
  let based = '';
  if (askCode) {
    const adoptedFailure=await adoptionFailure(run,p);if(adoptedFailure)return fail(adoptedFailure);
    // Reached at the code gate, or right after PR 1 opened when the terminal said yes to the code PR.
    p.say('Making the code branch…');
    try { based = await codeBranch(run, area, p, async () => {
      const changed=await codeEntryFailure(run,p);
      if (changed) throw Object.assign(Error(changed),{code:'workflow_code_contract_changed'});
      if (pendingCodeApproval) {
        const {decision,approvalRecord,alreadySaved}=pendingCodeApproval;
        await p.validateCodeSource?.();
        if (!alreadySaved) commitRun(run,p,latest=>{latest.decisions.push(decision);latest.approvalRecord=approvalRecord;});
        saved=decision;
      } else saved=await saveGateApproval(run,area,record,edits,p,approvalSnapshot);
    }); }
    catch (error) {
    if(error?.code==='workflow_progress_refused')throw error;
    if(error?.code==='workflow_code_contract_changed')return fail(error.message);
    return fail(`${oneLine(error.message)} Check PR 1, then ${approvalRetry(run, p.pdd)}`); }
  }
  if (askCode) carried.push(...await draftDescription(run, prOf(run, area.name), await pr1Drafts(run, p), p));
  const now = invocationAt;
  const storyRecord = normal && storyGate ? { gateId: saved?.gateId ?? selectedGate?.id ?? null, evidenceId: saved?.evidence?.id ?? null, at: invocationAt,
    fingerprint: reviewedStory ?? storyFingerprint({ root: run.root, changed: await changedFiles(run, p) }), prompts: (approvalSnapshot ?? []).map(row => row.path) } : null;
  const branch=run.branch,prBase=run.prBase,observedQuestion=selectedQuestion,areaIndex=selectedArea;
  commitRun(run,p,latest=>{
    if(storyRecord&&latest.area===areaIndex){latest.storyApproval=storyRecord;if(through!==undefined)latest.through=through;}
    if(askCode){latest.branch=branch;latest.prBase=prBase;}
    if(equalFact(latest.question,observedQuestion))latest.question=null;
    if(latest.area===areaIndex){if(askCode)latest.metricsOrigin={...(latest.metricsOrigin ?? {origin:'unknown'}),requiredOutcome:'code'};if(sameGate(latest.gate,selectedGate))latest.gate=null;for (const chat of latest.chats ?? []) if (chat.area === latest.areas[areaIndex].name) chat.endedAt ??= p.now();latest.area=areaIndex+1;latest.state=latest.question?'waiting':'running';latest.doneAt=null;}
  });
  approvalRecorded();
  const next = run.areas[run.area];
  const finalNotices = requestSnapshot(run, p).pendingRequests?.filter(entry => entry.kind === 'notice' && entry.area === area.name && entry.area !== next.name).map(entry => finalNotice(entry, false, 'warning: ')) ?? [];
  let chat;
  try { chat = await startNextChat(run, p, packageRoot); }
  catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail(`${carried.map(line => `${line}\n`).join('')}Approved the ${area.name} area of ${label}.${said} The ${next.name} chat startup was not confirmed (${failureReason(error)}). Start it: pdd workflow open ${run.number}\n${[...failureDetails(error), ...finalNotices].join("\n")}`); }
  const cleanup = await cleanupRunChats(run, p);
  return done([...cleanup.warnings, ...carried, ...finalNotices, `Approved the ${area.name} area of ${label}.${said}${based}`,
    `Started area ${run.area + 1} of ${run.areas.length}: ${next.name} (${next.steps.join(', ')}) in a new chat: Herdr session pdd, tab "${chat.label}".`,
    `Watch it: pdd workflow open ${run.number}`, ...(agent ? ['This chat\'s work is done. Stop here.'] : [])].join('\n'));
  } finally { releaseAdmission?.(); }
}

// A run that waits for the interpreter: no question to a person, its slot can be yielded, and Autopilot wakes it later.
const runtimeWaiting = run => run.state === 'paused' && Boolean(run.runtimeWait);
// A wake (a delivered request) or recorded progress ends the wait; the run goes on where it stopped.
function endRuntimeWait(run) {
  if (!run.runtimeWait) return;
  delete run.runtimeWait;
  if (run.state === 'paused') run.state = run.gate || openQuestion(run) ? 'waiting' : 'running';
}
// The latest pdd test result of the run decides whether it may wait for the interpreter: only a no-verdict
// AI-service, busy, network or unknown result waits. A failed check or a file rule is this issue's own work.
const RUNTIME_PARK_REFUSALS = {
  issue: 'pdd test failed an expectation, names a file rule, or a step took longer than the server time limit. This is this issue\'s own work, not an interpreter outage: find the cause and fix it (RUNBOOK §11). For a step time limit, make the step smaller, for example split 30 moves into 3 steps of 10. Nothing was parked.',
  access: 'pdd test reports a sign-in, access or interpreter address problem. It is not an interpreter outage, and waiting does not fix it: a person must fix the sign-in. Run gh auth status (and check PDD_RUNTIME_URL), then follow the access alert rule. Nothing was parked.',
  passed: 'The latest pdd test passed; nothing waits for the interpreter. Nothing was parked.',
};
// The text of an Autopilot interpreter wake starts with its park time, so one park is woken at most once.
export const runtimeWakeTag = at => `Interpreter wake for the park at ${new Date(at).toISOString()}.`;
const RUNTIME_WAKE_TAG = /^Interpreter wake for the park at [^ ]+\./;

// Record an automatic stop without releasing or waking its worker.
async function parkAutomaticRunCommand({ reason, runtime = false, step, blocker, until, route, cwd }, ports) {
  const p = deps(ports), run = await runForWorktree(cwd, p);
  if (!run) return fail('Park requires the existing run worktree.');
  const text = String(reason ?? '').trim();
  if (!text) return fail('Give the actual stop reason with --reason.');
  if (!run.automaticOrigin) return fail('Park requires an automatic run.');
  if (ended(run)) return fail('An ended run cannot be parked.');
  if (explicitlyStopped(run, p)) return fail('Autopilot is stopped.');
  const ownership = await continuationOwnership(run, cwd, p);
  if (ownership) return fail(ownership);
  const area = run.areas[run.area];
  if (route !== undefined && (!/^[a-z][a-z0-9-]*$/.test(route) || runtime || blocker !== undefined)) return fail('Use a route kind without --interpreter or --blocker.');
  if (step !== undefined && ((route === undefined && !['check', 'verify', 'formal'].includes(step)) || !area.steps.includes(step))) return fail('Name a check, verify or formal validation step in the current area. Nothing was parked.');
  let routeWait = null;
  let blockedOn = null;
  if (route !== undefined) {
    const fix = until ?? (route === 'prompt-reentry' ? '#2897' : `capability:route-${route}`);
    if (!/^(?:#[1-9][0-9]*|capability:[a-z][a-z0-9-]*|commit:[a-f0-9]{7,40})$/.test(fix)) return fail('Name an installed capability, issue fix or commit for the route.');
    const target = step ?? area.steps.find(name => !run.done?.[name]) ?? area.name;
    const previous = run.routeWait;
    routeWait = {kind: route, step: target, question: text, at: p.now(), until: fix};
    if (previous && ['kind', 'step', 'question', 'until'].every(key => previous[key] === routeWait[key])) routeWait.at = previous.at;
    blockedOn = {kind: 'pdd-route', until: fix};
  }
  if (blocker !== undefined) {
    const kinds = ['person', 'pdd', 'dependency', 'account', 'github', 'ci', 'review'];
    const valid = kinds.includes(blocker) && !runtime
      && (blocker === 'dependency' ? /^[1-9][0-9]*$/.test(String(until)) && Number.isSafeInteger(Number(until))
        : blocker === 'pdd' ? /^(?:#[1-9][0-9]*|capability:[a-z][a-z0-9-]*|commit:[a-f0-9]{7,40}|\d+\.\d+\.\d+(?:-[\w.-]+)?)$/.test(until ?? '')
        : ['account', 'github'].includes(blocker) ? Number.isFinite(Date.parse(until))
        : until === undefined);
    if (blocker === 'person' && !run.gate && !openQuestion(run)) return fail('A person blocker requires a pending question or gate. Nothing was parked.');
    if (!valid) return fail('Name a blocker and its clearing value: dependency issue, pdd release, or account/github reset time.');
    blockedOn = {kind: blocker, until: until ?? null};
  } else if (until !== undefined && route === undefined) return fail('--until requires --blocker or --route.');
  const stuckCause = classifyStuckCause(text, runtime);
  let retry = null;
  if (!blockedOn && stuckCause === 'environment' && !run.repairLimit && !run.integrationLimit) {
    const target = step;
    if (!target) return fail('Name the failed validation with --step STEP. Nothing was parked.');
    const previous = run.environmentRetry;
    const attempts = previous?.area === run.area && previous.step === target ? previous.attempts : 0;
    retry = { at: p.now(), reason: text, step: target, area: run.area, attempts, nextAt: attempts < ENVIRONMENT_BACKOFF.length ? p.now() + ENVIRONMENT_BACKOFF[attempts] : null };
  }
  let wait = null;
  if (runtime) {
    // A result read that fails is an outcome that is not known: never a sign that no check ran.
    let check = null, cause;
    try { check = readOwnResults(run, p).find(result => result.kind === 'pdd test') ?? null; cause = check ? savedCheckCause(check.batch, { env: p.env }) : 'none'; }
    catch { cause = 'unknown'; }
    if (RUNTIME_PARK_REFUSALS[cause]) return fail(RUNTIME_PARK_REFUSALS[cause]);
    wait = { at: p.now(), reason: clip(oneLine(text), 300), batch: check?.batch ?? null, cause };
  }
  const selectedArea=run.area, selectedGate=structuredClone(run.gate ?? null), selectedState=run.state, selectedOrigin=structuredClone(run.automaticOrigin);
  protectProgress(run,p,{approval:true});
  const waitLine = wait && `Automatic run waits for the interpreter: ${wait.reason}. Ask no person. End your turn now; the coordinator may yield this slot. Autopilot checks the interpreter at each tick without AI and wakes this run when the interpreter is back. Then run pdd test --read${wait.batch ? ` ${wait.batch}` : ''} first and resend only a check that surely gave no verdict.`;
  if (!blocker && !runtime && run.state === 'stuck' && run.parkReason === text && (!retry || retry.step === run.environmentRetry?.step)) return done('Automatic run is already parked.');
  if (wait && runtimeWaiting(run) && run.runtimeWait.batch === wait.batch) return done(waitLine);
  commitRun(run,p,latest=>{
    if (latest.area !== selectedArea || !sameGate(latest.gate,selectedGate) || latest.state !== selectedState || !equalFact(latest.automaticOrigin,selectedOrigin) || explicitlyStopped(latest,p))
      throw Object.assign(Error('The run or Autopilot changed; look again.'),{code:'workflow_progress_refused'});
    latest.stuckCause = stuckCause;
    if (routeWait) {
      latest.routeWait = routeWait;
      const reports = latest.routeReports ??= [];
      if (!reports.some(row => sameFact(row, routeWait))) reports.push(routeWait);
    } else delete latest.routeWait;
    if (retry) latest.environmentRetry = retry;
    if (!blockedOn) delete latest.blockedOn;
    if (blockedOn) { latest.state='paused'; latest.blockedOn=blockedOn; latest.parkReason=text; delete latest.runtimeWait; }
    else if (wait) { latest.state='paused'; latest.runtimeWait=wait; }
    else { latest.state='stuck'; latest.parkReason=text; delete latest.runtimeWait; }
    if (latest.parking) replaceParkingBlocker(latest, blockerFor(latest));
  });
  return done(wait ? waitLine : 'Automatic run parked: '+text);
}
export const parkAutomaticRun = saveGuard(parkAutomaticRunCommand);

// The agent asks the person in the middle of a step: status shows the question until the next done or the answer.
async function askPersonCommand({ text, cwd }, ports) {
  const p = deps(ports);
  const run = await runForWorktree(cwd, p);
  if (!run) return fail('pdd workflow ask works only in a run worktree. cd to the worktree that pdd made for this run.');
  if (ended(run)) return done(stoppedRunMessage(run));
  protectProgress(run,p);
  const question = String(text ?? '').trim().slice(0, 500);
  if (!question) return fail('Write the question after pdd workflow ask.');
  const asked={text:question,at:p.now(),area:run.areas[run.area].name};
  commitRun(run,p,latest=>{latest.question=asked;if(!latest.gate)latest.state='waiting';});
  return done([`pdd shows the person: waiting for you: ${question.split('\n')[0]}`,
    'Now ask the question in a plain chat message (not a question dialog) and end your turn.',
    `The person answers in this chat, or from their shell with: pdd workflow changes ${run.number} "answer". Then go on with the step and run done as usual.`].join('\n'));
}

// Journal claims cover synchronous local reads/writes only; readiness and Herdr never hold one.
const activeDeliveries = new Set();
const monotonicMs = () => Number(process.hrtime.bigint() / 1_000_000n);
const delay = ms => new Promise(resolve => setTimeout(resolve, ms));
const deliveryHost = p => typeof p.hostname === 'function' ? p.hostname() : p.hostname ?? hostname();
function ownerAlive(pid, p) {
  try {
    if (p.processIdentity) return p.processIdentity(pid)?.alive;
    process.kill(pid, 0); return true;
  } catch (error) { return error.code === 'ESRCH' ? false : null; }
}
function deliveryClaim(path, p) {
  const fs = { ...nativeDeliveryFiles, ...p.deliveryFiles }, token = (p.deliveryToken ?? randomUUID)();
  const owner = { pid: p.ownerPid ?? process.pid, hostname: deliveryHost(p), token };
  if (!Number.isInteger(owner.pid) || owner.pid < 1 || typeof owner.hostname !== 'string' || !owner.hostname || !/^[A-Za-z0-9_-]+$/.test(token)) throw Error('Cannot identify this sender');
  try { fs.mkdirSync(path, { mode: 0o700 }); } catch (error) { if (error.code !== 'EEXIST') throw error; }
  const busy = () => Object.assign(Error('Another command is saving a request'), { code: 'delivery_busy' });
  if (!fs.lstatSync(path).isDirectory()) throw busy();
  const leaf = join(path, `owner-${token}.json`), temporary = `${path}.${token}.tmp`, bytes = JSON.stringify(owner);
  try { fs.writeFileSync(temporary, bytes, { flag: 'wx', mode: 0o600 }); fs.renameSync(temporary, leaf); }
  finally { try { fs.unlinkSync(temporary); } catch { /* Published or never created. */ } }
  const release = () => { try { if (fs.readFileSync(leaf, 'utf8') === bytes) fs.unlinkSync(leaf); } catch { /* Only remove our observed record. */ } };
  try {
    for (const name of fs.readdirSync(path)) {
      if (name === `owner-${token}.json` || !/^owner-[A-Za-z0-9_-]+\.json$/.test(name)) continue;
      const otherPath = join(path, name); let text, other;
      try { text = fs.readFileSync(otherPath, 'utf8'); other = JSON.parse(text); }
      catch (error) { if (error.code === 'ENOENT') continue; throw busy(); }
      if (!Number.isInteger(other.pid) || other.pid < 1 || !other.hostname || name !== `owner-${other.token}.json` ||
        other.hostname !== owner.hostname || ownerAlive(other.pid, p) !== false) throw busy();
      try { if (fs.readFileSync(otherPath, 'utf8') === text) fs.unlinkSync(otherPath); }
      catch (error) { if (error.code !== 'ENOENT') throw error; }
    }
    return release;
  } catch (error) { release(); throw error; }
}
// Pure snapshot reader shared by visibility and the claimed mutation path.
function readDeliveryJournal(run, p) {
  const fs = { ...nativeDeliveryFiles, ...p.deliveryFiles };
  let journal;
  try { journal = JSON.parse(fs.readFileSync(join(run.runDir, 'delivery-journal.json'), 'utf8')); }
  catch (error) { if (error.code !== 'ENOENT') throw error; return { requests: [] }; }
  if (!journal || !Array.isArray(journal.requests) || journal.requests.some(entry => !entry || typeof entry.id !== 'string' || !entry.id ||
    typeof entry.text !== 'string' || !['pending', 'uncertain', 'delivered', 'superseded'].includes(entry.state) || !['answer', 'change', 'notice'].includes(entry.kind) ||
    typeof entry.area !== 'string' || !entry.area || typeof entry.paneId !== 'string' || !entry.paneId || !Number.isFinite(entry.at) ||
    entry.inFlight !== undefined && typeof entry.inFlight !== 'boolean') || new Set(journal.requests.map(entry => entry.id)).size !== journal.requests.length) throw Error('Malformed delivery journal');
  return journal;
}
// Queued replies are durable readiness, not permission to reserve a worker slot.
function parkedReplyEntries(run, p) {
  if (!run.parking) return [];
  return readDeliveryJournal(run, p).requests.filter(entry => entry.key?.startsWith(`park-reply:${run.parking.at}:`)
    && entry.area === run.areas[run.area]?.name && entry.state === 'pending' && !entry.inFlight
    && equalFact(entry.question, run.question ?? null) && equalFact(entry.gate, run.gate ?? null));
}
export function hasParkedReply(run, ports = {}) {
  try { return parkedReplyEntries(run, ports).length > 0; } catch { return false; }
}
const uptakeQuote = value => "'" + value.replaceAll("'", "'\"'\"'") + "'";
const uptakeCommand = (id, p) => `${p.pdd ?? pddFor(p, PACKAGE_ROOT)} ${PUBLIC_COMMAND_ROUTES.find(route => route.id === 'workflow.request-uptake').prefix.join(' ')} ${uptakeQuote(id)} --summary ${uptakeQuote('what I changed')}`;
const deliveryTime = (value, p = {}) => typeof value !== 'number' || !Number.isFinite(value) || Math.abs(value) > 8640000000000000 ? 'unknown' : new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit', hourCycle: 'h23', ...(p.timeZone ? { timeZone: p.timeZone } : {}) }).format(new Date(value));
const uptakeReceipt = (entry, p) => `Request ${entry.id}: delivered at ${deliveryTime(entry.deliveredAt, p)}; ${entry.ackedAt == null ? 'not yet acknowledged by the agent' : `acknowledged at ${deliveryTime(entry.ackedAt, p)}: ${entry.ackSummary ?? ''}`}.`;
// An undelivered pdd notice keeps the approval's success and adds its delivery result as warning lines.
const noticeWarnings = result => result.exitCode === 0 ? [] : result.message.split('\n').map(line => `warning: ${line}`);
// A status row of one journal entry; a pdd notice says so, and its text line shows only the notice's first line.
const requestRow = ({ id, text, area, paneId, kind }) => ({ id, text, area, paneId, ...(kind === 'notice' ? { kind } : {}) });
const shownText = entry => entry.kind === 'notice' ? `pdd notice: ${oneLine(entry.text.split('\n')[0]).slice(0, 160)}` : entry.text;
function requestSnapshot(run, p) {
  try {
    const entries = readDeliveryJournal(run, p).requests;
    return { requests: entries.filter(entry => entry.kind === 'change' && entry.state === 'delivered')
      .map(entry => ({ id: entry.id, text: entry.text, area: entry.area, deliveredAt: entry.deliveredAt ?? null, ackedAt: entry.ackedAt ?? null, ackSummary: entry.ackSummary ?? null })),
      pendingRequests: entries.filter(entry => !entry.inFlight && entry.state === 'pending').map(entry => ({ ...requestRow(entry), ...(typeof entry.reason === 'string' && entry.reason ? { reason: entry.reason } : {}) })),
      uncertainRequests: entries.filter(entry => !entry.inFlight && entry.state === 'uncertain').map(requestRow),
      inFlightRequests: entries.filter(entry => entry.inFlight).map(requestRow) };
  } catch { return { requests: null, inFlightRequests: null, pendingRequests: null, uncertainRequests: null, requestWarning: 'Change-request visibility unavailable: could not read the delivery journal. Check the run folder.' }; }
}
const protectedRequestAdvice = entry => `Request ${entry.id}: ${shownText(entry)}. Original area ${entry.area}, pane ${entry.paneId}. Wait for the current send to finish before checking the original chat or typing anything. If it remains stuck after waiting, pdd will not automatically clear or resend protected ownership. First verify the original chat before manually supplying anything absent.`;
const finalNotice = (entry, ended = false, framingPrefix = '') => `${framingPrefix}Request ${entry.id}: pdd notice was not sent and later changes will not send it.${ended ? " The run ended." : ""} Original ${entry.area} chat, pane ${entry.paneId}:\n${entry.text}\n${framingPrefix}Last delivery reason: ${entry.reason ?? "unknown"}.`;
function requestLines(snapshot, { openOnly = false, agent = false, ended = false, currentArea, p = {} } = {}) {
  if (snapshot.requestWarning) return [snapshot.requestWarning];
  return [...snapshot.requests.filter(entry => (!ended || !openOnly) && (!openOnly || entry.ackedAt == null)).map(entry =>
    `${uptakeReceipt(entry, p)} Area ${entry.area}: ${entry.text}${agent ? `\nTell the person about this outstanding request. After actually addressing this request, run: ${uptakeCommand(entry.id, p)}` : ""}`), ...snapshot.pendingRequests.map(entry => entry.kind === 'notice' && (ended || currentArea && entry.area !== currentArea) ? finalNotice(entry, ended) : `Request ${entry.id}: ${ended ? 'pending, not sent; run ended. Original' : 'pending, saved for the original'} ${entry.area} chat, pane ${entry.paneId}: ${shownText(entry)}${entry.reason ? ` Not sent: ${entry.reason}.` : ''}`), ...snapshot.uncertainRequests.map(entry => `Request ${entry.id}: uncertain, may already be in the original ${entry.area} chat, pane ${entry.paneId}: ${shownText(entry)}. Check that original chat.`), ...snapshot.inFlightRequests.map(entry => agent ? `Request ${entry.id}: delivery in progress. Tell the person about this outstanding request.` : protectedRequestAdvice(entry))];
}
function doneWithRequests(result, run, p) {
  if (result.exitCode !== 0) return result;
  const snapshot = requestSnapshot(run, p);
  // Completion warnings concern delivered changes; other custody states remain
  // visible in status without directing an agent to inspect its own chat.
  const lines = requestLines({ ...snapshot, pendingRequests: [], uncertainRequests: [], inFlightRequests: [] }, { openOnly: true, agent: true, p });
  return lines.length ? { ...result, message: `${result.message}\nwarning: ${lines.join('\n').split('\n').join('\nwarning: ')}` } : result;
}
export async function acknowledgeRequest({ requestId, summary, cwd }, ports) {
  const p = deps(ports), hint = `Use ${uptakeCommand(typeof requestId === 'string' ? requestId : 'REQUEST_ID', p)}.`;
  if (typeof requestId !== 'string' || !requestId.trim() || typeof summary !== 'string' || !oneLine(summary)) return fail(`Provide a request id and a short summary. ${hint}`);
  const run = await runForWorktree(cwd, p);
  if (!run || !['running', 'waiting'].includes(run.state)) return fail(`Acknowledgement requires an active run worktree. ${hint}`);
  try {
    const entry = await deliveryJournal(run, p, journal => {
      const entry = journal.requests.find(entry => entry.id === requestId);
      if (!entry || entry.kind !== 'change' || entry.state !== 'delivered' || entry.inFlight) throw Error('Request is not a delivered change in this run');
      if (entry.ackedAt == null) { entry.ackedAt = p.now(); entry.ackSummary = oneLine(summary).slice(0, 500); }
      return { ...entry };
    }, { recover: false });
    return done(`Agent uptake recorded. ${uptakeReceipt(entry, p)}`);
  } catch (error) { return fail(`Could not acknowledge request ${requestId}: ${oneLine(error.message).slice(0, 300)}. ${hint}`); }
}

async function deliveryJournal(run, p, action, { recover = true } = {}) {
  const fs = { ...nativeDeliveryFiles, ...p.deliveryFiles }, path = join(run.runDir, 'delivery-journal.json');
  const elapsed = p.journalElapsedNow ?? monotonicMs, began = elapsed(); let release;
  while (!release) {
    try { release = deliveryClaim(join(run.runDir, '.delivery-journal.lock'), p); }
    catch (error) {
      const left = 250 - Math.max(0, elapsed() - began);
      if (error.code !== 'delivery_busy' || left <= 0) throw error;
      await (p.journalSleep ?? delay)(Math.min(10, left));
    }
  }
  try {
    const saved = readRun(run.runDir);
    if (saved && runIdentity(saved) !== runIdentity(run)) throw Error('The selected workflow run was replaced');
    const journal = readDeliveryJournal(run, p);
    const before = JSON.stringify(journal);
    if (recover) for (const entry of journal.requests) if (entry.inFlight) {
      const owner = entry.owner;
      const verifiable = owner && Number.isInteger(owner.pid) && owner.pid > 0 && typeof owner.hostname === 'string' && owner.hostname && typeof owner.token === 'string' && owner.token;
      const abandoned = verifiable && owner.hostname === deliveryHost(p) &&
        (owner.pid === (p.ownerPid ?? process.pid) ? !activeDeliveries.has(owner.token) : ownerAlive(owner.pid, p) === false);
      if (abandoned) { entry.state = 'uncertain'; entry.code = 'acknowledgement_unknown'; delete entry.inFlight; delete entry.owner; }
    }
    const result = action(journal);
    if (!recover && JSON.stringify(journal) === before) return result;
    const temporary = `${path}.${(p.deliveryToken ?? randomUUID)()}.tmp`;
    try { fs.writeFileSync(temporary, JSON.stringify(journal, null, 2) + '\n', { flag: 'wx', mode: 0o600 }); fs.renameSync(temporary, path); }
    finally { try { fs.unlinkSync(temporary); } catch { /* Published or never created. */ } }
    return result;
  } finally { release(); }
}

// Shared lexical admission for a person's explicit continuation request. Trust belongs to the caller.
export function isRetryRequest(text) {
  const value = String(text ?? '').trim().replace(/\s+/g, ' ');
  // Negative continuation instructions win, even after an otherwise direct request.
  if (/\b(?:do\s+not|don['’]t|never|must\s+not|should\s+not|cannot|can['’]t|not|no)\b[^.;!?]*\b(?:retr(?:y(?:ing)?|ies)|resum(?:e|ing|ption)|try\s+again|continu(?:e|ing|ation)|proceed|restart)\b/i.test(value)) return false;
  if (/\b(?:stop|hold|wait)\b/i.test(value)
    || /\b(?:retr(?:y(?:ing)?|ies)|resum(?:e|ing|ption)|try\s+again|continu(?:e|ing|ation)|proceed|restart)\b[^.;!?]*\b(?:blocked|disabled|unsafe|forbidden|prohibited|not)\b/i.test(value)) return false;
  // A repaired-machine preface may precede the command. Arbitrary diagnostic or log
  // prefixes cannot turn a quoted/reported command into the person's instruction.
  // Whitespace also admits the saved one-line form of a multiline repair request.
  const request = value.replace(/^(?:the\s+)?(?:machine|host|environment|server|disk|tool)\s+(?:(?:is|was|has\s+been)\s+)?(?:fixed|repaired|healthy|ready|available|restored)(?:\s+now)?[.;!,:\s]+/i, '');
  const command = request.split(/[.;!]/, 1)[0].trim();
  // Admit commands with known continuation targets, not noun phrases such as
  // "retry budget" or status reports such as "resume remains unsafe".
  return /^(?:please\s+|(?:can|could|would)\s+you\s+(?:please\s+)?)?(?:retry|resume|try\s+again)(?:\s+(?:(?:(?:the|this|that)\s+)?(?:(?:failed|original|retained|stuck|paused)\s+)?(?:validation(?:\s+step)?|step|run|work|check|tests?|build|verify|formal)|it))?(?:\s+(?:again|now|please))?(?:\s+(?:from\s+(?:the\s+)?retained\s+evidence|using\s+(?:the|its)\s+original\s+command|after\s+(?:the\s+)?(?:machine|host|environment)\s+repair))?\s*\??$/i.test(command);
}
const isPersonRetry = (run, text) => run.state === 'stuck' && isRetryRequest(text);
async function personRetryRefusal(run, text, p, savedRetry = false) {
  if (!savedRetry && !isPersonRetry(run, text)) return null;
  if (run.repairLimit || run.integrationLimit) return 'The repair or integration limit requires the existing cancel and new-run route.';
  if (explicitlyStopped(run, p)) return 'Automatic continuation refused: Autopilot is stopped.';
  return await continuationOwnership(run, run.root, p);
}
const isEnvironmentWake = text => String(text).startsWith('Environment validation wake for ');
function currentEnvironmentWake(run, text, p) {
  const retry = environmentRecovery(run);
  return Boolean(retry && String(text).startsWith(environmentWakeTag(retry)) && retry.attempts < ENVIRONMENT_BACKOFF.length && p.now() >= retry.nextAt);
}
async function environmentWakeAllowed(run, text, p) {
  if (!isEnvironmentWake(text)) return null;
  if (!currentEnvironmentWake(run, text, p) || explicitlyStopped(run, p) || await continuationOwnership(run, run.root, p)) return false;
  try { return await (p.environmentHealthy ?? environmentHealthy)({ env: p.env, reason: environmentRecovery(run).reason }) === true; } catch { return false; }
}
export async function changeRun({ ref, text, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.packageRoot = packageRoot; const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  // An interpreter wake reaches the run only while it still waits for that park: a second copy sends nothing.
  const wake = RUNTIME_WAKE_TAG.exec(String(text ?? '').trim())?.[0];
  if (wake && !(runtimeWaiting(found.run) && wake === runtimeWakeTag(found.run.runtimeWait.at)))
    return done(`Run #${found.run.number} does not wait for the interpreter park that this wake names: it was already woken, or it parked again. Nothing was sent.`);
  if (await environmentWakeAllowed(found.run, text, p) === false) return done('Environment validation retry is not due, healthy or current. Nothing was sent.');
  const retryRefusal = await personRetryRefusal(found.run, text, p);
  if (retryRefusal) return fail(retryRefusal);
  if (found.run.parking?.phase === 'releasing') return fail('This parked run is releasing its claim. Wait for release to finish.');
  if (!p.queueOnly && found.run.parking?.phase === 'parked') {
    return lockedMutation({ref, cwd}, p, async (input, ports) => {
      const current = await resolveRun(ref, {cwd}, ports), run = current.run;
      if (!run || runIdentity(run) !== runIdentity(found.run) || run.parking?.phase !== 'parked'
        || run.parking.at !== found.run.parking.at) return fail('The parked run changed. Look again before replying.');
      const key = `park-reply:${run.parking.at}:${createHash('sha256').update(oneLine(text)).digest('hex')}`;
      return deliverRequest(run, text, {...ports, queueOnly: true, requestKey: key});
    });
  }
  return deliverRequest(found.run, text, p);
}

// Journal custody and FIFO delivery to the current area chat: the person's answer or change request, or (notice) a pdd
// notice with its exact text. A notice has no answer/change effect and no retry command; the next delivery sends it first.
async function deliverRequest(run, text, p, notice = false) {
  const selectedIdentity=runIdentity(run);
  if (ended(run)) return fail(`The run for ${run.repo}#${run.number} is ${run.state}.`);
  const retryRequested = !notice && isPersonRetry(run, text);
  const request = notice ? String(text) : oneLine(text), answer = !notice && !isEnvironmentWake(request) && !retryRequested && Boolean(openQuestion(run)), kind = notice ? 'notice' : answer ? 'answer' : 'change';
  if (!request.trim()) return fail('Write the change request after the issue number.');
  if (!notice && !answer && run.gate && looksLikeApproval(request)) return { exitCode: 2, message: `This looks like an approval. Tell your agent you approve this gate, or run pdd workflow approve ${run.number} in a terminal.
Nothing was sent to the chat.` };
  const area = run.areas[run.area], chat = currentChat(run);
  if (!chat) return fail(`The ${area.name} area has no chat${notice ? ', so pdd did not send its notice' : ''}. Start it: pdd workflow open ${run.number}`);
  const what = notice ? 'the pdd notice' : 'your request', What = notice ? 'The pdd notice' : 'Your request';
  const latest = () => readRun(run.runDir), matches = entry => entry.area === area.name && entry.paneId === chat.paneId;
  const targetCurrent = saved => saved && runIdentity(saved)===selectedIdentity && !ended(saved) && saved.areas[saved.area]?.name === area.name && currentChat(saved)?.paneId === chat.paneId
    && (!p.deliveryGuard || p.deliveryGuard(saved));
  const retry = notice ? `It goes to the chat first with your next pdd workflow changes ${run.number}.` : `Retry: pdd workflow changes ${run.number} '${request.replace(/'/g, `'\\''`)}'`;
  const kept = `${What} is kept. Wait briefly or open it: pdd workflow open ${run.number}. ${retry}`;
  const warning = `An earlier request is uncertain and may already be in the chat. Check the original chat: pdd workflow open ${run.number}; type it there if absent. pdd will not automatically resend it.`;
  const uncertain = () => fail(`${What} is uncertain and may already be in the chat. Check the original chat: pdd workflow open ${run.number}; type it there if absent. pdd will not automatically resend it.`);
  const progress = entry => fail(`Delivery to the original ${entry.area} chat is in progress or needs inspection. ${accepted.id !== entry.id ? `${What} is saved pending. ` : ''}${protectedRequestAdvice(entry)} Open it: pdd workflow open ${run.number}.`);
  const already = () => done(`${What} was already delivered to the ${area.name} chat.${accepted.kind === 'change' ? `\n${uptakeReceipt(accepted, p)}` : ''}`);
  const failure = sent => {
    if (sent.uncertain) return uncertain();
    if (sent.code === 'chat_target_changed') return fail(`The original ${area.name} chat target changed. ${kept}`);
    if (sent.code === 'chat_still_starting') return fail(`The ${area.name} chat is still starting. ${kept}`);
    if (sent.code === 'agent_blocked' || sent.code === 'agent_dialog') return fail(`The ${area.name} chat did not get ${what}: ${sent.reason ?? 'the chat shows a dialog'}. pdd sent nothing and did not answer the dialog. Answer it in the chat yourself, then retry. ${kept}`);
    if (sent.code === 'pane_unreadable') return fail(`The ${area.name} chat did not get ${what}: ${sent.reason}. pdd sends nothing when it cannot see the chat. ${kept}`);
    if (sent.code === 'agent_not_found') return fail(`The ${area.name} chat is not running. ${kept}`);
    return fail(`pdd could not send the text to the ${area.name} chat (${sent.code}). ${kept}`);
  };
  let accepted;
  try {
    accepted = await deliveryJournal(run, p, journal => {
      if (notice && !targetCurrent(latest())) throw Error('The run changed before notice delivery');
      let entry = journal.requests.find(item => p.requestKey ? item.key === p.requestKey : matches(item) && item.kind === kind && item.text === request && !['delivered', 'superseded'].includes(item.state));
      if (entry && p.requestKey && entry.state === 'pending' && !entry.inFlight && entry.area === area.name) entry.paneId = chat.paneId;
      if (!entry) { entry = { ...(p.requestKey ? {key: p.requestKey} : {}), id: (p.deliveryToken ?? randomUUID)(), text: request, kind, area: area.name, paneId: chat.paneId, state: 'pending', at: p.now(), ...(retryRequested ? { personRetry: true } : {}), question: notice ? null : run.question ?? null, gate: notice ? null : run.gate ?? null }; journal.requests.push(entry); }
      return { ...entry };
    });
  } catch (error) { return fail(error.code === 'delivery_busy' ? `Another command is saving a request. Wait briefly, then retry. ${retry}` : `Could not save ${what}; it was not sent. Check the run folder and retry. ${retry}`); }
  if (p.queueOnly) return done(kept);
  const owner = { pid: p.ownerPid ?? process.pid, hostname: deliveryHost(p), token: (p.deliveryToken ?? randomUUID)() };
  activeDeliveries.add(owner.token);
  try {
    const snapshot = await deliveryJournal(run, p, journal => ({ accepted: { ...journal.requests.find(item => item.id === accepted.id) }, queue: journal.requests.filter(item => matches(item) && !['delivered', 'superseded'].includes(item.state)).map(item => ({ ...item })) }));
    accepted = snapshot.accepted; const queue = snapshot.queue;
    if (accepted.state === 'delivered') return already();
    let warnings = queue.some(entry => entry.state === 'uncertain'), sentAccepted = false;
    if (accepted.state === 'uncertain') return uncertain();
    if (accepted.inFlight) return progress(accepted);
    const deferredEnvironment = new Set();
    for (const entry of queue) {
      if (entry.state === 'uncertain') continue;
      if (entry.inFlight) return progress(entry);
      run = latest(); if (!targetCurrent(run)) return failure({ code: 'chat_target_changed' });
      if (isEnvironmentWake(entry.text) && await environmentWakeAllowed(run, entry.text, p) === false) {
        const observed = await deliveryJournal(run, p, journal => {
          const saved = journal.requests.find(item => item.id === entry.id);
          if (saved?.state === 'pending' && !saved.inFlight && !currentEnvironmentWake(latest(), saved.text, p)) {
            saved.state = 'superseded'; saved.reason = 'The environment park changed before this wake was sent.';
          }
          return { ...saved };
        });
        if (observed.inFlight) return progress(observed);
        deferredEnvironment.add(entry.id);
        continue;
      }
      const personRetry = entry.kind === 'change' && isRetryRequest(entry.text) && (entry.personRetry || run.state === 'stuck');
      const retryRefusal = personRetry && await personRetryRefusal(run, entry.text, p, true);
      if (retryRefusal) return fail(retryRefusal);
      const retryTarget = environmentRecovery(run)?.step;
      const retryInstruction = personRetry ? ` Resume only ${retryTarget ? `the failed validation step ${retryTarget}` : 'the failed step identified in the retained evidence'}, using its original command. Preserve completed work, gates, questions, branch and claim. Never replay an external operation with an unknown outcome.` : '';
      const message = entry.kind === 'notice' ? entry.text : entry.kind === 'answer' ? `${ANSWER_PREFIX}: ${entry.text} Go on with the step.`
        : validSavedAutomaticOrigin(run) ? `Submitted request: ${entry.text}${retryInstruction} Address it in this chat and record uptake. This request is not an approval. Read the owner handoff and applicable automatic overlay before deciding what follows. Current package CLI: ${pddCommand(p.packageRoot ?? PACKAGE_ROOT)}. Run the repository full suite through ${pddCommand(p.packageRoot ?? PACKAGE_ROOT)} workflow suite --command COMMAND and wait for the queue result. Test-slot waiting is not stuck.\nRequest ${entry.id}. After addressing it, record agent uptake with a short note:\n${uptakeCommand(entry.id, { ...p, pdd: pddCommand(p.packageRoot ?? PACKAGE_ROOT) })}` : `${CHANGE_PREFIX}: ${entry.text} Revise in this chat, run done again for the step you changed, then show the result and ask again.\nRequest ${entry.id}. After addressing it, record agent uptake with a short note:\n${uptakeCommand(entry.id, p)}`;
      let custodyFailed = false, claimed = false;
      const transport = herdrCommand(p), guardedHerdr = async args => {
        try { return await transport(args); }
        catch (error) {
          if (args[0] === 'agent' && args[1] === 'prompt' && ['agent_not_found', 'agent_blocked'].includes(error.code)) {
            try { await deliveryJournal(run, p, journal => { const saved = journal.requests.find(item => item.id === entry.id); if (saved?.owner?.token === owner.token) { delete saved.inFlight; delete saved.owner; saved.code = error.code; } }); claimed = false; }
            catch { custodyFailed = true; }
          }
          throw error;
        }
      };
      const sent = await sendToChat(chat, message, { ...p, herdr: guardedHerdr, beforeSubmit: async () => {
        if (custodyFailed) return false;
        if (personRetry && await personRetryRefusal(latest(), entry.text, p, true)) return false;
        if (entry.kind !== 'notice' && await environmentWakeAllowed(latest(), entry.text, p) === false) return false;
        if (p.beforeDeliverySubmit && !await p.beforeDeliverySubmit()) return false;
        try { return await deliveryJournal(run, p, journal => {
          const current = latest();
          if (!targetCurrent(current) || isEnvironmentWake(entry.text) && !currentEnvironmentWake(current, entry.text, p)) return false;
          const saved = journal.requests.find(item => item.id === entry.id);
          if (!saved || saved.state !== 'pending' || saved.inFlight) return false;
          const first = journal.requests.find(item => matches(item) && item.state === 'pending' && (!deferredEnvironment.has(item.id) || item.inFlight));
          if (first?.id !== saved.id) return false;
          saved.inFlight = true; saved.owner = owner; claimed = true; return true;
        }); } catch { custodyFailed = true; return false; }
      } });
      if (custodyFailed) return fail(`Could not save submission intent; ${what} was not sent. ${kept}`);
      let observed;
      try {
        observed = await deliveryJournal(run, p, journal => {
          const saved = journal.requests.find(item => item.id === entry.id);
          if (!saved) throw Error('Saved request unavailable');
          // A pending request keeps the reason of its latest unsent delivery (a dialog or an unread screen) for status.
          const keepReason = () => { const reason = sent.reason ?? (sent.code === 'agent_blocked' ? 'the chat shows a question dialog' : null); if (reason) saved.reason = reason; else delete saved.reason; };
          if (!claimed || saved.owner?.token !== owner.token) { if (!claimed && !sent.ok && saved.state === 'pending' && !saved.inFlight) keepReason(); return { ...saved }; }
          delete saved.inFlight; delete saved.owner;
          if (!sent.ok) { saved.state = sent.uncertain ? 'uncertain' : 'pending'; saved.code = sent.code; keepReason(); return { ...saved }; }
          const now = p.now(); saved.state = 'delivered'; saved.deliveredAt = now; delete saved.code; delete saved.reason;
          // A pdd notice changes no workflow fact.
          if (entry.kind !== 'notice') commitRun(run,p,current=>{
          current.changes.push({ stage: entry.area, round: current.changes.filter(change => change.stage === entry.area).length + 1, text: entry.text, at: now, ...(entry.kind === 'answer' ? { answer: true } : {}) });
          if (targetCurrent(current)) {
            endRuntimeWait(current);
            const retry = environmentRecovery(current);
            if (retry && entry.text.startsWith(environmentWakeTag(retry))) {
              current.environmentRetry = { ...retry, attempts: retry.attempts + 1, nextAt: null, deliveredAt: now };
              current.state = current.gate || openQuestion(current) ? 'waiting' : 'running';
              delete current.parkReason;
            }
            if (personRetry && current.state === 'stuck' && !current.repairLimit && !current.integrationLimit) {
              current.state = current.gate || openQuestion(current) ? 'waiting' : 'running';
              delete current.parkReason;
            }
            if (!personRetry && !isEnvironmentWake(entry.text) && equalFact(current.question,entry.question))current.question=null;
            if(entry.kind==='answer'){if(!current.gate&&!current.question)current.state='running';}
            else if(!personRetry&&!entry.text.startsWith('Environment validation wake for ')&&current.gate&&equalFact(current.gate,entry.gate)){current.gate.id=p.randomUUID();current.gate.at=now;delete current.gate.promptSnapshot;}
          }
          }); return {...saved};
        });
      } catch { return fail('Could not save the submission acknowledgement. Check the original chat before retrying; delivery may be uncertain.'); }
      if (!claimed && observed.state === 'delivered') { if (entry.id === accepted.id) { accepted = observed; return already(); } continue; }
      if (!claimed && observed.inFlight) return progress(observed);
      if (observed.state === 'uncertain') { if (entry.id === accepted.id) return uncertain(); warnings = true; continue; }
      if (claimed && sent.ok && entry.id === accepted.id) { sentAccepted = true; accepted = observed; }
      if (!sent.ok) { const result = failure(sent); return warnings ? { ...result, message: `${result.message}\n${warning}` } : result; }
    }
    if (!sentAccepted) {
      const saved = await deliveryJournal(run, p, journal => ({ ...journal.requests.find(item => item.id === accepted.id) }));
      if (saved.state === 'delivered') { accepted = saved; return already(); }
      if (saved.inFlight) return progress(saved);
      if (saved.state === 'uncertain') return uncertain();
      return failure({ code: 'chat_target_changed' });
    }
    if (notice) return done(`Sent the pdd notice to the ${area.name} chat of #${run.number}.${warnings ? `\n${warning}` : ''}`);
    return done((answer ? `Sent your answer to the ${area.name} chat of #${run.number}. The agent goes on with the step.`
      : `Sent your change request to the ${area.name} chat of #${run.number}.${run.gate ? ' The gate stays open.' : ''}`) + (!answer ? `\n${uptakeReceipt(accepted, p)}` : '') + (warnings ? `\n${warning}` : ''));
  } catch (error) { return fail(`Could not update the saved request. Wait briefly, then retry; check the original chat (${error.code ?? 'journal unavailable'}).`); }
  finally { activeDeliveries.delete(owner.token); }
}

function cleanupLines(run) {
  const closed = (run.chats ?? []).filter(chat => Number.isFinite(chat.closed?.confirmedAt)).map(chat => chat.area);
  const pending = (run.chats ?? []).filter(chat => chat.closed && !Number.isFinite(chat.closed.confirmedAt)).map(chat => chat.area);
  return [...(pending.length ? [`Close pending: ${pending.join(', ')}`] : []), ...(closed.length ? [`Closed chats: ${closed.join(', ')}. Reopen one: pdd workflow open ${run.number} ${closed[0]}`] : []),
    ...(run.cleanupKept ?? []).map(item => `Kept open: ${item.area} (${item.reason})`)];
}
function stoppedRunMessage(run) {
  return `Run ${run.runId} for #${run.number} is ${run.cancelled?.state ?? run.state}${run.replacedBy ? ` by run ${run.replacedBy}` : ''}. Stop working on it. The retained worktree is ${run.root}.${run.cancelled?.state === 'handed-over' ? ` ${run.cancelled.reason}` : ''}`;
}
function endedChatHelp(run) {
  const lines = [stoppedRunMessage(run)];
  if (run.cancelled?.state === 'handed-over') return fail(lines.join('\n'));
  for (const chat of run.chats ?? []) {
    if (chat.closed?.screen) lines.push(`Read ${chat.area}: ${chat.closed.screen}`);
    if (!validSessionId(chat.session?.id)) continue;
    const agent = chat.agent ?? run.agent, variable = homeVariable(agent);
    const command = agent === 'codex' ? `codex resume ${shell(chat.session.id)}` : agent === 'claude' ? `claude --resume ${shell(chat.session.id)}` : null;
    if (command) lines.push(`Resume ${chat.area} yourself: cd ${shell(run.root)} && ${variable && chat.configDir ? `${variable}=${shell(chat.configDir)} ` : ''}${command}`);
  }
  return done(lines.join('\n'));
}
async function cleanupRunChats(run, p, options = {}) {
  const snapshot = structuredClone(run), savedTerminals = new Map((run.chats ?? []).map(chat => [chat.paneId, chat.terminalId]));
  for (const chat of finishedChats(snapshot)) chat.endedAt ??= finishedAt(snapshot,chat);
  const result = await closeFinishedChats(snapshot, {...p, ...options, checkpoint: async (chat, layout) => {
    commitMaintenance(run, p, latest => {
      if (chat) {
        const target = latest.chats?.find(item => sameChat(item,chat) && item.terminalId === savedTerminals.get(chat.paneId));
        if (!target || !options.force && !finishedChats(latest).includes(target)) throw Object.assign(Error('Cleanup target changed'), {code:'workflow_progress_refused'});
        if (chat.closed?.reason === 'absent' && target.closed)
          chat.closed = {...target.closed, confirmedAt: chat.closed.confirmedAt};
        Object.assign(target, structuredClone(chat));
        savedTerminals.set(chat.paneId, chat.terminalId);
      }
      if (layout) latest.layout = structuredClone(layout);
    });
  }});
  if (!options.dryRun) {
    const shellKept = run.layout?.phase !== 'closed' && !result.kept.some(item => item.area === 'run shell')
      ? (run.cleanupKept ?? []).filter(item => item.area === 'run shell') : [];
    const nextKept = [...(options.onlyChat ? (run.cleanupKept ?? []).filter(item => item.area !== options.onlyChat.area && item.area !== 'run shell') : []), ...shellKept, ...result.kept];
    if (!equalFact(run.cleanupKept ?? [],nextKept) || snapshot.chats?.some(chat => chat.endedAt !== run.chats?.find(item => sameChat(item,chat))?.endedAt))
      commitMaintenance(run, p, latest => {
        latest.cleanupKept = nextKept;
        for (const chat of finishedChats(latest)) chat.endedAt ??= snapshot.chats?.find(item => sameChat(item,chat))?.endedAt;
      });
  }
  return result;
}
// The target's origin alone is not authority to close it. Read the current
// source coordinator, independently of the selected run snapshot.
function currentParkingOwner(run, p, {allowOlder = false} = {}) {
  try {
    const root = realpathSync(run.sourceRoot), id = createHash('sha256').update(root).digest('hex').slice(0, 20);
    const folder = p.autopilotStateRoot ?? join(p.env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
    const state = JSON.parse(readFileSync(p.autopilotStateFile ?? join(folder, `${id}.json`), 'utf8'));
    return state.enabled === true && samePath(state.cwd, root) && state.repo?.toLowerCase() === run.repo?.toLowerCase()
      && state.machine === run.automaticOrigin?.machine
      && (allowOlder || state.coordinatorId === run.automaticOrigin?.coordinatorId) ? state : null;
  } catch {return null;}
}
// Called under the run lock. A remote recovery is retryable if the local save failed.
async function recoverParkingOwner(run, owner, p) {
  if (run.automaticOrigin.coordinatorId === owner.coordinatorId) return true;
  const origin = structuredClone(run.automaticOrigin);
  const recovery = await (p.recoverCoordinatorClaim ?? recoverCoordinatorClaim)({cwd: run.sourceRoot,
    repository: run.repo, claim: {...origin.claim, issue: run.issue.url, coordinatorId: origin.coordinatorId, machine: origin.machine},
    coordinatorId: owner.coordinatorId, machine: owner.machine, at: new Date(p.now()).toISOString()}, p);
  if (recovery.state !== 'recovered') {
    await chatContinuationOwnership(run, p, {releaseUnowned:true});
    return false;
  }
  commitMaintenance(run, p, latest => {
    if (!sameFact(latest.automaticOrigin, origin) || ended(latest) || currentParkingOwner(latest, p, {allowOlder:true})?.coordinatorId !== owner.coordinatorId)
      throw Object.assign(Error('Coordinator custody changed'), {code:'workflow_progress_refused'});
    latest.automaticOrigin = {...latest.automaticOrigin, coordinatorId: owner.coordinatorId};
  });
  return recovery;
}

export const recoverAutomaticRunOwner = saveGuard((args, ports) => lockedMutation(args, ports, async (input, ports) => {
  const p = deps(ports), found = await resolveRun(input.ref, {cwd:input.cwd}, p), run = found.run;
  const skip = () => ({...done(''), recovery:'skipped'});
  if (!run || ended(run) || !validSavedAutomaticOrigin(run) || !samePath(run.sourceRoot,input.cwd)) return skip();
  const owner = currentParkingOwner(run,p,{allowOlder:true});
  if (!owner || owner.coordinatorId !== input.coordinatorId || owner.machine !== input.machine) return skip();
  if (input.releaseUnowned) {
    await chatContinuationOwnership(run, p, {releaseUnowned: true, claimObservation:input.claimObservation ?? null,
      releaseReason:input.releaseReason === 'expired' ? 'expired' : 'lost'});
    const latest = readRun(run.runDir) ?? run;
    return {...done(''), recovery: ended(latest) ? latest.claimRelease?.state === 'pending' ? 'pending' : 'released' : 'skipped'};
  }
  if (run.automaticOrigin.coordinatorId === owner.coordinatorId) return skip();
  const result = await recoverParkingOwner(run,owner,p);
  return result ? {...done(''),recovery:'recovered',claim:result.claim} : skip();
}));
// Admission reuses parking custody. It never starts a worker or releases a claim.
export async function sweepIdleRuns({graceMs = 60_000, need, timeBudgetMs} = {}, ports = {}) {
  const p = deps(ports), runs = allRuns({}, p).sort((a,b) => idleSince(a) - idleSince(b) || a.number - b.number);
  const elapsed = p.elapsedNow ?? (() => Number(process.hrtime.bigint() / 1_000_000n)), began = elapsed();
  let closed = 0, kept = 0, reasonCounts = {};
  for (const run of runs) {
    if (timeBudgetMs !== undefined && elapsed() - began >= timeBudgetMs) break;
    if (need !== undefined) {const usage = await paneUsage(p); if (!usage.budget || usage.panes + need <= usage.budget) break;}
    const owner = currentParkingOwner(run, p, {allowOlder:true});
    if (!owner || !validSavedAutomaticOrigin(run) || readRunOwnership(run.runDir, p) || explicitlyStopped(run, p)
      || ['parked', 'waking', 'releasing'].includes(run.parking?.phase)) continue;
    const blocker = idleParkingBlocker(run, p.now(), graceMs);
    if (!blocker) continue;
    const result = await parkBlockedRun({ref: String(run.number), cwd: run.sourceRoot,
      coordinatorId: owner.coordinatorId, machine: owner.machine,
      blocker, expected: run, idleGraceMs: graceMs}, {...p, progressGuard: undefined});
    const latest = readRun(run.runDir);
    closed += (latest?.runId === run.runId ? latest.chats ?? [] : []).filter(chat => Number.isFinite(chat.closed?.confirmedAt)
      && !(run.chats ?? []).some(old => sameChat(old, chat) && Number.isFinite(old.closed?.confirmedAt))).length;
    if (result.recovery !== 'parked') kept++;
    reasonCounts = mergeReasonCounts(reasonCounts, result.reasonCounts ?? {});
  }
  return {closed, kept, reasonCounts};
}

export async function tidyRuns({dryRun = false, graceMs, need, timeBudgetMs} = {}, ports = {}) {
  const p = deps(ports), runs = allRuns({cancelled:true}, p), kept = [], warnings = [];
  let closed = 0;
  const elapsed = p.elapsedNow ?? (() => Number(process.hrtime.bigint() / 1_000_000n)), began = elapsed();
  const candidates = runs.flatMap(run => {
    const chats = finishedChats(run).filter(chat => !Number.isFinite(chat.closed?.confirmedAt));
    if (chats.length) return chats.map(chat => ({run,chat,at:finishedAt(run,chat)}));
    return ended(run) && run.layout?.workspaceId && run.layout.phase !== 'closed'
      ? [{run,chat:null,at:run.cancelled?.at ?? run.updatedAt ?? run.startedAt}] : [];
  }).sort((a,b) => a.at - b.at);
  for (const [index,{run,chat}] of candidates.entries()) {
    if (timeBudgetMs !== undefined && elapsed()-began >= timeBudgetMs) { kept.push(...candidates.slice(index).map(({chat})=>({area:chat?.area ?? 'run shell',reason:'sweep-time-budget'}))); break; }
    if (readRunOwnership(run.runDir,p)) { kept.push({runId:run.runId,reason:'run-busy'}); continue; }
    let release;
    try {
      release = acquireRunLock(run.runDir);
      const latest = readRun(run.runDir);
      if (!latest || latest.runId !== run.runId) continue;
      const result = await cleanupRunChats(latest, {...p,progressGuard:undefined}, {dryRun, ...(chat ? {onlyChat:chat} : {}),
        ...(graceMs === undefined ? {} : {graceMs}), ...(graceMs === 0 ? {reason:'budget'} : {})});
      closed += result.closed; kept.push(...result.kept); warnings.push(...result.warnings);
      if (need !== undefined) { const usage = await paneUsage(p); if (!usage.budget || usage.panes + need <= usage.budget) break; }
    } catch (error) {
      kept.push({runId:run.runId,reason:error.code ?? 'cleanup-unavailable'});
      if (error.code !== 'run_busy') warnings.push(failureReason(error));
    } finally { release?.(); }
  }
  return {...done([`${dryRun ? 'Would close' : 'Closed'} ${closed} finished chat tabs. Kept ${kept.length}. Retained: ${reasonWords(countReasons(kept))}.`, ...warnings].join('\n')),closed,kept:kept.length,reasonCounts:countReasons(kept)};
}

async function cancelRunCommand({ ref, cwd }, ports, expectedIdentity = null) {
  const p = deps(ports);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  if (expectedIdentity && runIdentity(run) !== expectedIdentity) return fail('The selected workflow run changed. Retry cancellation.');
  const automatic = !ports?.claimReleased && validSavedAutomaticOrigin(run);
  const recordCancellation = at => commitRun(run,p,latest=>{
    latest.state='cancelled';
    latest.cancelled=['replaced','handed-over'].includes(latest.cancelled?.state)?latest.cancelled:{state:'cancelled',at};
    latest.gate=null; delete latest.parking; delete latest.blockedOn; delete latest.parkReason;
    delete latest.runtimeWait; delete latest.routeWait;
    for(const chat of latest.chats ?? []) chat.endedAt ??= at;
    if (automatic) latest.claimRelease = {state:'pending',reason:'cancel',at};
  });
  // The automatic cancellation lock is held by cancelRun. Persist the terminal
  // blocker before an awaited Herdr cleanup lets a publication continue.
  if (automatic) recordCancellation(p.now());
  p.say('Closing the chat tabs in Herdr…');
  const { warnings, kept } = await cleanupRunChats(run, p, {force:true, reason:'cancel'});
  const held = automatic && !kept.length ? await releaseWorkerHeld(readRun(run.runDir) ?? run,p) : null;
  if (!kept.length) removeStaleLoginFiles(run.runDir, { maxAgeMs: 0 });
  if (!automatic) recordCancellation(p.now());
  const cleanupNotes = [];
  if (automatic) {
    const latest = readRun(run.runDir) ?? run;
    const replacement = hasLiveReplacementRun(latest,p);
    const custody = kept.length ? 'Herdr retained one or more chats.' : held || (replacement ? 'A replacement local run owns this issue.' : null);
    if (custody) cleanupNotes.push(`Claim cleanup remains pending: ${custody} Local allocation and GitHub labels stay held.`);
    else {
      let local;
      try { local = await releaseIssueClaim({ cwd: run.sourceRoot, runId: run.runId, issueNumber: run.number }, p.commandPorts); }
      catch { local = {state:'recovery_required',message:'The local issue allocation could not be confirmed.'}; }
      if (local?.state !== 'released') cleanupNotes.push(`Claim cleanup remains pending: ${local?.message ?? 'the local issue allocation is not confirmed released'}`);
      else {
        const after = readRun(run.runDir) ?? latest;
        const afterHeld = await releaseWorkerHeld(after,p);
        if (afterHeld || hasLiveReplacementRun(after,p)) cleanupNotes.push(`Claim cleanup remains pending: ${afterHeld ?? 'a replacement local run owns this issue'}. The GitHub labels stay held.`);
        else try {
          const remote = await (p.releaseParkedClaim ?? releaseParkedClaim)({
            cwd: run.sourceRoot, repository: run.repo,
            claim: { issue: run.issue.url, coordinatorId: run.automaticOrigin.coordinatorId, machine: run.automaticOrigin.machine, ...run.automaticOrigin.claim },
            coordinatorId: run.automaticOrigin.coordinatorId, machine: run.automaticOrigin.machine,
            runId: run.runId, branch: run.branch, reason: 'cancel',
          }, {...p, ...p.commandPorts});
          if (remote?.state === 'released') commitRun(run,p,current=>{if(current.claimRelease?.reason==='cancel')delete current.claimRelease;});
          else cleanupNotes.push('Remote claim cleanup remains pending; both labels were not confirmed absent. The coordinator will retry it on a later tick.');
        } catch { cleanupNotes.push('Remote claim cleanup remains pending; both labels were not confirmed absent. The coordinator will retry it on a later tick.'); }
      }
    }
  }
  return done([...warnings, `Cancelled the run for ${run.repo}#${run.number}.${kept.length ? ` Kept open: ${kept.map(item=>`${item.area} (${item.reason})`).join(', ')}. Retry: pdd workflow tidy, or cancel from another terminal.` : ' Closed its Herdr tabs.'}`,
    ...cleanupNotes, `The worktree stays at ${run.root} (branch ${run.branch}).`].join('\n'));
}

async function releaseWorkerHeld(run, p) {
  if (continuationCheckHeld(run,p)) return 'A suite or interpreter check is running, queued or unavailable.';
  for (const chat of run.chats ?? []) {
    if (Number.isFinite(chat.closed?.confirmedAt)) continue;
    const live = await chatSession(chat, {...p,run});
    if (live.alive) {
      if (!['idle','done'].includes(live.status)) return 'A workflow worker is still active or its status is unknown.';
    } else if (!live.workspaceClosed && !['agent_not_found','pane_not_found','server_not_running'].includes(live.code))
      return 'Herdr cannot confirm that the workflow worker has stopped.';
  }
  return null;
}

export const releaseRunClaim = saveGuard(async ({ ref, cwd, repository, machine, coordinatorId }, ports = {}) => {
  const p = deps(ports);
  const text = String(ref ?? '').trim().replace(/\/$/, '');
  const match = /^#?([1-9][0-9]*)$/.exec(text) ?? /^([^/\s#]+\/[^/\s#]+)#([1-9][0-9]*)$/.exec(text)
    ?? /^https:\/\/github\.com\/([^/]+\/[^/]+)\/issues\/([1-9][0-9]*)$/.exec(text);
  if (!match) return fail(`"${String(ref).slice(0, 80)}" is not an issue number, owner/repo#N or issue URL.`);
  const number = Number(match.at(-1)), refRepo = match.length === 3 ? match[1] : null;
  const found = await resolveRun(String(number), { cwd }, p);
  let run = found.run ?? null, release;
  if ((!run || !Object.hasOwn(run, 'automaticOrigin') || coordinatorId && run.automaticOrigin?.coordinatorId !== coordinatorId) && cwd) {
    const candidates = allRuns({cancelled: true}, p).filter(item => item.number === number
      && (!refRepo || item.repo?.toLowerCase() === refRepo.toLowerCase())
      && (!repository || item.repo?.toLowerCase() === repository.toLowerCase())
      && samePath(item.sourceRoot, cwd)
      && Object.hasOwn(item, 'automaticOrigin')
      && (!coordinatorId || item.automaticOrigin?.coordinatorId === coordinatorId));
    run = candidates.find(item => item.claimRelease?.state === 'pending') ?? candidates.at(-1) ?? run;
  }
  if (run) {
    try { release = acquireRunLock(run.runDir); }
    catch (error) { return fail(error.message); }
    const latest = readRun(run.runDir);
    if (!latest || runIdentity(latest) !== runIdentity(run)) { release?.(); return fail('The selected workflow run changed. Retry the release.'); }
    run = latest;
  }
  try {
    let repo = repository || refRepo || run?.repo;
    if (!repo && cwd) {
      try { repo = githubOriginRepository(await git(p,cwd,'config','--get','remote.origin.url')); } catch { repo = ''; }
    }
    if (!repo) return fail('Could not determine the GitHub repository for this issue.');
    if (refRepo && refRepo.toLowerCase() !== repo.toLowerCase()) return fail(`Issue ${ref} does not belong to ${repo}.`);
    const host = machine || run?.automaticOrigin?.machine || hostname();
    const coord = coordinatorId || run?.automaticOrigin?.coordinatorId || '';
    const localAutomatic = run && Object.hasOwn(run,'automaticOrigin') && validSavedAutomaticOrigin(run)
      && run.automaticOrigin.machine === host;
    if (run && Object.hasOwn(run,'automaticOrigin') && !validSavedAutomaticOrigin(run))
      return fail('The local run has malformed automatic claim ownership; inspect it before release.');
    if (run && hasLiveReplacementRun(run,p)) return fail(`Cannot release ${repo}#${number}: another local run still owns this issue.`);
    let releaseReason = localAutomatic && run.claimRelease?.reason
      && ['cancel','release','expired','lost'].includes(run.claimRelease.reason) ? run.claimRelease.reason : 'release';
    if (localAutomatic) {
      const held = await releaseWorkerHeld(run,p);
      if (held) return fail(`Cannot release ${repo}#${number}: ${held}`);
      const at = p.now();
      commitRun(run,p,latest=>{
        if (!ended(latest)) {
          latest.state='cancelled'; latest.cancelled={state:'cancelled',at}; latest.gate=null;
          delete latest.parking; delete latest.blockedOn; delete latest.parkReason; delete latest.runtimeWait; delete latest.routeWait;
          for(const chat of latest.chats ?? []) chat.endedAt ??= at;
        }
        latest.claimRelease={state:'pending',reason:releaseReason,at:latest.claimRelease?.at ?? at};
      });
      const {kept}=await cleanupRunChats(readRun(run.runDir) ?? run,p,{force:true,reason:'cancel'});
      if (kept.length) return fail(`Cannot release ${repo}#${number}: Herdr retained work. The local allocation and GitHub labels stay held.`);
      const cleaned = readRun(run.runDir) ?? run, heldAfter = await releaseWorkerHeld(cleaned,p);
      if (heldAfter) return fail(`Cannot release ${repo}#${number}: ${heldAfter} The local allocation and GitHub labels stay held.`);
      let local;
      try { local = await releaseIssueClaim({cwd:run.sourceRoot,runId:run.runId,issueNumber:run.number},p.commandPorts); }
      catch { local = {state:'recovery_required',message:'The local issue allocation could not be confirmed released.'}; }
      if (local?.state !== 'released') return fail(`Cannot release ${repo}#${number}: local allocation release is ${local?.state ?? 'unknown'}; ${local?.message ?? 'retry after inspection'}. GitHub labels stay held.`);
      removeStaleLoginFiles(run.runDir,{maxAgeMs:0});
      const afterLocal = readRun(run.runDir) ?? run, heldAfterLocal = await releaseWorkerHeld(afterLocal,p);
      if (heldAfterLocal || hasLiveReplacementRun(afterLocal,p))
        return fail(`Cannot release ${repo}#${number}: ${heldAfterLocal ?? 'another local run now owns this issue'}. GitHub labels stay held.`);
    }
    const issueUrl = `https://github.com/${repo}/issues/${number}`;
    const savedClaim = localAutomatic ? run.automaticOrigin.claim : {};
    const remote = await (p.releaseParkedClaim ?? releaseParkedClaim)({
      cwd, repository: repo,
      claim: { issue: issueUrl, coordinatorId: coord, machine: host, ...savedClaim },
      coordinatorId: coord, machine: host, runId: run?.runId, branch: run?.branch, reason: releaseReason,
    }, {...p, ...p.commandPorts});
    if (remote?.state === 'refused') {
      const owner = remote.machine || 'unknown';
      return fail(owner === 'unknown' ? `Cannot release ${repo}#${number}: claim ownership is unknown.`
        : `Cannot release ${repo}#${number}: ${owner} holds a live claim.`);
    }
    if (remote?.state !== 'released') return fail(`Could not confirm claim cleanup for ${repo}#${number}; retry the release.`);
    const completedRun = localAutomatic ? readRun(run.runDir) ?? run : null;
    if (completedRun?.claimRelease?.reason === releaseReason)
      commitRun(completedRun,p,latest=>{if(latest.claimRelease?.reason===releaseReason)delete latest.claimRelease;});
    return { ...done(`Released the Autopilot claim for ${repo}#${number}.${run ? ` The worktree stays at ${run.root} (branch ${run.branch}).` : ''}`), number, repo, recovery: 'released' };
  } finally { release?.(); }
});

async function refreshPr(run, p) {
  if (!run.pr?.length || run.state === 'cancelled') return;
  const cwd=existsSync(run.root)?run.root:run.sourceRoot,observations=[];
  // #3042: the read of a PR that pdd published with readable facts also gives its description, head and comments
  // (`view`), so that the refresh below of its readable top needs no other read when nothing changed.
  for(const pr of run.pr){const {view,...fields}=await (p.readPrStatus??readWorkflowPrStatus)({cwd,url:pr.url,...(pr.readable?.facts?{view:true}:{})},p.commandPorts);observations.push({url:pr.url,number:pr.number,stage:pr.stage,fields,view});}
  await captureClosedCi({ ...run, pr: observations.map(row => ({ ...run.pr.find(pr => pr.url === row.url), ...row.fields, ...(row.view?.head ? { headSha: row.view.head } : {}) })) }, p);
  const refreshTops=async()=>{
    const observed=new Map(observations.map(observation=>[observation.url,{...observation.fields,view:observation.view}]));
    for(const pr of run.pr) if(pr.readable?.facts && observed.get(pr.url)?.state==='open') for(const line of await refreshReadableTop(run,pr,p,{observed,cwd})) p.say(line);
  };
  const checkedAt=p.now();
  if(!observations.some(observation=>{
    const pr=run.pr.find(pr=>pr.url===observation.url&&pr.number===observation.number&&pr.stage===observation.stage);
    return Object.entries(observation.fields).some(([key,value])=>!equalFact(pr[key],value));
  }))return refreshTops();
  commitRun(run,p,latest=>{
    for(const observation of observations){
      const pr=latest.pr.find(pr=>pr.url===observation.url&&pr.number===observation.number&&pr.stage===observation.stage);
      if(pr)Object.assign(pr,observation.fields);
    }
    const last=latest.pr.at(-1),area=latest.areas.find(item=>item.name===last?.stage);
    if(!last)return;
    latest.prState={state:last.state,ci:last.ci,checkedAt};
    if(latest.state==='cancelled')return;
    if(last.state==='merged'&&area===latest.areas.at(-1))latest.state='completed';
    if(last.state==='merged'&&area?.then==='ask-code'&&latest.gate?.kind==='ask-code'){latest.state='completed';latest.doneAt='PR 1';}
    if (ended(latest)) for (const chat of latest.chats ?? []) chat.endedAt ??= checkedAt;
  });
  await refreshTops();
}

// What Herdr shows for the current chat of a running run or a run at a gate, with one Herdr call: 'blocked' (a question
// dialog), 'working', 'stopped' (the saved chat state is ended: evidence, never "not seen yet"), 'starting' (an unconfirmed
// start after the shared grace), 'unavailable', 'cannot-work' (the agent is alive, but its login or usage limit stops every
// turn; the chat owner's chatHealth result goes into facts.health), 'idle' (an exact idle/done session), or null (still within the grace, or pdd cannot
// tell, and status keeps its words). A lifecycle change is saved into the same chat of the run record.
async function observeRunSessions(run, p) {
  if (run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase)) return;
  for (const chat of [...run.chats ?? []]) {
    if (validSessionId(chat.session?.id) || chat.startUnconfirmed) continue;
    const live = await chatSession(chat, {...p, run});
    const id = validSessionId(live.sessionId) ? live.sessionId :
      (await ownSession({run, chat, since: launchAnchor(chat), ports:p}));
    const found = typeof id === 'string' ? id : id?.kind === 'match' ? id.id : null;
    if (found) commitMaintenance(run, p, latest => {
      const saved = latest.chats?.find(item => sameChat(item,chat));
      if (saved && sameFact(saved, chat)) saved.session = {agent:chat.agent ?? run.agent,id:found};
    });
  }
}
async function chatState(run, p, facts = {}) {
  await observeRunSessions(run, p);
  if (run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase)) return 'unconfirmed';
  if (ended(run)) return null;
  const area = run.areas[run.area], failure = activeChatFailure(run), chat = currentChat(run);
  if (!chat) return failure || !run.gate && !prOf(run, area?.name) ? 'unconfirmed' : null;
  if (!(run.state === 'running' || run.gate || failure)) return null;
  const live = await chatSession(chat, {...p, run});
  if (live.namingError) facts.namingError = live.namingError;
  if (live.workspaceClosed) return 'closed';
  // A never-seen chat after the grace counts as ended only when its own native session shows that the agent ran.
  const own = sessionEvidenceDue(chat, live, p.now()) && !observedSession(chat, chat.agent ?? run.agent) ? await ownSession({ run, chat, since: launchAnchor(chat), ports: p }) : null;
  const observed = observeLifecycle(chat, live, p.now(), chat.agent ?? run.agent, own?.kind === 'match' ? own.id : null);
  // A start fact needs the saved session, an explicit matching live identity when live,
  // and the native session metadata timestamp. Launch and observation times are not starts.
  let metricsStartAt = null;
  const kind=chat.agent ?? run.agent, id=chat.session?.id, since=launchAnchor(chat);
  if (!run.metricsStartRecorded && ['codex','claude'].includes(kind) && validSessionId(id)
      && Number.isFinite(since) && (live.alive ? live.sessionId === id : observed.state === 'ended')) {
    try {
      const folder=expandHome(chat.configDir,p.env ?? process.env);
      const sessions=await (p.findNativeSessions ?? findNativeSessions)({agent:kind,root:run.root,startedAt:since,endedAt:p.now(),sessionId:id},
        {env:p.env ?? process.env,...(folder ? (kind === 'claude' ? {claudeConfigDir:folder} : {codexHome:folder}) : {})});
      if (Array.isArray(sessions) && sessions.length === 1 && sessions[0].id === id && Number.isFinite(sessions[0].startedAt)
          && sessions[0].startedAt >= since && sessions[0].startedAt <= p.now()) metricsStartAt=sessions[0].startedAt;
    } catch { /* Missing evidence leaves coverage unknown. */ }
  }
  // Status saves only positive facts: the exact live agent (running) or end evidence. An unclear observation changes nothing.
  let next = structuredClone(chat);
  if (own?.kind === 'match') next.session = {agent: chat.agent ?? run.agent, id: own.id};
  if (live.namingError) next.namingError = live.namingError;
  else delete next.namingError;
  facts.timeZone = p.timeZone;
  if (observed.state === 'ended' || observed.state === 'running' && observed.exact) applyLifecycle(next, observed);
  if (live.alive) delete next.startUnconfirmed;
  next = observeIdle(next, live, p.now());
  const recovered = live.alive && failure;
  const nativeChange = !sameFact(next, chat) || recovered;
  if (nativeChange || metricsStartAt !== null) {
    const saveObservation = () => commitRun(run,p,latest=>{
      const saved=latest.chats.find(item=>sameChat(item,chat));
      if(saved&&sameFact(saved,chat)) {
        copyObservation(saved,next);
        if (metricsStartAt !== null && !latest.metricsStartRecorded) {
          latest.metricsStartRecorded=true;
          latest.metricsObservations=[...(latest.metricsObservations ?? []),{type:'start',at:new Date(metricsStartAt).toISOString(),data:latest.metricsOrigin ?? {origin:'unknown',requiredOutcome:'unknown'}}];
        }

      }
      if(recovered&&equalFact(latest.chatFailure,failure))clearChatFailure(latest);
    });
    if (nativeChange) saveObservation();
    else try { saveObservation(); } catch { /* Existing incomplete coverage remains; retry on a later observation. */ }
  }
  if (live.alive) {
    // An alive agent can still fail every turn on its login or usage limit (#2902); a gate or question keeps its words.
    const health = run.state === 'running' && !run.gate && !openQuestion(run) && !failure ? await chatHealth({ run, chat: next, live }, p) : null;
    if (health) { facts.health = { ...health, at: p.now(), timeZone: p.timeZone }; return 'cannot-work'; }
    const saved = currentChat(run);
    if (idleAgent(next, live) && saved?.paneId === next.paneId && saved.session?.id === next.session?.id
      && saved.idleAnchor === launchAnchor(next) && Number.isFinite(saved.idleSince)) return 'idle';
    return ['blocked', 'working'].includes(live.status) ? live.status : null;
  }
  if (failure) return 'unconfirmed';
  if (live.code === 'server_unavailable') return 'unavailable';
  // A saved end stays true while Herdr cannot tell; otherwise an unclear answer keeps the words status had.
  if (observed.state === 'ended') return 'stopped';
  if (!['agent_not_found', 'server_not_running'].includes(live.code)) return null;
  const anchor = launchAnchor(chat);
  return observed.state === 'starting' && (anchor === null || p.now() >= anchor + START_GRACE_MS) ? 'starting' : null;
}

// What status needs to know about the gate: PR 1's draft prompts at the code gate, nothing to try before the PR.
async function gateFacts(run, p) {
  const normal = normalRun(run, p);
  if (run.gate?.kind === 'ask-code') return { normal, drafts: await pr1Drafts(run, p) };
  if (run.gate?.kind === 'approve-pr') return { normal, nothing: nothingToTry(run, run.areas[run.area], await worktreeContents(run, p)) };
  return { normal };
}

function detail(run, chat = null, facts = {}) {
  const drafts = facts.drafts ?? [], stories = ownStoryCount(run), pr1Stories=(run.evidence??[]).some(e=>e.association?.stage==='pr1')?ownStoryCount(run,{stage:'pr1'}):null;
  const area = run.areas[run.area], tab = currentChat(run) ?? run.chats?.at(-1);
  const ci = pr => ({ passing: 'CI passing', failing: 'CI failing', pending: 'CI running', none: 'no CI checks' }[pr.ci] ?? 'CI unknown');
  const steps = (area?.steps ?? []).map(step => `${step} ${run.done[step] ? 'done' : 'to do'}${run.done[step]?.summary ? ` ("${clip(oneLine(run.done[step].summary), 120)}")` : ''}`);
  const pending = run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase);
  const next = run.gate?.automaticHold ? `Resolve the PR 1 hold: ${run.gate.automaticHold}.` : pending ? `pdd workflow open ${run.number} --new` : activeChatFailure(run) || ['unconfirmed', 'unavailable', 'starting', 'closed'].includes(chat) ? `pdd workflow open ${run.number}`
    : chat === 'cannot-work' && facts.health && run.state === 'running' ? cannotWorkWords(run, facts.health).next
    : environmentRecovery(run) ? (environmentRecovery(run).attempts >= ENVIRONMENT_BACKOFF.length
      ? 'Environment retries are exhausted. Inspect the environment alert in pdd autopilot status before resuming the failed validation.'
      : 'Autopilot retries only this validation when the host is healthy; inspect pdd autopilot status for any environment alert.')
    : facts.normal && run.storyApproval && run.gate?.kind === 'approve-pr' && !atStoryGate(run) ? `pdd workflow done check --summary \"Prompt tests line\"`
    : facts.normal && run.storyApproval && run.gate?.kind === 'ask-code' ? run.through === 'code' ? 'Fix the reported code entry problem, then run pdd workflow done check.' : codeLater(run)
    : run.gate ? approvalGuide(run)
    : runtimeWaiting(run) ? `nothing for a person unless an Autopilot alert asks (pdd autopilot status). Autopilot wakes this run when the interpreter is back; the worker then reads pdd test --read${run.runtimeWait.batch ? ` ${run.runtimeWait.batch}` : ''} first.`
    : ended(run) ? null : run.promptReturn && area?.steps.some(step=>!run.done[step]) ? `pdd workflow open ${run.number}` : prOf(run, area?.name) ? (run.pr.length > 1 && run.prBase && run.prBase !== run.baseBranch && run.pr[0]?.state === 'open' && run.pr[0]?.ci === 'failing'
      ? 'Review and merge PR 2 on GitHub: PR 1\'s CI fails, so PR 2 also merges PR 1. Do not merge PR 1 alone. pdd never merges.'
      : `Review and merge ${run.pr.length > 1 && run.prBase && run.prBase !== run.baseBranch ? 'PR 1, then PR 2,' : 'the PR'} on GitHub. pdd never merges.`) : `pdd workflow open ${run.number}`;
  return [`${run.repo}#${run.number} "${oneLine(run.issue.title)}" · ${run.workflow} · ${run.agent}${run.agentDefinition?.name ? ` ${JSON.stringify(run.agentDefinition.name)}` : ''}`,
    `State: ${describe(run, chat, facts)}`,
    ...(run.parking && !ended(run) ? [`Parking: ${run.parking.phase} (${run.parking.blocker.kind}), since ${new Date(run.parking.at).toISOString()}`] : []),
    ...(['stuck', 'paused'].includes(run.state) ? [`Cause: ${run.stuckCause ?? classifyStuckCause(run.parkReason, runtimeWaiting(run))}`] : []),
    ...cleanupLines(run),
    `Launch: model ${launchProfile(run).model ?? 'account default'}; account ${launchProfile(run).configDir ?? 'default folder'}; Codex threads ${launchProfile(run).codexThreads ?? 'account default'}`,
    ...(tab?.herdrAgentName ? [`Herdr agent: ${tab.herdrAgentName}; pane ${tab.paneId}`] : []),
    ...(facts.namingError ? [`Herdr name is not bound (${facts.namingError.code}); inspect the saved pane.`] : []),
    ...promptReturnLines(run),
    ...(pending ? [`Chat replacement pending: ${run.chatReplacement.phase}; retry pdd workflow open ${run.number} --new, or end with pdd workflow cancel ${run.number}.`] : []),
    ...(pending && run.chatReplacement.phase==='launchRequested' ? ['After startup grace, --new sends the saved launch once only if authoritative inspection proves the latest request never ran; unknown or agent processes keep it pending.'] : []),
    ...(area ? [`Area ${run.area + 1} of ${run.areas.length}: ${area.name} — ${steps.join(', ')}`] : []),
    ...(tab && !ended(run) ? [`Chat: Herdr session pdd, tab "${tab.label}" — pdd workflow open ${run.number}`] : []),
    ...(run.pr ?? []).map(pr => { const label = prLabel(run, run.areas.find(item => item.name === pr.stage) ?? {}); return `${label === 'the PR' ? 'PR' : label}: ${pr.url} — ${pr.state ?? 'open'}, ${ci(pr)}${pr.base && pr.base !== run.baseBranch ? ` (stacked on ${pr.base})` : ''}`; }),
    ...(drafts.length ? [draftLine(drafts)] : []),
    ...(stories ? [`Stories: ${storyText(stories)}${stories.failing.length ? ` (✗ ${stories.failing.join(', ')})` : ''}`,
      ...(stories.unknown?.length ? [`Unknown Stories: ${stories.unknown.join(', ')}`] : []),
      ...(stories.evidence ? [stories.evidence] : [])] : []),
    ...(pr1Stories ? [`PR 1 Stories: ${storyText(pr1Stories)}`] : []),
    ...beforeResults(run).map(beforeLine),
    `Worktree: ${run.root} (branch ${run.branch})`, `Run folder: ${run.runDir}`, `Review without resuming: pdd workflow view ${run.repo}#${run.number}`, ...(next ? [`Next: ${next}`] : [])].join('\n');
}

// One list line per run, grouped by what it needs: the person, the agent, a PR review, nothing.
const GROUPS = ['waiting', 'working', 'pr-open', 'done', 'cancelled'];
function savedRuntimeEvidence(run, results = []) {
  const latest = [...(run.pddHistory ?? []), ...Object.values(run.done ?? {}).flatMap(record => record?.pddResults ?? []), ...results]
    .filter(result => ['pdd test','pdd lint'].includes(result?.kind) && result.coverage?.runtime)
    .sort((a,b) => (b.at ?? 0) - (a.at ?? 0))[0];
  const published = run.workflow === 'small-change' && !askArea(run) ? run.pr?.at(-1)?.readable?.facts?.records : null;
  const smallChange = published ? {checklist: published.checklist, formal: published.formal}
    : Object.values(run.done ?? {}).filter(record => record.smallChange).sort((a,b) => b.at - a.at)[0]?.smallChange;
  return {...(latest ? {runtimeCoverage:latest.coverage.runtime,nativeOnly:latest.nativeOnly ?? []} : {}), ...(smallChange ? {smallChange} : {})};
}
function runtimeStatusLines(evidence, {smallChange = true} = {}) {
  const value = evidence.runtimeCoverage;
  const scope = smallChange ? evidence.smallChange : null;
  const small = scope ? [`Issue checklist: ${scope.checklist?.status ?? 'missing'}`, formatFormalEvidence(scope.formal, true)] : [];
  return [...small, ...(value ? [`Runtime coverage: ${value.checkable} of ${value.total} prompts checkable, ${value.native_only} native-only`,
    ...(evidence.nativeOnly ?? []).flatMap(row => (row.prompts ?? []).map(prompt => `${row.test} ${row.state}: ${prompt.path}: ${oneLine(prompt.reason)}`))] : [])];
}

function summary(run, timeZone, chat = null, { drafts = [], nothing = false, health = null, normal = false, suite = null, now = null, namingError = null } = {}) {
  const area = run.areas[run.area], ask = askArea(run), running = run.state === 'running';
  const cardRun = normal && Boolean(run.storyApproval);
  const replacementPending = run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase);
  const problem = replacementPending || activeChatFailure(run) || ['unconfirmed', 'unavailable', 'starting', 'closed'].includes(chat);
  const question = openQuestion(run), writing = !problem && Boolean(run.gate) && !question && chat === 'working';
  const cannotWork = !problem && !question && !run.gate && running && chat === 'cannot-work' && health ? health : null;
  const group = run.state === 'cancelled' ? 'cancelled' : run.state === 'completed' ? 'done' : run.parking?.phase === 'parked' ? 'waiting' : environmentRecovery(run) && environmentRecovery(run).attempts < ENVIRONMENT_BACKOFF.length ? 'working' : run.state === 'stuck' ? 'waiting' : runtimeWaiting(run) ? 'working' : problem ? 'waiting' : writing ? 'working'
    : run.state === 'stuck' || run.gate || question || cannotWork || running && ['blocked', 'stopped'].includes(chat) ? 'waiting' : prOf(run, area?.name) && !(run.promptReturn && area?.steps.some(step=>!run.done[step])) ? 'pr-open' : 'working';
  const step = area?.steps.find(item => !run.done[item]);
  const words = group === 'cancelled' ? (run.cancelled?.state === 'replaced' ? 'replaced' : 'cancelled')
    : group === 'done' ? (run.gate?.kind === 'ask-code' ? 'done at PR 1' : 'done')
    : run.parking?.phase === 'parked' ? `parked (${run.parking.blocker.kind})${run.gate?.automaticHold ? ` · PR 1 waits: ${run.gate.automaticHold}` : ''}`
    : environmentStatus(run) ? environmentStatus(run)
    : run.state === 'stuck' ? `stuck: ${stuckReason(run)}`
    : suite && (suite.state !== 'finished' || suite.reason) ? suiteStatusWords(suite)
    : runtimeWaiting(run) ? `waiting for the interpreter: ${run.runtimeWait.reason}`
    : replacementPending ? `chat replacement pending at ${run.chatReplacement.phase}; run pdd workflow open ${run.number} --new`
    : problem ? chatStatusWords(run, chat)
    : question ? `waiting for you: ${question.text.split('\n')[0]}`
    : cannotWork ? cannotWorkWords(run, cannotWork).short
    : !run.gate && running && chat === 'blocked' ? `waiting for you: the chat asks a question in its window`
    : !run.gate && running && chat === 'stopped' ? `the chat stopped: run pdd workflow open ${run.number}`
    : run.gate?.automaticHold ? `PR 1 waits: ${run.gate.automaticHold}`
    : writing ? (revising(run) ? 'agent working on your changes' : 'agent writing the gate message')
    : run.gate?.kind === 'ask-code' && drafts.length ? `waiting for you: approve the draft prompt${drafts.length > 1 ? 's' : ''}, then the code PR (PR 1 open)`
    : run.gate?.kind === 'ask-code' && cardRun ? run.through === 'code' ? 'code PR requested; code entry waits' : 'stopped after PR 1; code can start when requested'
    : run.gate?.kind === 'ask-code' ? 'waiting for you: code PR now or stop (PR 1 open)'
    : run.gate?.kind === 'approve-pr' && cardRun && !atStoryGate(run) ? 'agent must finish the prompt check before PR 1'
    : run.gate?.kind === 'approve-pr' ? `waiting for you: ${nothing ? '' : 'try it, then '}approve to open ${area.then === 'ask-code' ? 'PR 1' : 'the PR'}`
    : run.gate ? `waiting for you: approve the ${run.gate.area}`
    : group === 'pr-open' ? `${!ask ? 'PR' : area.then === 'ask-code' ? 'PR 1' : 'PR 2'} open`
    : running && chat === 'idle' && step ? idleWords(run, timeZone)
    : running && automaticResumeWords(run, now) ? automaticResumeWords(run, now)
    : step ? `agent working on ${step}` : 'agent working';
  const ref = `${run.repo}#${run.number}`;
  const when = Number.isFinite(run.updatedAt) ? new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit', hourCycle: 'h23', ...(timeZone ? { timeZone } : {}) }).format(new Date(run.updatedAt)) : 'unknown time';
  const prs = (run.pr ?? []).map(pr => ({ number: pr.number, url: pr.url, state: pr.state ?? 'open' })), stories = ownStoryCount(run);
  return { ...savedRuntimeEvidence(run), ...(suite ? { suite } : {}), ref, repo: run.repo, number: run.number, workflow: run.workflow, area: area?.name ?? null, group, words, prs, stories, waitingForStory: normal && atStoryGate(run),
    launchProfile: launchProfile(run), chat: lastChat(run, area?.name) ? {herdrAgentName: lastChat(run, area?.name).herdrAgentName ?? null, paneId: lastChat(run, area?.name).paneId, ...(namingError ? {namingError} : {})} : null,
    ...(cannotWork ? { chatProblem: { kind: cannotWork.kind, agent: cannotWork.agent, until: cannotWork.until !== null ? new Date(cannotWork.until).toISOString() : null, message: cannotWork.message } } : {}),
    ...((run.evidence??[]).some(e=>e.association?.stage==='pr1')?{pr1Stories:ownStoryCount(run,{stage:'pr1'})}:{}),
    ...((run.evidence??[]).some(beforeStage)?{before:beforeResults(run)}:{}),
    updatedAt: run.updatedAt ?? null, root: run.root, runDir: run.runDir, viewCommand: `pdd workflow view ${ref}`,
    line: [ref, run.workflow, area?.name ?? '?', words, ...(stories ? [storyText(stories)] : []), ...(prs.length ? [`PR ${prs.map(pr => `#${pr.number}`).join(' ')}`] : []), when].join(' · ') };
}

function ownershipLines(owner) {
  return owner?[`Workflow progress ownership: ${owner.path}; PID ${owner.pid??'unknown'}, host ${owner.hostname??'unknown'}, token ${owner.token??'unknown'}.${owner.warning?` ${owner.warning}.`:''} If no pdd command is running, inspect and remove this ownership folder, then retry.`]:[];
}

// Project saved steps, rather than the current area or the newest run-wide results.
function savedStepResults(run) {
  return Object.entries(run.done ?? {}).map(([step, record]) => ({ step,
    area: record.area ?? run.areas.find(area => area.steps.includes(step))?.name ?? null,
    pddResults: record.pddResults ?? [] }));
}

async function listStatus(runs, { json, cancelled, scope, snapshotOnly=false }, p) {
  const reading = runs.filter(run => run.state === 'waiting' && run.pr?.length).reduce((sum, run) => sum + run.pr.length, 0);
  if (reading) p.say(`Reading ${reading} PR${reading === 1 ? '' : 's'} from GitHub…`);
  for (const run of runs) if (!snapshotOnly && !readRunOwnership(run.runDir,p) && run.state === 'waiting' && run.pr?.length) { try { await refreshPr(run, p); } catch(error) { if(error?.code==='workflow_run_save_failed')throw error; /* A PR read failure keeps the saved state. */ } }
  const all = [];
  for (const run of runs) {
    const ordinaryOwnership=readRunOwnership(run.runDir,p);
    const health = {}, chat = ordinaryOwnership||snapshotOnly?null:await chatState(run, p, health);
    const item = summary(run, p.timeZone, chat, { ...(ended(run)||ordinaryOwnership||snapshotOnly ? {} : await gateFacts(run, p)), ...health, now: p.now(), suite: readSuiteProgress({cwd:run.root, since:run.updatedAt ?? 0, env:p.env}, p) });
    const snapshot = requestSnapshot(run, p);
    all.push({ ...item, chats: run.chats ?? [], steps: savedStepResults(run), ...snapshot, ordinaryOwnership, line: [item.line, ...cleanupLines(run), ...ownershipLines(ordinaryOwnership), ...requestLines(snapshot, { openOnly: true, ended: ended(run), currentArea: run.areas[run.area]?.name, p })].join('\n') });
  }
  const hidden = cancelled ? 0 : all.filter(item => item.group === 'cancelled').length;
  const shown = all.filter(item => cancelled || item.group !== 'cancelled')
    .sort((a, b) => GROUPS.indexOf(a.group) - GROUPS.indexOf(b.group) || (b.updatedAt ?? 0) - (a.updatedAt ?? 0));
  let herdr = null, inventory = [];
  try {
    herdr = {...await paneUsage({...p,onPaneUsage:rows=>{inventory=rows;}}), finishedOpen: 0};
    const machineRuns = allRuns({cancelled:true},p);
    herdr.owners = paneOwners(inventory, machineRuns).owners;
    herdr.warning = herdr.budget && herdr.panes >= Math.ceil(herdr.budget * 0.9)
      ? `Herdr pane capacity is near its limit (${herdr.panes} of ${herdr.budget}). Run pdd workflow tidy.` : null;
    const reply = await herdrCommand(p)(['workspace', 'list']), workspaces = reply?.result?.workspaces;
    if (reply?.result?.type !== 'workspace_list' || !Array.isArray(workspaces)
      || workspaces.some(w => typeof w?.workspace_id !== 'string' || !w.workspace_id)
      || new Set(workspaces.map(w => w.workspace_id)).size !== workspaces.length) throw Error('invalid_workspace_inventory');
    const known = new Set(machineRuns.flatMap(run => [run.layout?.workspaceId, run.layout?.repoWorkspaceId,
      ...(run.chats ?? []).flatMap(chat => [chat.workspaceId, chat.repoWorkspaceId])]).filter(Boolean));
    herdr.unownedWorkspaces = workspaces.filter(w => !known.has(w.workspace_id)).map(w => ({workspaceId: w.workspace_id,
      closeCommand: `herdr --session pdd workspace close ${shellQuote(w.workspace_id)}`}));
    for (const run of machineRuns) {
      if (readRunOwnership(run.runDir,p)) continue;
      const snapshot = structuredClone(run);
      snapshot.chats = (snapshot.chats ?? []).filter(chat => !Number.isFinite(chat.closed?.confirmedAt));
      herdr.finishedOpen += (await closeFinishedChats(snapshot, {...p, dryRun:true})).closed;
    }
  } catch {}
  if (json) return done(JSON.stringify({ herdr, runs: shown.map(({ line, ...item }) => item) }, null, 2));
  const paneLines = herdr ? [`Herdr session pdd: ${herdr.panes} of ${herdr.budget} panes. ${herdr.finishedOpen} eligible finished chats.${herdr.finishedOpen ? ' Run pdd workflow tidy.' : ''} ${p.describePaneOwners(inventory)}`,
    ...(herdr.warning ? [herdr.warning] : []), ...(herdr.unownedWorkspaces ?? []).map(w => `Unowned workspace ${JSON.stringify(w.workspaceId)}: ${w.closeCommand}`)] : [];
  if (!shown.length) return done([...paneLines, `No pdd runs ${scope}.${hidden ? ` ${hidden} cancelled run${hidden > 1 ? 's' : ''} hidden; add --cancelled to see ${hidden > 1 ? 'them' : 'it'}.` : ''}`, 'Start one with: pdd workflow run NAME ISSUE'].join('\n'));
  const cards = shown.filter(item => item.waitingForStory).map(item => item.ref);
  return done([...paneLines, ...shown.map(item => [item.line,...runtimeStatusLines(item, {smallChange:false})].join('\n')),
    ...(cards.length ? [`Waiting for Story approval: ${cards.join(', ')}. Show each card: pdd workflow card N.`] : []),
    ...(hidden ? [`${hidden} cancelled run${hidden > 1 ? 's' : ''} hidden; add --cancelled to see ${hidden > 1 ? 'them' : 'it'}.`] : []),
    `Review without resuming: pdd workflow view ${shown[0].ref}`, `Open one: pdd workflow open ${shown[0].ref}`].join('\n'));
}

// The Story card of one run, read-only (#2962): no GitHub, Herdr or interpreter call and no saved change.
async function showStoryCardCommand({ ref, cwd }, ports) {
  const p = deps(ports), found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  let changes = run.gate?.storyChanges ?? [];
  if (!changes.length && run.storyApproval?.fingerprint && !ended(run))
    changes = fingerprintChanges(run.storyApproval.fingerprint, storyFingerprint({ root: run.root, changed: await changedFiles(run, p) }));
  const results = run.area > storyGateIndex(run) && storyGateIndex(run) >= 0 ? pddTestLines(run, p) : [];
  return done(await cardText(run, p, { changes, results }));
}

async function runStatusCommand({ ref, cwd, all = false, json = false, cancelled = false }, ports, snapshotOnly=false) {
  const p = deps(ports);
  if (ref === undefined && (all || !(await gitContext(cwd, p)))) return listStatus(allRuns({ cancelled }, p), { json, cancelled, scope: 'on this machine', snapshotOnly }, p);
  if (ref === undefined && !(await runForWorktree(cwd, p))) return listStatus(await listRuns({ cwd, cancelled }, p), { json, cancelled, scope: 'in this repository', snapshotOnly }, p);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  // A login file of a launch that never ran must not stay in the run folder.
  removeStaleLoginFiles(found.run.runDir);
  if (found.run.pr?.length && found.run.state !== 'cancelled') p.say(`Reading ${found.run.pr.length === 1 ? 'the PR' : `${found.run.pr.length} PRs`} from GitHub…`);
  const ordinaryOwnership=readRunOwnership(found.run.runDir,p);
  if(!ordinaryOwnership&&!snapshotOnly)await refreshPr(found.run, p);
  const run = found.run, facts = ended(run)||ordinaryOwnership||snapshotOnly ? {} : await gateFacts(run, p), chat = ordinaryOwnership||snapshotOnly?null:await chatState(run, p, facts);
  facts.suite = readSuiteProgress({cwd:run.root, since:run.updatedAt ?? 0, env:p.env}, p);
  facts.now = p.now();
  const snapshot = requestSnapshot(run, p);
  const currentResults=ownResults(run,p), nativeResults=currentResults.filter(result=>result.kind==='native evidence');
  const runtimeEvidence=savedRuntimeEvidence(run,currentResults);
  const steps = savedStepResults(run);
  if (json) { const { line, ...item } = summary(run, p.timeZone, chat, facts); return done(JSON.stringify({ runs: [{ ...item, ...runtimeEvidence, chats: run.chats ?? [], steps, ...snapshot, ordinaryOwnership, nativeResults }] }, null, 2)); }
  return done([detail(run, chat, facts), ...runtimeStatusLines(runtimeEvidence), ...steps.flatMap(({ step, area, pddResults }) =>
    [`Step: ${area ?? 'unknown'} / ${step}`, ...resultLines(pddResults).map(line => `  ${line}`)]),
    ...(nativeResults.length?resultLines(nativeResults):[]), ...ownershipLines(ordinaryOwnership), ...requestLines(snapshot, { ended: ended(run), currentArea: run.areas[run.area]?.name, p })].join('\n'));
}

const replacementPhases = ['intent', 'closeRequested', 'closed', 'createRequested', 'prepared', 'launchRequested', 'launched', 'rolledBack', 'ended'];
function validReplacement(record, run) {
  if (!record || typeof record !== 'object' || Array.isArray(record) || Object.keys(record).some(key => !['id', 'area', 'phase', 'at', 'original', 'configDir', 'launchProfile', 'replacement', 'recovery'].includes(key)) || !validSessionId(record.id) || !Number.isSafeInteger(record.at) || record.at < 0 || !replacementPhases.includes(record.phase) || !run.areas.slice(0, run.area + 1).some(area => area.name === record.area)) return false;
  if (Object.hasOwn(record, 'configDir') && (record.configDir !== null && (typeof record.configDir !== 'string' || !record.configDir.length)
    || record.replacement && record.replacement.configDir !== record.configDir)) return false;
  if (record.launchProfile !== undefined && (!validLaunchProfile(record.launchProfile) || record.launchProfile.agent !== run.agent
    || record.launchProfile.configDir !== record.configDir || record.replacement && !sameFact(record.replacement.launchProfile, record.launchProfile))) return false;
  const recovery = record.recovery;
  if (recovery !== undefined && (!recovery || typeof recovery !== 'object' || Array.isArray(recovery)
    || Object.keys(recovery).some(key => !['closeAcknowledged','resumeRequested','allocationLabel','tabIdsBefore','latestLaunchRequest','unsentProof'].includes(key))
    || ['closeAcknowledged','resumeRequested'].some(key => recovery[key] !== undefined && typeof recovery[key] !== 'boolean')
    || recovery.allocationLabel !== undefined && (typeof recovery.allocationLabel !== 'string' || !recovery.allocationLabel)
    || recovery.tabIdsBefore !== undefined && (!Array.isArray(recovery.tabIdsBefore) || recovery.tabIdsBefore.some(id => typeof id !== 'string' || !id) || new Set(recovery.tabIdsBefore).size !== recovery.tabIdsBefore.length))) return false;
  const request=recovery?.latestLaunchRequest,proof=recovery?.unsentProof;
  if(request!==undefined && (!request || typeof request!=='object' || Array.isArray(request) || Object.keys(request).some(key=>!['id','at'].includes(key)) || !validSessionId(request.id) || !Number.isFinite(request.at)))return false;
  if(proof!==undefined && (!proof || typeof proof!=='object' || Array.isArray(proof) || Object.keys(proof).some(key=>!['requestId','requestAt','observedAt','paneId','shellPid','foregroundProcessGroupId','shellName'].includes(key)) ||
    !validSessionId(proof.requestId) || !Number.isFinite(proof.requestAt) || !Number.isFinite(proof.observedAt) || typeof proof.paneId!=='string' || proof.paneId!==record.replacement?.paneId ||
    !Number.isSafeInteger(proof.shellPid) || proof.shellPid<=0 || proof.foregroundProcessGroupId!==proof.shellPid || !['bash','zsh','sh','dash','fish','ksh','tcsh'].includes(proof.shellName)))return false;
  const chat = value => value && value.area === record.area && value.agent === run.agent && ['tabId', 'paneId', 'workspaceId', 'messageFile'].every(key => typeof value[key] === 'string' && value[key]) && (value.session == null || value.session.agent === value.agent && validSessionId(value.session.id));
  if (!chat(record.original) || typeof record.original.originalMessageFile !== 'string' || !record.original.originalMessageFile || record.original.messageFile !== join(run.runDir, 'abandoned-chats', `${record.id}-start.md`)) return false;
  if (['rolledBack','ended'].includes(record.phase)) return true;
  const prepared = replacementPhases.indexOf(record.phase) >= 4;
  if (!prepared) return record.replacement === undefined;
  const replacement = record.replacement;
  return chat(replacement) && replacement.paneId !== record.original.paneId && replacement.tabId !== record.original.tabId && replacement.workspaceId === record.original.workspaceId && typeof replacement.terminalId === 'string' && Boolean(replacement.terminalId) && typeof replacement.label === 'string' && Number.isSafeInteger(replacement.startedAt) && replacement.startedAt >= 0 && replacement.messageFile === join(run.runDir, `${record.area}-restart-${record.id}-start.md`) && (replacement.configDir === null || typeof replacement.configDir === 'string') && (record.phase !== 'launchRequested' || replacement.startUnconfirmed === true) && (record.phase !== 'launched' || !replacement.startUnconfirmed);
}
// Observations merge only into the same saved chat snapshot. Human progress,
// cancellation and replacement custody can change while Herdr is answering.
function conditionalCommit(run, p, eligible, update) {
  if (!eligible(readRun(run.runDir))) return false;
  let saved = false;
  commitRun(structuredClone(run), p, latest => { if (eligible(latest)) { update(latest); saved = true; } });
  return saved;
}
function copyObservation(selected, observed) {
  for (const key of CHAT_OBSERVATION) {
    if (Object.hasOwn(observed, key)) selected[key] = structuredClone(observed[key]);
    else delete selected[key];
  }
}
// Explicit AREA navigation owns only observations of the selected saved chat.
function saveAreaObservations(run, original, observed, p) {
  return conditionalCommit(run, p, fresh => fresh && fresh.runId === run.runId && !ended(fresh) && sameFact(lastChat(fresh, original.area), original),
    fresh => copyObservation(lastChat(fresh, original.area), observed));
}
// Default open and startup own chat observations, never a stale workflow snapshot.
function saveChatObservations(run, original, observed, p, { error, phase = 'open', reset = false, checkpoint = false, layout = null, automatic = false, resumeSuccess = null } = {}) {
  const area = original?.area ?? observed?.area ?? run.areas[run.area].name;
  if (observed && original?.resumedAt !== observed.resumedAt) { delete observed.idleSince; delete observed.idleAnchor; }
  // A late reset cannot retire historical custody; a dispatched start retains it.
  return conditionalCommit(run, p, fresh => fresh && fresh.runId === run.runId && !ended(fresh) && sameFact(lastChat(fresh, area), original) && !(reset && fresh.area !== run.area), fresh => {
    const selected = lastChat(fresh, area);
    if (reset) {
      fresh.abandonedChats = [...(fresh.abandonedChats ?? []), { ...selected, abandonedAt: p.now(), reason: 'tab-and-agent-missing' }];
      fresh.chats = fresh.chats.filter(chat => chat !== selected);
    } else if (selected && observed) copyObservation(selected, observed);
    else if (observed) fresh.chats.push(structuredClone(observed));
    // Verified live custody supersedes stale hints; partial allocation saves retain known fields.
    if (layout) fresh.layout = { ...fresh.layout, ...structuredClone(layout) };
    if (checkpoint) return;
    if (resumeSuccess && observed && !observed.startUnconfirmed && fresh.state === 'running' && fresh.areas[fresh.area].name === area)
      fresh.chatResumeSuccess = {...resumeSuccess, area, paneId: observed.paneId, sessionId: observed.session?.id, resumedAt: observed.resumedAt};
    // A late failed open of an area that is no longer current keeps its own record, but never replaces a current failure.
    if (error && phase === 'open' && fresh.areas[fresh.area].name !== area && !activeChatFailure(fresh))
      fresh.chatFailure = { area, phase, code: oneLine(error.code ?? 'error').slice(0, 100), message: firstLine(error.message ?? 'Herdr request failed').slice(0, 500), at: p.now() };
    if (fresh.areas[fresh.area].name === area && sameFact(fresh.chatFailure, run.chatFailure)) {
      const stateFields = ['state', 'area', 'done', 'gate', 'question', 'approvalRecord', 'decisions'];
      const unchanged = stateFields.every(key => sameFact(fresh[key], run[key]));
      if (error) {
        fresh.chatFailure = { area, phase, code: oneLine(error.code ?? 'error').slice(0, 100), message: firstLine(error.message ?? 'Herdr request failed').slice(0, 500), at: p.now() };
        if (unchanged && !automatic) fresh.state = 'waiting';
      } else if (fresh.chatFailure) {
        if (unchanged) clearChatFailure(fresh);
        else delete fresh.chatFailure;
      }
    }
  });
}
const promptReturnLines = run => run.promptReturn
  ? [`Returned to prompt space: ${run.promptReturn.reason}. Code checks from before the return were cleared.`] : [];
async function specificationEdits(run,p,base,candidate) {
  // Check only prompts. A failed scenario inventory remains the replay owner's
  // BLOCKED result; it must not turn into an unrelated prompt-listing exception.
  await rawGit(p,run.root,'fetch','origin',`refs/heads/${base}:refs/remotes/origin/${base}`);
  const delta=await p.execFile('git',['diff','--quiet',`refs/remotes/origin/${base}`,...(candidate?[candidate]:[]),'--','*.prompt.md'],{cwd:run.root}).catch(error=>{
    if(error.code===1)return {code:1};
    throw error;
  });
  if(delta.code!==undefined && ![0,1].includes(delta.code))throw Error('Prompt comparison unavailable.');
  const untracked=candidate?[]:(await rawGit(p,run.root,'ls-files','--others','--exclude-standard','-z')).split('\0').filter(path=>path.endsWith('.prompt.md'));
  return [...(delta.code===1?['tracked prompt changes']:[]),...untracked];
}
async function storyContractPaths(run,p,reference) {
  const comparison = await git(p,run.root,'merge-base',reference ?? 'HEAD',`refs/remotes/origin/${run.baseBranch}`);
  const paths = reference
    ? (await rawGit(p,run.root,'diff','--name-only','-z',comparison,reference)).split('\0').filter(Boolean)
    : await changedFiles({...run,baseSha:comparison},p,true);
  const approved=[...run.decisions].reverse().find(decision=>Array.isArray(decision.storyPaths))?.storyPaths??[];
  return [...new Set([...approved,...paths])].filter(path=>isStoryPath(path)||path.endsWith('.json')).sort();
}
async function storyContract(run,p,reference) {
  const texts=[];
  const paths=await storyContractPaths(run,p,reference);
  // Only a successful tree inventory proves absence. A failed blob read must
  // remain unavailable source, including ENOENT from the Git program port.
  const treePaths=reference ? new Set((await rawGit(p,run.root,'ls-tree','-r','--name-only','-z',reference)).split('\0').filter(Boolean)) : null;
  for (const path of paths.sort()) {
    if(!isStoryPath(path) && !path.endsWith('.json'))continue;
    let text;
    if (reference) {
      if (!treePaths.has(path)) continue;
      text=await rawGit(p,run.root,'show',`${reference}:${path}`);
    } else {
      try {text=readFileSync(join(run.root,path),'utf8');}
      catch(error) {if(error.code==='ENOENT')continue;throw error;}
    }
    texts.push([path,text]);
  }
  return storyContractHash(run, texts);
}
function storyContractHash(run, texts) {
  const facts=[];
  for (const [path,text] of texts) {
    if (isStoryPath(path)) facts.push([path,text]);
    else {
      try {if(isScenario(text))facts.push([path,canonical(JSON.parse(text))]);} catch {
        if(run.replayBaseline?.vectors?.some(v=>v.path===path))facts.push([path,text]);
      }
    }
  }
  return createHash('sha256').update(JSON.stringify(facts)).digest('hex');
}
function approvedStoryContract(run) {
  return [...run.decisions].reverse().find(item=>item.decision==='approve' && typeof item.storyContract==='string')?.storyContract;
}
async function reopenChangedStory(run,p,entryContract,observedContract) {
  if(ended(run) || (!run.promptReturn && !entryContract) || run.areas[run.area]?.then!=='ask-code')return false;
  const contract=observedContract ?? await storyContract(run,p);
  if(contract===(run.promptReturn?approvedStoryContract(run):entryContract))return false;
  const story=run.areas.findIndex(item=>item.gate==='approve');
  if(story<0)return false;
  commitRun(run,p,latest=>{
    if(ended(latest) || latest.area!==run.area || latest.promptReturn?.at!==run.promptReturn?.at)throw Object.assign(Error('The returned area changed. Look at the current run again.'),{code:'workflow_progress_refused'});
    for(const item of latest.areas.slice(story))for(const step of item.steps)delete latest.done[step];
    latest.area=story;latest.gate=null;latest.question=null;latest.state='running';
  });
  return true;
}
function resetPromptChecks(run,p) {
  const prompt=run.areas.findIndex(item=>item.then==='ask-code'),selected=Math.min(run.area,prompt);
  commitRun(run,p,latest=>{
    for(const area of latest.areas.slice(selected))for(const step of area.steps)delete latest.done[step];
    latest.area=selected;latest.gate=null;latest.question=null;latest.state='running';
  });
}
async function integratePromptBase(run,p) {
  if ((await rawGit(p,run.root,'status','--porcelain=v1','-z')).length) return 'Commit the PR 1 edits before updating its base, then open prompt-pr again.';
  let source;
  try {
    await rawGit(p,run.root,'fetch','origin',`refs/heads/${run.baseBranch}:refs/remotes/origin/${run.baseBranch}`);
    source=await git(p,run.root,'rev-parse','--verify',`refs/remotes/origin/${run.baseBranch}^{commit}`);
    if (!commitSha(source)) throw Error('Invalid fetched base');
  } catch { return `Cannot fetch the saved base ${run.baseBranch}. PR 1 remains current; retry workflow open ${run.number} prompt-pr when the base is available.`; }
  const comparison=await git(p,run.root,'merge-base','HEAD',source);
  if (comparison===source) return null;
  resetPromptChecks(run,p);
  try { await rawGit(p,run.root,'merge','--no-edit',source); return null; }
  catch { return 'PR 1 is current. Resolve its base merge conflicts, commit the resolution, run prompt checks, then finish with workflow done check.'; }
}
async function returnToPrompt(run,selected,p) {
  const ownership = await continuationOwnership(run,run.root,p);
  if(ownership)return ownership;
  if(run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase))return 'Finish the pending chat replacement before returning to prompt space.';
  const missing=missingHome(run,p.env);if(missing)return missing;
  if((await rawGit(p,run.root,'status','--porcelain=v1','-z')).length)return 'Commit or keep the current code edits before returning to PR 1; the worktree must be clean.';
  const prompt=askArea(run),pr1=prOf(run,prompt.name);
  let state;
  try {state=await (p.readPrStatus??readWorkflowPrStatus)({cwd:run.root,url:pr1?.url},p.commandPorts);} catch {return 'Cannot read PR 1. Retry when its state is available.';}
  if(!pr1 || state.state!=='open')return 'Returning to prompt space requires the owned PR 1 to be open.';
  protectProgress(run,p);
  const codeBranch=run.branch;
  try {
    await rawGit(p,run.root,'fetch','origin',`refs/heads/${pr1.branch}:refs/remotes/origin/${pr1.branch}`);
    await rawGit(p,run.root,'switch','-q',pr1.branch);
    await rawGit(p,run.root,'merge','--ff-only',`refs/remotes/origin/${pr1.branch}`);
  } catch {
    await rawGit(p,run.root,'switch','-q',codeBranch).catch(()=>{});
    return 'Cannot fast-forward the owned PR 1 branch. Repair its local branch, then retry.';
  }
  commitRun(run,p,latest=>{
    if(latest.area!==run.area || ended(latest))throw Error('The area changed while returning to prompt space.');
    latest.promptReturn={at:p.now(),reason:'a prompt correction was requested after code work',codeBranch,codeApprovalId:[...latest.decisions].reverse().find(decision=>decision.stage===prompt.name&&decision.decision==='approve')?.evidence?.id??null};
    for(const area of latest.areas.slice(selected))for(const step of area.steps)delete latest.done[step];
    for(const key of ['replayEvidence','testInventory','approvalRecord','publicationPending','chatReplacement'])delete latest[key];
    latest.runtimeHistory=[];latest.pddHistory=[];latest.evidence=[];latest.evidenceAssociations=[];
    latest.branch=pr1.branch;latest.prBase=run.baseBranch;latest.area=selected;latest.state='running';latest.gate=null;latest.question=null;
  });
  for(const file of ['replay-evidence.json','old-code-proof.json','test-inventory.json','verify.md','formal.md','review.md'])
    rmSync(join(run.runDir,file),{force:true});
  const integration = await integratePromptBase(run,p);
  if (integration) return integration;
  return null;
}
async function openRunLocked({ ref, cwd, area, newSession = false, model, herdrAgentName, codexThreads, packageRoot = PACKAGE_ROOT, automaticResume = null }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  if (run.parking?.phase === 'releasing') return fail('This parked run is releasing its claim. Wait for release to finish.');
  const selected = area === undefined ? run.area : run.areas.findIndex(item => item.name === area);
  let chat = [...(run.chats ?? [])].reverse().find(item => item.area === run.areas[selected]?.name), started = false, handedOff = false, rebuilt = false;
  if (selected < 0) return fail(`Unknown area ${area}. Valid areas: ${run.areas.map(item => item.name).join(', ')}.`);
  if (selected > run.area || area !== undefined && !chat) return fail(`The area ${area} has no recorded chat at or before the current area.`);
  if (automaticResume && (!validSavedAutomaticOrigin(run) || run.automaticOrigin.coordinatorId !== automaticResume.coordinatorId
    || run.automaticOrigin.machine !== automaticResume.machine || !samePath(run.sourceRoot, cwd)))
    return {...done(''), recovery: 'skipped'};
  if (!ended(run) || run.cancelled?.state === 'handed-over') {
    const ownership = await chatContinuationOwnership(run, p);
    if (ownership) return fail(ownership);
  }
  if (automaticResume && !ended(run) && !run.parking) {
    await observeRunSessions(run,p);
    chat = [...(run.chats ?? [])].reverse().find(item => item.area === run.areas[selected]?.name);
  }
  let beforeLaunch, resumeSuccess = null;
  if (automaticResume?.parked) {
    if (!validSavedAutomaticOrigin(run) || run.automaticOrigin.coordinatorId !== automaticResume.coordinatorId
      || run.automaticOrigin.machine !== automaticResume.machine || !samePath(run.sourceRoot, cwd)
      || run.parking?.phase !== 'waking' || run.parking.at !== automaticResume.at)
      return {...done(''), recovery: 'skipped'};
    beforeLaunch = async () => {
      const fresh = readRun(run.runDir);
      if (!fresh || fresh.runId !== run.runId || fresh.parking?.phase !== 'waking' || fresh.parking.at !== automaticResume.at
        || ended(fresh) || !sameFact(fresh.automaticOrigin, run.automaticOrigin))
        throw Object.assign(Error('Parked run changed before resume.'), {code: 'chat_target_changed'});
    };
  } else if (automaticResume) {
    const skipped = () => ({...done(''), recovery: 'skipped'});
    if (!validSavedAutomaticOrigin(run) || run.automaticOrigin.coordinatorId !== automaticResume.coordinatorId
      || run.automaticOrigin.machine !== automaticResume.machine || !samePath(run.sourceRoot, cwd)) return skipped();
    if (run.parking || layoutClosing(run) || chat?.closed) return skipped();
    if (run.state === 'stuck' && run.chatResumeLimit) return {...done(run.parkReason), recovery: 'stuck', area: run.chatResumeLimit.area};
    if (run.state !== 'running' || run.gate || openQuestion(run) || !chat || chat.startUnconfirmed
      || !validSessionId(chat.session?.id)
      || run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase)) return skipped();
    const selectedChat = structuredClone(chat);
    const stillEligible = fresh => fresh && fresh.runId === run.runId && fresh.state === 'running'
      && !layoutClosing(fresh) && !lastChat(fresh, selectedChat.area)?.closed
      && fresh.area === selected && !fresh.gate && !openQuestion(fresh)
      && sameFact(lastChat(fresh, selectedChat.area), selectedChat) && sameFact(fresh.done, run.done)
      && sameFact(fresh.automaticOrigin, run.automaticOrigin) && sameFact(fresh.chatReplacement, run.chatReplacement);
    const live = await chatSession(chat, p);
    if (live.alive || !['agent_not_found', 'pane_not_found', 'server_not_running'].includes(live.code)) return skipped();
    const absent = live.code === 'pane_not_found' ? {...live, code: 'agent_not_found'} : live;
    const own = sessionEvidenceDue(chat, absent, p.now()) && !observedSession(chat, chat.agent ?? run.agent)
      ? await ownSession({run, chat, since: launchAnchor(chat), ports: p}) : null;
    const observed = observeLifecycle(chat, absent, p.now(), chat.agent ?? run.agent, own?.kind === 'match' ? own.id : null);
    if (observed.state !== 'ended') return skipped();
    if (await chatHealth({run, chat, live}, p)) return skipped();
    const name = run.areas[run.area].name, at = p.now();
    const attempts = (run.chatResumes?.[name] ?? []).filter(time => Number.isFinite(time) && time > at - 3600000);
    if (attempts.length >= 3) {
      const reason = `The ${name} chat stopped after 3 automatic resume attempts in one hour. Inspect the chat before resuming this run.`;
      const saved = conditionalCommit(run, p, stillEligible, fresh => {fresh.state = 'stuck'; fresh.parkReason = reason; fresh.chatResumeLimit = {area: name, at};});
      return saved ? {...done(reason), recovery: 'stuck', area: name} : skipped();
    }
    beforeLaunch = async () => {
      const saved = conditionalCommit(run, p, fresh => fresh && fresh.runId === run.runId && fresh.state === 'running'
        && !layoutClosing(fresh) && !lastChat(fresh, name)?.closed
        && sameFact(lastChat(fresh, name), defaultOriginal)
        && fresh.area === selected && !fresh.gate && !openQuestion(fresh)
        && sameFact(fresh.automaticOrigin, run.automaticOrigin), fresh => {
          const at = p.now(), recent = (fresh.chatResumes?.[name] ?? []).filter(time => Number.isFinite(time) && time > at - 3600000);
          if (recent.length >= 3) throw Object.assign(Error('Automatic resume limit reached.'), {code: 'chat_resume_limit'});
          (fresh.chatResumes ??= {})[name] = [...recent, at];
          resumeSuccess = {at, count: recent.length + 1};
        });
      if (!saved) throw Object.assign(Error('The run changed before automatic resume.'), {code: 'chat_target_changed'});
    };
  }
  if (ended(run)) return endedChatHelp(run);
  let historical = selected < run.area, returned = false, returnWarnings = [];
  const promptIndex = run.areas.findIndex(item=>item.then==='ask-code');
  if (historical && promptIndex >= 0 && run.area > promptIndex && selected <= promptIndex) {
    if (newSession && p.env.PDD_AGENT_SESSION) return fail('Use another terminal outside the agent session to replace this chat.');
    const refused = await returnToPrompt(run,selected,p);
    if (refused) return fail(refused);
    historical=false;returned=true;
  }
  const profileOptions = [model, herdrAgentName, codexThreads].some(value => value !== undefined);
  if (profileOptions && (!newSession || historical)) return fail('Launch settings require --new for the current area.');
  if (!returned && !historical && area !== undefined && run.promptReturn && run.area === promptIndex) {
    const ownership = await continuationOwnership(run,run.root,p); if (ownership) return fail(ownership);
    const integration = await integratePromptBase(run,p); if (integration) return fail(integration);
  }
  let areaOriginal = area !== undefined && !newSession && !returned ? structuredClone(chat) : null;
  let defaultOriginal = chat ? structuredClone(chat) : undefined;
  if (newSession && historical) return fail(`Select the current area ${run.areas[run.area].name} to start a new session; earlier areas cannot be replaced.`);
  if (newSession && !chat && (!run.chatReplacement || ['launched','rolledBack','ended'].includes(run.chatReplacement.phase))) return fail('The current area has no saved chat to replace. Open it first.');
  const pending = run.chatReplacement;
  if (pending !== undefined) {
    if (!validReplacement(pending, run)) return fail('The saved chat replacement record is malformed or unknown. Inspect it before opening a chat.');
    if (!['launched', 'rolledBack', 'ended'].includes(pending.phase) && !newSession) return fail(`Chat replacement is pending at ${pending.phase}. Retry: pdd workflow open ${run.number} --new`);
  }
  const recovering = pending && !['launched','rolledBack','ended'].includes(pending.phase);
  const variable = homeVariable(run.agent);
  const incoming = newSession && !recovering && variable && typeof p.env[variable] === 'string' && p.env[variable].length ? p.env[variable] : null;
  const replacementConfig = incoming ? resolve(cwd, expandHome(incoming, p.env)) : launchProfile(run).configDir;
  if (incoming && !isFolder(replacementConfig)) return fail(`${variable} is "${replacementConfig}", but that folder does not exist. Fix ${variable} and run the command again.`);
  let replacementProfile;
  try { replacementProfile = recovering ? pending.launchProfile : newSession
    ? selectLaunchProfile({run, configDir: replacementConfig, model, herdrAgentName, codexThreads}, p) : launchProfile(run); }
  catch (error) { return fail(error.message); }
  // Pending recovery checks the profile of each effect, which may be the original
  // chat's folder rather than either the current run or the retrying terminal.
  const missing = !recovering && missingHome({ ...run, configDir: replacementConfig }, p.env);
  if (missing) return fail(missing);

  const snapshot = requestSnapshot(run, p);
  if (automaticResume && snapshot.requestWarning) return fail(snapshot.requestWarning);
  const groupResumeRequests = automaticResume?.parked ? readDeliveryJournal(run, p).requests.filter(entry => entry.key?.startsWith('group:') && entry.area === chat?.area && entry.state === 'pending' && !entry.inFlight) : [];
  const requests = [...(snapshot.requests ?? []), ...groupResumeRequests].filter(entry => entry.area === chat?.area && entry.ackedAt == null
    && !(snapshot.inFlightRequests ?? []).some(active => active.id === entry.id));
  const resumeMessage = requests.length ? ['Continue this same run. Keep completed steps and approvals. These requests are not approval.',
    ...requestLines({requests, pendingRequests: [], uncertainRequests: [], inFlightRequests: []}, {agent: true, p})].join('\n') : undefined;
  try {
    if (newSession) assertRestartCaller({chat, pending}, p);
    if (chat && !recovering) {
      rebuilt = await rebuildClosedChat({run, chat, resumeMessage, message: await areaMessage(run, selected, p, packageRoot) + (resumeMessage ?? '')}, {...p, beforeLaunch,
        checkpoint: async (observed, layout) => {
          if (layout && automaticResume?.parked) layout.phase = 'open';
          if (!saveChatObservations(run, defaultOriginal, observed, p, {checkpoint: true, layout}))
            throw Object.assign(Error('The run changed during workspace recovery.'), {code: 'chat_target_changed'});
          if (observed) {
            defaultOriginal = structuredClone(observed);
            if (areaOriginal) areaOriginal = structuredClone(observed);
          }
          if (layout) run.layout = {...run.layout, ...structuredClone(layout)};
        }});
      if (rebuilt) newSession = false;
    }
    if (newSession) {
      if (recovering) chat = pending.original;
      const replacementArea = recovering ? run.areas.findIndex(item => item.name === pending.area) : run.area;
      const currentArea = run.areas[replacementArea];
      const completed = currentArea.steps.filter(step => run.done[step]);
      const remaining = currentArea.steps.filter(step => !run.done[step]);
      const message = await areaMessage(run, replacementArea, p, packageRoot) + [
        'Continue this same run. Do not rerun already completed steps. Prior approval does not approve new work.',
        `Completed in this area: ${completed.map(step => `${step}: ${run.done[step].summary ?? 'done'}`).join('; ') || 'none'}.`,
        `Remaining steps: ${remaining.join(', ') || 'none; wait for the person'}.`,
        ...(run.gate ? [`Open gate: ${run.gate.kind} for ${run.gate.area ?? currentArea.name}. Wait for the person to decide whether to approve or request changes; do not treat this new session as approval.`] : []),
        ...(openQuestion(run) ? [`Pending question: ${openQuestion(run).text}`] : []),
      ].join('\n') + '\n';
      const replacementRun = { ...run, configDir: replacementConfig, launchProfile: replacementProfile };
      const checkpoint = async (record, layout) => {
        if (!validReplacement(record, run)) throw Object.assign(Error('Invalid replacement checkpoint'), { code: 'invalid_replacement_checkpoint' });
        const admit = fresh => {
          if (!fresh || ended(fresh)) throw Object.assign(Error('The run ended during replacement.'), {code:'run_ended'});
          const prior = fresh.chatReplacement;
          const sameAttempt = prior && prior.id === record.id && prior.at === record.at && sameFact(prior.original, record.original);
          if (sameAttempt && prior.launchProfile && !sameFact(prior.launchProfile, record.launchProfile)) throw Error('Replacement launch profile changed');
          if (sameAttempt && Object.hasOwn(prior, 'configDir') && prior.configDir !== record.configDir) throw Error('Replacement configuration changed');
          if (record.phase === 'intent' && !sameAttempt) {
            if (prior && !['launched','rolledBack','ended'].includes(prior.phase)) throw Error('Replacement already pending');
            if (prior?.id === record.id) throw Error('Invalid replacement transition');
          } else if (!sameAttempt || record.phase === 'intent' && prior.phase !== 'intent') throw Error('Invalid replacement transition');
          return sameAttempt;
        };
        admit(readRun(run.runDir));
        commitRun(run, p, fresh => {
          if (!admit(fresh)) (fresh.abandonedChats ??= []).push({ ...record.original, replacementId: record.id, abandonedAt: record.at, reason: 'explicit-new-session' });
          const priorPhase = fresh.chatReplacement?.phase;
          fresh.chatReplacement = structuredClone(record);
          if (layout) fresh.layout = {...fresh.layout, ...structuredClone(layout)};
          // Only the first current-area installation selects later-area inheritance.
          // Observation/recovery checkpoints must not retarget a newer saved account.
          if (record.phase === 'launchRequested' && record.area === fresh.areas[fresh.area]?.name
            && !['launchRequested','launched'].includes(priorPhase)) {
            fresh.configDir = record.configDir;
            if (record.launchProfile) fresh.launchProfile = structuredClone(record.launchProfile);
          }
          if (['launchRequested', 'launched', 'rolledBack'].includes(record.phase)) {
            fresh.chats = fresh.chats.filter(item => item.area !== record.area);
            fresh.chats.push(record.phase === 'rolledBack' ? {...record.original, messageFile: record.original.originalMessageFile} : {...record.replacement});
          }
          if (['launched','rolledBack','ended'].includes(record.phase) && record.area === fresh.areas[fresh.area]?.name) clearChatFailure(fresh);
        });
        Object.assign(replacementRun, run);
      };
      chat = await restartChat({ run: replacementRun, chat, message, pending: recovering ? pending : undefined }, { ...p, checkpoint });
      const replacementResult = message => done([...(chat.namingError ? [`Herdr name is not bound (${chat.namingError.code}); inspect the saved pane.`] : []), message].join('\n'));
      if (run.chatReplacement?.phase === 'ended') return replacementResult(`Ended the historical ${chat.area} replacement attempt without launching or resuming it. The current chat and progress are kept.`);
      if (run.chatReplacement?.phase === 'rolledBack') return replacementResult(`Restored the usable ${chat.area} chat. The same replacement attempt was rolled back.`);
      if (run.chatReplacement?.phase === 'launched' && chat.area === run.areas[run.area]?.name && !chat.startUnconfirmed) armCurrentAutomaticChat(run, p);
      if (run.chatReplacement?.recovery?.resumeRequested) return replacementResult(`Resumed this attempt's ${chat.area} session in Herdr session pdd; no second first message was sent. The run, completed work, gates and approvals are kept.`);
      return replacementResult(`Started one fresh ${chat.area} chat in Herdr session pdd. The run, completed work, gates and approvals are kept.`);
    }
    if (!chat) { chat = await startNextChat(run, p, packageRoot); defaultOriginal = structuredClone(chat); started = true; }
    p.say(`Opening the ${chat.area} chat in Herdr…`);
    const priorResumeAnchor = launchAnchor(chat);
    const opened = await openChat({ run, chat, resumeMessage }, { ...p, background: Boolean(automaticResume), beforeLaunch, beforeAttach: async () => {
      if (automaticResume?.parked) delete chat.closed;
      const saved = areaOriginal ? saveAreaObservations(run, areaOriginal, chat, p)
        : saveChatObservations(run, defaultOriginal, chat, p, {resumeSuccess});
      if (saved && !historical && (rebuilt || Number.isFinite(chat.resumedAt) && launchAnchor(chat) !== priorResumeAnchor)) armCurrentAutomaticChat(run, p);
      if (saved && returned) returnWarnings=noticeWarnings(await deliverRequest(run,await areaMessage(run,selected,p,packageRoot),p,true));
      handedOff = true;
      if (saved && !automaticResume?.parked && !historical && Number.isFinite(chat.resumedAt)
        && (rebuilt || launchAnchor(chat) !== priorResumeAnchor)) await continueResumedChat(run, chat, p, packageRoot);
      p.releaseRunLock?.();
    } });
    if (automaticResume?.parked && (rebuilt || opened.resumed) && groupResumeRequests.length) {
      await deliveryJournal(run, p, journal => {
        for (const offered of groupResumeRequests) {
          const entry = journal.requests.find(entry => entry.id === offered.id);
          if (entry?.state === 'pending' && !entry.inFlight && entry.text === offered.text) {
            entry.state = 'delivered'; entry.deliveredAt = p.now();
          }
        }
      });
    }
    if (opened.restartAvailable) {
      if (areaOriginal) return fail(`The ${chat.area} chat has an unconfirmed missing tab. Inspect its saved identity.`);
      if (historical) return fail(`The historical ${chat.area} chat has an unconfirmed missing tab. Inspect its saved identity.`);
      const message = `The saved tab and agent are gone. The stale start was cleared; the run and worktree are kept. Run pdd workflow open ${run.number} to start the ${chat.area} chat again.`;
      if (!saveChatObservations(run, defaultOriginal, chat, p, { error: { code: 'chat_start_reset', message }, reset: true }))
        return fail('The run changed during chat inspection. Its latest progress and chat custody are kept.');
      return fail(message);
    }
    if (!handedOff) {
      if (areaOriginal) saveAreaObservations(run, areaOriginal, chat, p);
      else saveChatObservations(run, defaultOriginal, chat, p);
    }
    // The gate shown is the latest saved one: the lock was released before attach, so reload the run record.
    const latest = readRun(run.runDir), gateRun = latest?.runId === run.runId ? latest : run;
    const shownGate = gateRun.gate?.promptSnapshot ? snapshotLines(gateRun.gate.promptSnapshot) : [];
    const where = `Herdr session pdd, tab "${chat.label}"`;
    return done([...(opened.namingError ? [`Herdr name is not bound (${opened.namingError.code}); inspect the saved pane.`] : []), ...promptReturnLines(gateRun), ...returnWarnings, ...shownGate, ...(gateRun.gate ? [approvalGuide(gateRun, p.pdd)] : []), started ? `Started the ${chat.area} chat in ${where}.` : opened.resumed ? `Resumed the ${chat.area} chat in ${where}.` : `The ${chat.area} chat is in ${where}.`,
      ...(opened.attached ? [] : [p.env.HERDR_ENV === '1' ? 'pdd focused that tab. If you are in another Herdr session, run: herdr session attach pdd' : 'See it with: herdr session attach pdd'])].join('\n'));
  } catch (error) {
    if (automaticResume?.parked && ['agent_not_found', 'pane_not_found'].includes(error.code) && chat) {
      delete chat.startUnconfirmed; chat.state = 'ended';
    }
    if (newSession) return fail([`Chat replacement ${run.chatReplacement?.phase ?? 'refused'} (${failureReason(error)}).${run.chatReplacement ? ` Retry: pdd workflow open ${run.number} --new` : ''}`, ...failureDetails(error)].join('\n'));
    if (!handedOff) {
      if (areaOriginal) saveAreaObservations(run, areaOriginal, chat, p);
      else saveChatObservations(run, defaultOriginal, chat, p, { error, phase: chat ? 'open' : 'start', automatic: Boolean(automaticResume) });
    }
    // A starting chat is not a failed one: say so, with the one safe next step.
    if (['chat_start_unconfirmed', 'chat_start_failed'].includes(error.code)) return fail(oneLine(error.message));
    return fail([`pdd could not open the ${run.areas[selected].name} chat (${failureReason(error)}).`, ...failureDetails(error)].join('\n'));
  }
}

const openRunCommand = async (args, ports) => {
  const p = deps(ports), found = await resolveRun(args.ref, {cwd: args.cwd}, p);
  if (found.run?.parking?.phase === 'releasing') return fail('This parked run is releasing its claim. Wait for release to finish.');
  if (found.run?.parking?.phase === 'parked') {
    const run = found.run, origin = run.automaticOrigin;
    const resumed = await wakeParkedRun({...args, at: run.parking.at, coordinatorId: origin.coordinatorId, machine: origin.machine}, ports);
    if (resumed.exitCode !== 0) return resumed;
  }
  return lockedMutation(args, ports, openRunLocked);
};

function continueText(run, packageRoot) {
  const area = run.areas[run.area], step = area.steps.find(step => !run.done[step]);
  const brief = resolve(run.skillDir ?? join(packageRoot ?? PACKAGE_ROOT, 'skills', run.skill), 'steps', `${step ?? 'review'}.md`);
  return `Continue your current step${step ? ` (${step})` : ''} in the ${area.name} area. Read the step brief ${JSON.stringify(brief)} and ${JSON.stringify(join(run.runDir, 'STEP.md'))}, if present. Keep completed work and approvals. Preserve any gate or person question and its required decision. This notice is not approval.`;
}
const deliverContinue = (run, text, p) => p.deliverContinue ? p.deliverContinue(run, text, p) : deliverRequest(run, text, p, true);

function continuationCheckHeld(run, p) {
  const held = progress => progress && ['waiting', 'running', 'unavailable'].includes(progress.state);
  return held((p.readSuiteProgress ?? readSuiteProgress)({cwd: run.root, env: p.env}, p));
}

async function continueResumedChat(run, chat, p, packageRoot) {
  const anchor = chat.resumedAt, latest = readRun(run.runDir);
  const sameTarget = fresh => fresh && runIdentity(fresh) === runIdentity(run)
    && fresh.state === 'running' && !fresh.gate && !openQuestion(fresh) && !continuationCheckHeld(fresh, p)
    && fresh.area === run.area && !layoutClosing(fresh) && !currentChat(fresh)?.closed
    && currentChat(fresh)?.paneId === chat.paneId && currentChat(fresh)?.session?.id === chat.session?.id
    && currentChat(fresh)?.resumedAt === anchor;
  if (!sameTarget(latest) || currentChat(latest).continueAnchor === anchor) return;
  const unchanged = fresh => sameTarget(fresh) && ['state', 'done', 'gate', 'question'].every(key => sameFact(fresh[key], latest[key]));
  if (!conditionalCommit(latest, p, unchanged, fresh => { currentChat(fresh).continueAnchor = anchor; })) return;
  const result = await deliverContinue(readRun(run.runDir), continueText(latest, packageRoot), {
    ...p, packageRoot, deliveryGuard: unchanged,
  });
  if (result.exitCode !== 0) p.say(result.message);
}

// An idle worker uses the existing journal and transport. It never launches another chat.
export const nudgeIdleRun = saveGuard((args, ports) => lockedMutation(args, ports, async (input, ports) => {
  const p = deps(ports), found = await resolveRun(input.ref, {cwd: input.cwd}, p);
  const skipped = () => ({...done(''), recovery: 'skipped'});
  if (!found.run) return found.error ? {...fail(found.error), recovery: 'skipped'} : skipped();
  const run = found.run, chat = currentChat(run), area = run.areas[run.area];
  const owned = fresh => fresh && runIdentity(fresh) === runIdentity(run)
    && validSavedAutomaticOrigin(fresh) && fresh.automaticOrigin.coordinatorId === input.coordinatorId
    && fresh.automaticOrigin.machine === input.machine && samePath(fresh.sourceRoot, input.cwd);
  if (!owned(run) || run.parking || layoutClosing(run) || chat?.closed) return skipped();
  // The saved stop survives a failed alert handoff or process restart. The alert
  // service owns retries and delivered/unconfirmed deduplication on later ticks.
  if (run.state === 'stuck' && run.chatIdleLimit)
    return {...done(run.parkReason), recovery: 'stuck', area: run.chatIdleLimit.area};
  const eligible = fresh => owned(fresh) && fresh.state === 'running' && !fresh.gate && !openQuestion(fresh) && !activeChatFailure(fresh)
    && !continuationCheckHeld(fresh, p)
    && !layoutClosing(fresh) && !currentChat(fresh)?.closed && fresh.area === run.area
    && (!fresh.chatReplacement || ['launched', 'rolledBack', 'ended'].includes(fresh.chatReplacement.phase))
    && currentChat(fresh) && !currentChat(fresh).startUnconfirmed && validSessionId(currentChat(fresh).session?.id)
    && !prOf(fresh, area?.name) && area?.steps.some(step => !fresh.done[step]);
  if (!eligible(run)) return skipped();
  const original = structuredClone(chat), progress = Object.fromEntries(area.steps.filter(step => run.done[step]).map(step => [step, run.done[step]]));
  const unchanged = fresh => eligible(fresh) && sameFact(currentChat(fresh), original)
    && sameFact(fresh.done, run.done) && sameFact(fresh.automaticOrigin, run.automaticOrigin);
  const live = await chatSession(chat, p), at = p.now(), observed = observeIdle(chat, live, at);
  if (!idleAgent(chat, live)) {
    if (!sameFact(chat, observed)) conditionalCommit(run, p, unchanged, fresh => copyObservation(currentChat(fresh), observed));
    return skipped();
  }
  if (await chatHealth({run, chat, live}, p)) return skipped();
  const previous = run.chatIdleNudges?.[area.name];
  const budget = previous && sameFact(previous.progress, progress) ? previous : {progress, count: 0, lastAt: null};
  const since = Math.max(observed.idleSince, budget.lastAt ?? -Infinity);
  if (at < since + IDLE_WAIT_MS) {
    if (!sameFact(chat, observed)) conditionalCommit(run, p, unchanged, fresh => copyObservation(currentChat(fresh), observed));
    return skipped();
  }
  if (budget.count >= 3) {
    const reason = `The ${area.name} agent stayed idle after 3 continue prompts without step progress. Inspect the chat before continuing this run.`;
    const saved = conditionalCommit(run, p, unchanged, fresh => {
      copyObservation(currentChat(fresh), observed);
      fresh.state = 'stuck'; fresh.parkReason = reason; fresh.chatIdleLimit = {area: area.name, at};
    });
    return saved ? {...done(reason), recovery: 'stuck', area: area.name} : skipped();
  }
  const attempt = {...budget, count: budget.count + 1, lastAt: at};
  if (!conditionalCommit(run, p, unchanged, fresh => {
    copyObservation(currentChat(fresh), observed);
    (fresh.chatIdleNudges ??= {})[area.name] = attempt;
  })) return skipped();
  const reserved = readRun(run.runDir);
  const stillCurrent = fresh => eligible(fresh) && sameFact(currentChat(fresh), currentChat(reserved))
    && sameFact(fresh.done, reserved.done) && sameFact(fresh.automaticOrigin, reserved.automaticOrigin)
    && sameFact(fresh.chatIdleNudges?.[area.name], attempt);
  const result = await deliverContinue(reserved, continueText(reserved, input.packageRoot), {
    ...p, packageRoot: input.packageRoot, deliveryGuard: stillCurrent,
    beforeDeliverySubmit: async () => idleAgent(currentChat(reserved), await chatSession(currentChat(reserved), p)),
  });
  return {...result, recovery: result.exitCode === 0 ? 'nudged' : 'skipped'};
}));

// A replacement wait owns its clearing condition, while disk and slot custody survive.
function replaceParkingBlocker(run, blocker, interpreterBatch, interpreterCheck, now) {
  if (!blocker) return;
  // Read current evidence before replacing the old blocker. A person park must
  // never lend a stale interpreter cache to its replacement.
  let wait = blocker.kind === 'interpreter' ? interpreterWaitFor(run) ?? {
    at: run.updatedAt ?? run.startedAt ?? 0, reason: 'The finished prompt check has no saved verdict.', batch: interpreterBatch ?? null, cause: 'unknown'} : null;
  if (blocker.kind === 'interpreter' && interpreterCheck !== undefined) {
    const unchanged = sameFact(run.parking.interpreterGate, run.gate ?? null)
      && sameFact(run.parking.interpreterCheck, interpreterCheck);
    wait = unchanged && run.parking.interpreterWait ? run.parking.interpreterWait : {
      at: Math.max(now, (run.parking.interpreterWait?.at ?? -Infinity) + 1),
      reason: 'The finished prompt check has no saved verdict.', batch: interpreterBatch ?? null, cause: 'unknown'};
    run.parking.interpreterCheck = structuredClone(interpreterCheck);
  } else delete run.parking.interpreterCheck;
  const changed = !sameFact(run.parking.blocker, blocker);
  if (changed) {
    run.parking.blocker = structuredClone(blocker);
    delete run.parking.text;
    delete run.parking.personWait;
    if (blocker.kind === 'person' && (run.gate || openQuestion(run)))
      run.parking.personWait = {gate: run.gate ?? null, question: run.question ?? null};
  }
  if (wait && (changed || !sameFact(run.parking.interpreterWait, wait))) {
    run.parking.interpreterWait = structuredClone(wait);
    run.parking.interpreterGate = structuredClone(run.gate ?? null);
    delete run.parking.text;
  } else if (!wait) {
    delete run.parking.interpreterWait;
    delete run.parking.interpreterGate;
  }
}

export const parkBlockedRun = saveGuard((args, ports) => lockedMutation(args, ports, async (input, ports) => {
  const p = deps(ports), found = await resolveRun(input.ref, {cwd: input.cwd}, p), run = found.run;
  const skipped = reason => ({...done(''), recovery: 'skipped', ...(reason ? {reasonCounts:{[reason]:1}} : {})});
  if (!run || ended(run) || !validSavedAutomaticOrigin(run)
    || run.automaticOrigin.machine !== input.machine
    || !samePath(run.sourceRoot, input.cwd) || explicitlyStopped(run, p) || ['waking', 'releasing'].includes(run.parking?.phase)) return skipped();
  if (['area-end', 'run-end', 'budget', 'cancel'].includes(currentChat(run)?.closed?.reason)) return skipped();
  if (!run.layout?.workspaceId) return skipped('not-pdd-created');
  if (input.expected && ['runId', 'root', 'state', 'area', 'gate', 'question', 'done', 'blockedOn', 'runtimeWait', 'parkReason', 'stuckCause', 'environmentRetry', 'automaticOrigin', 'progressAt', 'updatedAt', 'chatIdleLimit', 'chatResumeLimit']
    .some(key => !sameFact(run[key], input.expected[key]))) return skipped();
  if (input.idleGraceMs !== undefined && (!currentParkingOwner(run, p, {allowOlder:true}) || !idleParkingBlocker(run, p.now(), input.idleGraceMs))) return skipped();
  if (run.automaticOrigin.coordinatorId !== input.coordinatorId) {
    const owner = currentParkingOwner(run, p, {allowOlder:true});
    if (owner?.coordinatorId !== input.coordinatorId) return skipped('claim-unavailable');
    try { if (!await recoverParkingOwner(run, owner, p)) return skipped(ended(run) ? 'claim-transferred' : 'claim-unavailable'); }
    catch { return skipped('claim-unavailable'); }
  }
  if (run.parking?.phase === 'parked') {
    commitRun(run, p, fresh => {
      replaceParkingBlocker(fresh, input.blocker, input.interpreterBatch, input.interpreterCheck, p.now());
      if (continuationCheckHeld(fresh, p)) fresh.parking.checkHeld = true;
      else delete fresh.parking.checkHeld;
    });
    return {...done(''), recovery: 'parked'};
  }
  const retainClosing = reason => {
    if (run.parking?.phase === 'closing') commitRun(run, p, fresh => {
      fresh.parking.closeReasons = {[reason]: 1, ...(p.now() - fresh.parking.at >= 60_000 ? {'closing-retry': 1} : {})};
      fresh.parking.closeAttemptAt = p.now();
      fresh.parking.closeAttempts = (fresh.parking.closeAttempts ?? 0) + 1;
    });
    return skipped(reason);
  };
  if (continuationCheckHeld(run, p)) return retainClosing('check-busy');
  const activeChat = currentChat(run), live = activeChat ? await chatSession(activeChat, {...p, run}) : null;
  const agentBusy = live?.alive && !['idle','done'].includes(live.status);
  if (agentBusy && run.parking) return retainClosing('agent-busy');
  if (!input.blocker) return skipped();
  const snapshot = {state: run.state, area: run.area, gate: run.gate, question: run.question, done: run.done,
    blockedOn: run.blockedOn, runtimeWait: run.runtimeWait, parkReason: run.parkReason, stuckCause: run.stuckCause, environmentRetry: run.environmentRetry, automaticOrigin: run.automaticOrigin,
    chatIdleLimit: run.chatIdleLimit, chatResumeLimit: run.chatResumeLimit};
  let cleanupUpdatedAt = run.updatedAt, cleanupProgressAt = run.progressAt;
  const unchanged = fresh => fresh && fresh.runId === run.runId && fresh.root === run.root && !ended(fresh)
    && fresh.updatedAt === cleanupUpdatedAt && fresh.progressAt === cleanupProgressAt && (input.idleGraceMs === undefined || currentParkingOwner(fresh, p))
    && Object.entries(snapshot).every(([key, value]) => sameFact(fresh[key], value));
  if (!agentBusy && !conditionalCommit(run, p, unchanged, fresh => {
    fresh.parking ??= {at: p.now(), blocker: input.blocker, phase: 'closing', closeReasons: {'cleanup-pending': 1},
      ...(input.blocker.kind === 'person' && (run.gate || openQuestion(run))
        ? {personWait: {gate: run.gate ?? null, question: run.question ?? null}} : {})};
    replaceParkingBlocker(fresh, input.blocker, input.interpreterBatch, input.interpreterCheck, p.now());
  })) return skipped();
  const parked = readRun(run.runDir), copy = structuredClone(parked);
  cleanupUpdatedAt = parked.updatedAt; cleanupProgressAt = parked.progressAt;
  const result = await closeFinishedChats(copy, {...p, force: !agentBusy, graceMs: 0, reason: 'park', beforeClose: async () => {
    const fresh = readRun(run.runDir);
    if (!unchanged(fresh) || !currentParkingOwner(fresh, p) || continuationCheckHeld(fresh, p))
      throw Object.assign(Error('Parking custody changed before close'), {code: 'workflow_progress_refused'});
  }, checkpoint: async (chat, layout) => {
    if (continuationCheckHeld(readRun(run.runDir), p)) throw Object.assign(Error('Check process custody changed'), {code: 'workflow_progress_refused'});
    if (!conditionalCommit(parked, p, fresh => unchanged(fresh) && fresh.parking?.at === parked.parking?.at, fresh => {
      if (chat) {
        const target = fresh.chats.find(item => sameChat(item, chat));
        if (!target || target.terminalId !== chat.terminalId) throw Object.assign(Error('Parking chat changed'), {code: 'workflow_progress_refused'});
        Object.assign(target, structuredClone(chat));
      }
      if (layout) fresh.layout = structuredClone(layout);
    })) throw Object.assign(Error('Parking custody changed'), {code: 'workflow_progress_refused'});
    const saved = readRun(run.runDir);
    cleanupUpdatedAt = saved.updatedAt; cleanupProgressAt = saved.progressAt;
  }});
  if (agentBusy) {
    const kept = [...result.kept, {area: activeChat.area, reason: 'agent-busy'}];
    conditionalCommit(parked, p, unchanged, fresh => {fresh.cleanupKept = kept;});
    return {...done(result.warnings.join('\n')), recovery: 'skipped', reasonCounts: {...result.reasonCounts, 'agent-busy': 1}};
  }
  const cleaned = readRun(run.runDir);
  const closed = !result.kept.length && cleaned?.layout?.phase === 'closed'
    && cleaned.chats.every(chat => Number.isFinite(chat.closed?.confirmedAt));
  conditionalCommit(parked, p, fresh => unchanged(fresh) && fresh.parking?.at === parked.parking.at, fresh => {
    fresh.cleanupKept = result.kept;
    fresh.parking.closeAttemptAt = p.now();
    fresh.parking.closeAttempts = (fresh.parking.closeAttempts ?? 0) + 1;
    if (closed) {fresh.parking.phase = 'parked'; delete fresh.parking.closeReasons;}
    else fresh.parking.closeReasons = {
      ...(Object.keys(result.reasonCounts).length ? result.reasonCounts : {'cleanup-unconfirmed': 1}),
      ...(p.now() - fresh.parking.at >= 60_000 ? {'closing-retry': 1} : {})};
  });
  return {...done(result.warnings.join('\n')), recovery: closed ? 'parked' : 'skipped', reasonCounts: result.reasonCounts};
}));

// Keep run custody through the irreversible release. Unknown effects retain a
// durable reservation, so a later tick retries instead of resuming unowned work.
export const releaseParkedRun = saveGuard((args, ports) => lockedMutation(args, ports, async (input, ports) => {
  const p = deps(ports), found = await resolveRun(input.ref, {cwd: input.cwd}, p), run = found.run;
  const skipped = () => ({...done(''), recovery: 'skipped'});
  const current = fresh => fresh && fresh.runId === input.runId && !ended(fresh)
    && fresh.parking?.at === input.at && ['parked', 'releasing'].includes(fresh.parking.phase)
    && validSavedAutomaticOrigin(fresh) && fresh.automaticOrigin.coordinatorId === input.coordinatorId
    && fresh.automaticOrigin.machine === input.machine && samePath(fresh.sourceRoot, input.cwd)
    && sameFact(fresh.automaticOrigin, run?.automaticOrigin) && fresh.root === run?.root
    && !continuationCheckHeld(fresh, p);
  if (!current(run) || typeof p.releaseParkedClaim !== 'function') return skipped();
  if (!conditionalCommit(run, p, current, fresh => {fresh.parking.phase = 'releasing';})) return skipped();
  if (!current(readRun(run.runDir))) return skipped();
  const remote = await p.releaseParkedClaim(readRun(run.runDir));
  if (remote?.state !== 'released' || !current(readRun(run.runDir))) return skipped();
  const local = await releaseIssueClaim({cwd: input.cwd, issueNumber: run.number, runId: run.runId}, p);
  if (local.state !== 'released' || !current(readRun(run.runDir))) return skipped();
  const result = await cancelRunCommand(input, {...p, claimReleased: true});
  return {...result, recovery: result.exitCode === 0 ? 'released' : 'skipped'};
}));

export const wakeParkedRun = saveGuard((args, ports) => lockedMutation(args, ports, async (input, ports) => {
  const p = deps(ports), found = await resolveRun(input.ref, {cwd: input.cwd}, p), run = found.run;
  const skipped = () => ({...done(''), recovery: 'skipped'});
  if (!run || !validSavedAutomaticOrigin(run) || run.automaticOrigin.coordinatorId !== input.coordinatorId
    || run.automaticOrigin.machine !== input.machine || !samePath(run.sourceRoot, input.cwd)
    || run.parking?.at !== input.at || !['parked', 'waking'].includes(run.parking.phase)) return skipped();
  if (run.cancelled?.state === 'handed-over') return fail(await chatContinuationOwnership(run, p));
  if (ended(run) || explicitlyStopped(run, p)) return skipped();
  const ownership = await chatContinuationOwnership(run, p);
  if (ownership) return fail(ownership);
  if (input.expectedBlocker) {
    if (!sameFact(run.parking.blocker, input.expectedBlocker)
      || run.parking.phase === 'parked' && !sameFact(blockerFor(run) ?? run.parking.blocker, input.expectedBlocker)
      || continuationCheckHeld(run, p) || run.parking.phase === 'parked' && !await p.parkingBlockerCleared?.(run)) return skipped();
    const latest = readRun(run.runDir);
    if (!latest || latest.runId !== run.runId || latest.parking?.at !== input.at
      || !sameFact(latest.parking.blocker, input.expectedBlocker)
      || !['parked', 'waking'].includes(latest.parking.phase)
      || !sameFact(latest.automaticOrigin, run.automaticOrigin)
      || latest.parking.phase === 'parked' && !sameFact(blockerFor(latest) ?? latest.parking.blocker, input.expectedBlocker)
      || continuationCheckHeld(latest, p)) return skipped();
  }
  for (const reply of parkedReplyEntries(run, p)) if (reply.personRetry) {
    const refusal = await personRetryRefusal(readRun(run.runDir), reply.text, p, true);
    if (refusal) return {...fail(refusal), recovery: 'skipped'};
  }
  const text = run.parking.text ?? input.text;
  const inferredGate = run.parking.blocker.kind === 'interpreter' && run.parking.interpreterWait && sameFact(run.gate, run.parking.interpreterGate) && run.gate?.kind === 'approve-pr' && !openQuestion(run);
  if (text && (RUNTIME_WAKE_TAG.test(text) || isEnvironmentWake(text)) && (run.gate || openQuestion(run)) && !inferredGate) return skipped();
  commitRun(run, p, fresh => {
    if (fresh.parking?.at !== input.at) throw Object.assign(Error('Park changed'), {code: 'workflow_progress_refused'});
    if (fresh.parking.phase === 'parked') {
      if (fresh.parking.blocker.kind === 'pdd-route') {
        const route = routeQuestionFor(fresh);
        if (route && fresh.question?.text === route.question && !fresh.question.answeredAt) delete fresh.question;
        delete fresh.routeWait;
      }
      endRuntimeWait(fresh); delete fresh.blockedOn;
      // Consume the accepted stop before resume/delivery can save a new one.
      // Environment retry delivery still needs its cause for validation.
      if (fresh.parking.blocker.kind !== 'environment') {
        delete fresh.parkReason; delete fresh.stuckCause;
      }
    }
    fresh.parking.phase = 'waking';
    if (text) fresh.parking.text = text;
    if (fresh.parking.blocker.kind === 'pdd-route' && (fresh.gate || openQuestion(fresh))) fresh.state = 'waiting';
    else if (fresh.parking.blocker.kind !== 'environment' && (inferredGate || !fresh.gate && !openQuestion(fresh) || ['pdd', 'pdd-route'].includes(fresh.parking.blocker.kind))) fresh.state = 'running';
  });
  const result = await openRunLocked({...input, automaticResume: {...input, parked: true}}, p);
  if (result.exitCode !== 0) return {...result, recovery: 'skipped'};
  const fresh = readRun(run.runDir), chat = currentChat(fresh);
  if (!chat || chat.startUnconfirmed || !validSessionId(chat.session?.id)) return skipped();
  const deliveryPorts = {...p, packageRoot: input.packageRoot, deliveryGuard: latest => latest.parking?.at === input.at && latest.parking.phase === 'waking' && sameFact(latest.automaticOrigin, run.automaticOrigin)};
  const replies = parkedReplyEntries(fresh, p);
  if (replies.length) {
    for (const reply of replies) {
      const delivered = await deliverRequest(fresh, reply.text, {...deliveryPorts, requestKey: reply.key});
      if (delivered.exitCode !== 0) return {...delivered, recovery: 'skipped'};
    }
  } else {
    const notice = text ?? continueText(fresh, input.packageRoot);
    const delivered = !text && (fresh.gate || openQuestion(fresh)) ? done('') : await deliverRequest(fresh, notice, {...deliveryPorts, requestKey: `park:${input.at}`}, !text || fresh.parking.blocker.kind !== 'environment');
    if (delivered.exitCode !== 0) return {...delivered, recovery: 'skipped'};
  }
  commitRun(fresh, p, latest => {if (latest.parking?.at === input.at) delete latest.parking;});
  return {...done('Resumed the saved parked session.'), recovery: 'resumed'};
}));

export const resumeStoppedRun = saveGuard(async ({ref, cwd, packageRoot, coordinatorId, machine}, ports) => {
  const args = {ref, cwd, packageRoot};
  const result = await lockedMutation(args, ports, (input, p) => openRunLocked({...input, automaticResume: {coordinatorId, machine}}, p));
  return result.recovery ? result : {...result, recovery: result.exitCode === 0 ? 'resumed' : 'skipped'};
});

async function startRunCommand(args, ports = {}) {
  if (Object.hasOwn(args, 'automaticOrigin')) return fail('Invalid automatic start context.');
  const p = deps(ports);
  const nativeSession = /[\\/]sessions[\\/]([^\\/]+)[\\/][^\\/]+$/.exec(String(p.env.HERDR_SOCKET_PATH ?? ''))?.[1];
  const recoverCoordinator = args.coordinator === undefined && !Object.hasOwn(p.env, 'PDD_AUTOPILOT_CONTEXT') && nativeSession === 'pdd-autopilot';
  if (args.coordinator === undefined && !Object.hasOwn(p.env, 'PDD_AUTOPILOT_CONTEXT') && !recoverCoordinator) return startRunUnlocked(args, ports);
  if (args.coordinator !== undefined && !validAutomaticContext(args.coordinator)) return fail('Invalid automatic start context.');
  if (Object.hasOwn(p.env, 'PDD_AUTOPILOT_CONTEXT')) {
    try { if (!validAutomaticContext(JSON.parse(p.env.PDD_AUTOPILOT_CONTEXT))) return fail('Invalid automatic start context.'); }
    catch { return fail('Invalid automatic start context.'); }
  }
  let context, release;
  try {
    context = await gitContext(args.cwd, p);
    if (!context) return fail('Run this inside a Git checkout of the repository that has the issue.');
    let recoveryFile, root;
    if (recoverCoordinator) {
      root = realpathSync(context.toplevel);
      const id = createHash('sha256').update(root).digest('hex').slice(0, 20);
      const folder = ports.autopilotStateRoot ?? join(p.env.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
      recoveryFile = join(folder, `${id}.json`);
      let selected;
      try { selected = JSON.parse(readFileSync(recoveryFile, 'utf8')); } catch { selected = null; }
      if (!selected || !p.env.HERDR_PANE_ID || selected.paneId !== p.env.HERDR_PANE_ID)
        return await startRunUnlocked(args, ports);
    }
    const dir = join(context.commonDir, 'pdd');
    mkdirSync(dir, { recursive: true });
    release = acquireRunLock(dir, 'autopilot-admission.lock');
    if (recoverCoordinator) {
      let state;
      try { state = JSON.parse(readFileSync(recoveryFile, 'utf8')); } catch { return fail('Automatic start unavailable: current coordinator state is missing.'); }
      const coordinator = {version:'pdd.autopilot-coordinator.v1',repository:state.repo,coordinatorId:state.coordinatorId,machine:state.machine,activation:state.activatedAt,...(state.runs === undefined ? {} : {runs:state.runs})};
      if (state.enabled !== true || state.paneId !== p.env.HERDR_PANE_ID || state.ownerLaunch?.paneId !== state.paneId || !equalFact(state.ownerLaunch?.coordinator, coordinator) || !validAutomaticContext(coordinator) || realpathSync(state.cwd) !== root)
        return fail('Automatic start unavailable: current coordinator ownership does not match.');
      args = {...args,coordinator};
    }
    return await startRunUnlocked(args, ports);
  } catch { return fail('Automatic start is unavailable: admission lock could not be acquired.'); }
  finally { release?.(); }
}

// A completed registered turn can yield capacity without claiming the chat process exited.
async function yieldAutomaticCapacityCommand({ ref, cwd }, ports) {
  const p = deps(ports);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  if (ports.expectedCompletion) {
    const expected = ports.expectedCompletion, chat = currentChat(run);
    if (run.runId !== expected.runId || run.areas?.[run.area]?.name !== expected.area || chat?.paneId !== expected.paneId || launchAnchor(chat) !== expected.startAnchor)
      return fail('Capacity handoff refused: completion identity changed.');
  }
  if (!run.automaticOrigin) return fail('Capacity handoff requires a saved automatic run.');
  const reason = run.state === 'completed'
    ? (validSavedAutomaticOrigin(run) ? null : 'Capacity handoff requires a valid saved automatic origin and repository association.')
    : await continuationOwnership(run, cwd, p);
  if (reason) return fail(reason);
  if (!['waiting', 'paused', 'stuck', 'question', 'completed', 'cancelled'].includes(run.state))
    return fail('Capacity handoff requires a waiting or ended run.');
  const chat = currentChat(run);
  if (!chat || chat.startUnconfirmed || run.chatFailure || run.chatReplacement && !['launched', 'rolledBack', 'ended'].includes(run.chatReplacement.phase))
    return fail('Capacity handoff cannot confirm the current chat has stopped.');
  const live = await chatSession(chat, {...p, run}), now = p.now();
  const own = sessionEvidenceDue(chat, live, now) && !observedSession(chat, chat.agent ?? run.agent)
    ? await ownSession({ run, chat, since: launchAnchor(chat), ports: p }) : null;
  const observed = observeLifecycle(chat, live, now, chat.agent ?? run.agent, own?.kind === 'match' ? own.id : null);
  const completedTurn = live.alive && live.status === 'done' && observed.exact;
  const endedChat = !live.alive && ['agent_not_found', 'server_not_running', ...(chat.closed ? ['pane_not_found','tab_not_found'] : [])].includes(live.code) && ['ended', 'failed'].includes(observed.state);
  if (!completedTurn && !endedChat)
    return fail('Capacity handoff cannot confirm the current chat has stopped.');
  if (['completed', 'cancelled'].includes(run.state)) {
    const released = await releaseIssueClaim({ cwd: run.sourceRoot, runId: run.runId, issueNumber: run.number }, p.commandPorts);
    if (released.state !== 'released') return fail(`Capacity handoff could not release the issue allocation: ${released.message}`);
  }
  const request = p.requestAutopilotCompletion ?? (await import('./autopilot-launcher.mjs')).requestAutopilotCompletion;
  p.releaseRunLock?.();
  const result = await request({ cwd: run.sourceRoot, env: p.env }, ports);
  if (result.state === 'reconciled') return done('Capacity handoff reconciled with Autopilot.');
  if (result.state === 'inactive') return done('Capacity handoff complete; Autopilot is inactive.');
  if (result.state === 'busy') return fail('Capacity handoff could not reconcile: Autopilot is busy.');
  return fail('Capacity handoff could not confirm Autopilot reconciliation.');
}
export const yieldAutomaticCapacity = saveGuard(yieldAutomaticCapacityCommand);

export const startRun=saveGuard(startRunCommand);

export const recordEvidence=saveGuard(recordEvidenceCommand);
export const associateEvidenceWorkspace=saveGuard(associateEvidenceWorkspaceCommand);

export const stepDone=saveGuard(stepDoneCommand);

// The run locks cover authorization and dispatch. An interrupted send is consumed, never replayed.
export const resendChecks = saveGuard(async ({refs, cwd, said, packageRoot = PACKAGE_ROOT}, ports = {}) => {
  const p = deps(ports), releases = [], selected = [];
  try {
    if (!Array.isArray(refs) || !refs.length || new Set(refs.map(String)).size !== refs.length) return fail('Select distinct run numbers.');
    for (const ref of refs) {
      const found = await resolveRun(ref, {cwd}, p);
      if (found.error) return fail(found.error);
      selected.push(found.run);
    }
    for (const run of [...selected].sort((a,b) => a.runDir.localeCompare(b.runDir))) releases.push(acquireRunLock(run.runDir));
    const checks = [];
    for (const run of selected) {
      Object.assign(run, readRun(run.runDir));
      if (!['paused','waiting','stuck'].includes(run.state)) return fail(`Run #${run.number} is not stopped. Nothing was resent.`);
      const check = readOwnResults(run,p).find(row => row.kind === 'pdd test');
      const lost = check && savedLostCheck(check.batch, {env:p.env, root:run.root});
      if (!lost) return fail(`Run #${run.number} has no stopped lost-verdict check with valid call caps. Nothing was resent.`);
      if ((run.checkResends ?? []).some(row => row.oldBatch === lost.batch && row.state !== 'authorized'))
        return fail(`Run #${run.number}, batch ${lost.batch}, already consumed its resend decision. Nothing was resent.`);
      const saved = JSON.parse(readFileSync(join(p.env.PDD_STATE_DIR || join(p.env.HOME || homedir(), '.pdd','runtime'), 'batches',lost.batch,'batch.json'),'utf8'));
      const capture = (p.captureSource ?? captureSource)(run.root, {tests:[...new Set(saved.rows.filter(row=>!row.unsent).map(row=>row.test))],appMap:null,excludeFixtureProjects:saved.exclude_fixture_projects === true});
      if (capture.sha256 !== lost.sourceSha256) return fail(`Run #${run.number}: source changed. Nothing was resent.`);
      const strict = readApprovalPolicy({root:run.sourceRoot},p).strictApprovals;
      if (strict && (said !== undefined || !p.isTTY || isAgentSession(p.env))) return fail(`Run #${run.number} requires a person terminal for resend.`);
      checks.push({run,lost,saved});
    }
    const listing = checks.map(({run,lost}) => `#${run.number}: batch ${lost.batch}; earlier AI calls: ${lost.cost.calls ?? `unknown (at least ${lost.cost.knownCalls})`}`).join('\n');
    p.say(listing);
    let words = null;
    if (said !== undefined) words = await readSaidWords(said,p);
    else if (!p.isTTY || isAgentSession(p.env)) return fail(`${listing}\nA person must decide: use pdd workflow resend ${refs.join(' ')} --said - with their nonblank words.`);
    else if (!await confirm(p, `${listing}\nResend these lost checks once? [y/N] `)) return done('Nothing was resent.');
    const unchanged = ({run,lost,saved}) => {
      const latest=readOwnResults(run,p).find(row=>row.kind==='pdd test');
      const source=(p.captureSource ?? captureSource)(run.root,{tests:[...new Set(saved.rows.filter(row=>!row.unsent).map(row=>row.test))],appMap:null,excludeFixtureProjects:saved.exclude_fixture_projects === true});
      return latest?.batch===lost.batch && source.sha256===lost.sourceSha256;
    };
    if (!checks.every(unchanged)) return fail('The saved batch or source changed during the decision. Nothing was resent.');
    const id = p.randomUUID(), at = p.now();
    for (const {run,lost} of checks) commitRun(run,p,latest => {
      (latest.checkResends ??= []).push({id,at,actor:approvalActor(p.env),route:said === undefined?'terminal':'said',words,
        oldBatch:lost.batch,oldCost:lost.cost,tests:lost.tests,maxCalls:lost.maxCalls,state:'authorized',newBatch:null});
    });
    const lines = [listing];
    let exitCode = 0;
    for (const item of checks) {
      const {run,lost}=item;
      if (!unchanged(item)) return fail('The saved batch or source changed. No further checks were sent.');
      const update = fields => commitRun(run,p,latest=>Object.assign(latest.checkResends.find(row=>row.id===id),fields));
      update({state:'sending'});
      let output;
      try { output = await p.execFile(process.execPath,[join(packageRoot,'bin','pdd.mjs'),'test',...lost.tests,'--json','--max-calls',String(lost.maxCalls),'--cache-clear'],{cwd:run.root,env:{...p.env,PDD_CHECK_SINGLE_ATTEMPT:'1'}}); }
      catch (error) { output = error; }
      let report;
      try { report = JSON.parse(output.stdout); } catch { /* An uncertain reply never allows a second send. */ }
      const newer = readOwnResults(run,p).find(row=>row.kind==='pdd test' && row.batch!==lost.batch && row.at>=at);
      const newBatch = newer?.batch ?? null;
      const valid = report?.batch === newBatch && newBatch !== null && Array.isArray(report.rows) && report.rows.length
        && lost.tests.every(path=>report.rows.some(row=>row.test===path));
      const verdict = valid && report.rows.every(row=>['passed','failed'].includes(row.state));
      update({newBatch,state:verdict?'verdict':valid?'no-verdict':'uncertain',finishedAt:p.now()});
      lines.push(`#${run.number}: ${newBatch ? `batch ${newBatch}` : 'new batch unknown'}; ${verdict?'verdict saved':'no verdict; stop and give this receipt to the interpreter owner'}.`);
      if (!verdict) return {exitCode:1,message:lines.join('\n')};
      if (report.rows.some(row=>row.state==='failed')) exitCode = 1;
    }
    return {exitCode,message:lines.join('\n')};
  } catch (error) { return fail(`Resend stopped: ${failureReason(error)}. No automatic retry.`); }
  finally { for (const release of releases.reverse()) release(); }
});

export const approveRun=saveGuard(approveRunCommand);

export const askPerson=saveGuard(askPersonCommand);

export const cancelRun=saveGuard(async (args, ports = {}) => {
  const p = deps(ports), found = await resolveRun(args.ref, {cwd: args.cwd}, p);
  if (!found.run || found.error || !validSavedAutomaticOrigin(found.run)) return cancelRunCommand(args, ports);
  let release;
  try {
    release = acquireRunLock(found.run.runDir);
    const latest = readRun(found.run.runDir);
    if (!latest || runIdentity(latest) !== runIdentity(found.run))
      return fail('The selected workflow run changed. Retry cancellation.');
    return await cancelRunCommand(args, ports, runIdentity(latest));
  } catch (error) {
    if (error.code === 'run_busy') return fail(error.message);
    throw error;
  } finally { release?.(); }
});

export const runStatus=saveGuard(async(options,ports)=>{
  ports = { ...ports, skipCostSessions: true };
  try{return await runStatusCommand(options,ports);}
  catch(error){
    if(error?.code==='workflow_run_save_failed'&&error.cause?.code==='workflow_run_busy')return runStatusCommand(options,ports,true);
    throw error;
  }
});

export const openRun=saveGuard(openRunCommand);

export const showStoryCard=saveGuard(showStoryCardCommand);

// Canonical, read-only association admission for native workspace consumers.
// The existing registered authority above remains the only permission rule.
export function readEvidenceEligibility({root,producerRoot,tests,source_sha256,runId=null,stage=null},ports={}){
  const canonical=ports.realpath??realpathSync,capture=ports.captureSource??captureSource;
  let result={state:'unavailable',reason:'source or ownership unavailable',runId:null,repo:null,producerRoot:null,tests:[],stage:null,sourceAnchor:null,source_sha256:source_sha256??null};
  try{
    root=canonical(root);producerRoot=canonical(producerRoot);tests=evidenceTests(tests);
    result={...result,producerRoot,tests};
    if(!/^[a-f0-9]{64}$/.test(source_sha256??''))return{...result,state:'ineligible',reason:'original selected source identity is missing'};
    const runs=(ports.allRuns??allRuns)({cancelled:true},ports);
    // Only the consumer's owned source/run may authorize an alternate producer.
    const candidates=[];
    for(const run of runs){
      if(!run||typeof run.root!=='string'||canonical(run.root)!==root)continue;
      for(const association of run.evidenceAssociations??[]){
        if(association.workspaceRoot===producerRoot&&selectionEqual(association.tests,tests)&&association.source_sha256===source_sha256)candidates.push({run,association});
      }
    }
    if(candidates.length){
      if(candidates.length!==1)return{...result,state:'ineligible',reason:'workspace association is ambiguous'};
      const {run,association:a}=candidates[0];
      if(runId!==null&&runId!==run.runId||stage!==null&&stage!==a.stage)return{...result,state:'ineligible',reason:'saved run or stage disagrees with the owned association'};
      // Before-the-fix evidence is historical: only a caller that names that stage may read it.
      if(a.stage==='before'&&stage!=='before')return{...result,state:'ineligible',reason:'before-the-fix evidence is historical; it is read only through its registered import'};
      const inspect=ports.inspectRepository??(path=>{const git=spawnSync('git',['rev-parse','--path-format=absolute','--git-common-dir'],{cwd:path,encoding:'utf8'});if(git.status!==0)throw Error('repository ownership unavailable');return canonical(git.stdout.trim());});
      const common=inspect(root);
      if(canonical(run.commonDir)!==common||canonical(run.runDir)!==canonical(runDirFor(common,run.number))||typeof run.repo!=='string'||!run.runId)return{...result,state:'ineligible',reason:'run ownership is missing or contradictory'};
      checkedAssociation(run,a,capture);
      return{state:'eligible',reason:null,runId:run.runId,repo:run.repo,producerRoot,tests,stage:a.stage,sourceAnchor:{...a.sourceAnchor},source_sha256};
    }
    if(runId!==null||stage!==null&&stage!=='current')return{...result,state:'ineligible',reason:'saved run/stage has no matching owned association'};
    if(root!==producerRoot)return{...result,state:'ineligible',reason:'alternate producer has no owned workspace association'};
    if(capture(root,{tests,appMap:null}).sha256!==source_sha256)return{...result,state:'ineligible',reason:'the exact selected source has changed'};
    return{state:'eligible',reason:null,runId:null,repo:null,producerRoot,tests,stage:'current',sourceAnchor:{root,head:null},source_sha256};
  }catch(error){return{...result,reason:oneLine(error.message??error)};}
}

// An explicit full-suite command uses the machine queue, never the run mutation lock.
export function runSuite(input, ports = {}) { return runTestSuite(input, ports); }

// Local cost observations never advance the workflow.
export async function runCosts({ ref, cwd, input }, ports = {}) {
  const p = deps(ports), found = await resolveRun(ref, { cwd }, p);
  if (!found.run) return fail(found.error);
  try {
    const run = updateRunCosts(found.run.runDir, latest => input === undefined ? latest : applyCostMeasurement(latest, input, p.now()), p);
    return done(JSON.stringify(costReport([run], p.now()).runs[0], null, 2));
  } catch (error) { return { exitCode: 2, message: error.message }; }
}
