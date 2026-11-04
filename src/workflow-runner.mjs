// Generated from prompts/cli/workflow-runner.prompt.md (sha256: f0309eab9f5595caa6aa8ef58b3985008448472b004e3f4e51f8bbad0c5e55de).
import { approvalActor, readSaidWords, readApprovalPolicy, readPromptApprovals, recordPromptApproval } from './approval-policy.mjs';
import { approvePromptText } from './prompt-approve.mjs';
import { execFile as execFileCallback } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { constants, openSync, closeSync, fsyncSync, unlinkSync, existsSync, lstatSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, renameSync, rmSync, writeFileSync } from 'node:fs';

import * as nativeDeliveryFiles from 'node:fs';
import { homedir, hostname, tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { createInterface } from 'node:readline/promises';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { PUBLIC_COMMAND_ROUTES } from './command-catalog.mjs';
import { readWorkflowAreas } from './workflow-areas.mjs';
import { resolveWorkflowIssue, prepareWorkflowPr, publishWorkflowPr, readWorkflowPrStatus } from './workflow-github.mjs';
import { allocateIssueWorktree, releaseIssueClaim } from './workflow-worktree.mjs';
import { allRuns, currentChat, gitContext, listRuns, readRun, readRunOwnership, resolveRun, runDirFor, runForWorktree, updateRun, writeRun } from './workflow-runs.mjs';
import { startChat, sendToChat, herdrCommand, chatSession, openChat, restartChat, validSessionId, closeChats, expandHome, homeVariable, isFolder, observeLifecycle, applyLifecycle, launchAnchor, sessionEvidenceDue, ownSession, observedSession, START_GRACE_MS } from './workflow-chat.mjs';
import { captureSource, findTests, gitFiles, interfaceBlocks, interfaceSchemaProblems, proseSha256 } from './runtime-preflight.mjs';
import { storyLines, PROMPT_TESTS_LABEL, PROMPT_TESTS_WORDS } from './runtime-output.mjs';
import { PDD_HERDR_SESSION } from './workflow-herdr-layout.mjs';
import { causeText } from './runtime-output.mjs';
import { preparePrEvidence } from './workflow-pr-evidence.mjs';
import { validateProofRecord } from './workflow-prove.mjs';
import { collectTestInventory } from './workflow-inventory.mjs';
import {adoptReplayCorpus,REPLAY_POLICY,sourceFingerprint as gitFingerprint,pinReplayVectors,readReplayEvidence,formatReplayEvidence} from './workflow-replay.mjs';

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

function deps(ports = {}) {
  const env = ports.env ?? process.env;
  const execFile = ports.execFile ?? ((file, args, options = {}) => execute(file, args, { ...options, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 }));
  return { ...ports, env, execFile, commandPorts: ports.execFile ? { execFile: ports.execFile } : {}, now: ports.now ?? Date.now, randomUUID: ports.randomUUID ?? randomUUID,
    isTTY: ports.isTTY ?? Boolean(process.stdin.isTTY && process.stderr.isTTY), say: ports.say ?? (() => {}) };
}
// This run lock is independent of the shared Herdr layout lock. Never wait on a live owner.
const lockProblem = () => Object.assign(Error('Another open operation holds this run, or its ownership cannot be verified. Wait for it to finish and retry.'), { code: 'run_busy' });
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
function acquireRunLock(runDir) {
  const path = join(runDir, 'chat-replacement.lock'), claim = `${path}.claim`, owner = { pid: process.pid, token: randomUUID() };
  const create = () => {
    const fd = openSync(path, 'wx', 0o600);
    try { writeFileSync(fd, JSON.stringify(owner)); fsyncSync(fd); } finally { closeSync(fd); }
  };
  try { create(); } catch (error) {
    if (error.code !== 'EEXIST') throw lockProblem();
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
async function lockedMutation(args, ports, action) {
  const p = deps(ports), found = await resolveRun(args.ref, { cwd: args.cwd }, p);
  if (!found.run) return action(args, ports);
  let release;
  try { release = acquireRunLock(found.run.runDir); return await action(args, { ...ports, releaseRunLock: release }); }
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
// Revalidate command authority at local commits and before consequential effects.
function protectProgress(run,p,{approval=false}={}) {
  const selectedState=run.state,selectedGate=structuredClone(run.gate ?? null),selectedArea=run.area;
  const check=latest=>{
    if(ended(latest) && !(selectedState==='completed'&&latest.state==='completed'&&selectedGate?.kind==='ask-code'))
      throw Object.assign(Error(`The run ended (${latest.state}). Stop working on it.`),{code:'workflow_progress_refused'});
    if(approval && (latest.area!==selectedArea || Boolean(latest.gate)!==Boolean(selectedGate) || (selectedGate?.id && latest.gate?.id!==selectedGate.id) || ['area','kind','at'].some(key=>latest.gate?.[key]!==selectedGate?.[key])))
      throw Object.assign(Error('The gate changed, look again.'),{code:'workflow_progress_refused'});
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
  return ()=>{approval=false;};
}
const sameGate = (current, selected) => (!current || !selected) ? current === selected : ['area','kind','at'].every(key=>current[key]===selected[key]) && (!selected.id || current.id===selected.id);
const equalFact = (a,b) => JSON.stringify(a ?? null) === JSON.stringify(b ?? null);
// The same saved record regardless of key order.
const canonical = value => Array.isArray(value) ? value.map(canonical) : value && typeof value === 'object'
  ? Object.fromEntries(Object.keys(value).sort().map(key => [key, canonical(value[key])])) : value;
const sameFact = (a,b) => JSON.stringify(canonical(a ?? null)) === JSON.stringify(canonical(b ?? null));
const lastChat = (run, area) => [...(run.chats ?? [])].reverse().find(chat => chat.area === area);
// The chat identity and lifecycle fields that one observation may change.
const CHAT_OBSERVATION = ['tabId', 'paneId', 'terminalId', 'session', 'resumedAt', 'startUnconfirmed', 'state', 'evidence', 'code'];
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
    const tracked = (await rawGit(p, run.root, 'diff', '--name-only', '-z', run.baseSha)).split('\0');
    const untracked = (await rawGit(p, run.root, 'ls-files', '--others', '--exclude-standard', '-z')).split('\0');
    return [...new Set([...tracked, ...untracked].filter(Boolean))];
  } catch (error) { if (strict) throw error; return []; }
}
const isScenario = text => JSON.parse(text)?.schema_version === 'prompt-runtime.program-scenario.v1';
async function scenarioInventory(run, p) {
  const paths = [];
  const saved=new Set(run.replayBaseline?.vectors?.map(vector=>vector.path)??[]);
  for (const path of await changedFiles(run,p,true)) {
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
async function refreshReplayBaseline(run,p) {
  if (!replayEnabled(run) || run.replayAdoption) return;
  try { run.replayBaseline = pinReplayVectors(run.root,await scenarioInventory(run,p)); }
  catch { run.replayBaseline = {schema_version:'pdd.replay-vectors.v1',vectors:[],outcome:'blocked',reason:'The changed scenario inventory is unavailable; repair unreadable or malformed JSON candidates and Git listing failures.'}; }
  const applyPublication=publicationUpdate(run,['replayBaseline']);
  commitRun(run,p,applyPublication);
}
async function currentReplayEvidence(run,p,validated=false) {
  let reason = validated ? null : await adoptionFailure(run,p);
  let paths;
  try {
    paths=await scenarioInventory(run,p);
  } catch(error) { reason = `The current changed scenario inventory is unavailable: ${oneLine(error.message)}. Repair unreadable or malformed JSON candidates and Git listing failures.`; }
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

async function areaMessage(run, index, p, packageRoot) {
  const area = run.areas[index], pdd = '"$PDD_BIN"', earlier = run.areas.slice(0, index).flatMap(item => item.steps);
  const summaries = earlier.filter(step => run.done[step]).map(step => `${step}: ${oneLine(run.done[step].summary).replace(/[.\s]+$/, '') || 'done'}`);
  const files = index ? await changedFiles(run, p) : [];
  return [
    `Use the ${run.skill} skill: ${join(run.skillDir ?? join(packageRoot ?? PACKAGE_ROOT, 'skills', run.skill), 'SKILL.md')}. This is a pdd workflow run.${index ? ' The person approved the earlier areas.' : ''}`,
    `Issue: ${run.repo}#${run.number} "${oneLine(run.issue.title)}" ${run.issue.url}`,
    `Worktree: ${run.root} (branch ${run.branch}). Work and commit only here.`,
    `Run folder: ${run.runDir}. Put notes there. verify writes verify.md there with the exact test commands and their output.`,
    ...(index ? [`Approved so far: ${summaries.join('; ') || 'no step summaries'}.`, `Changed files: ${files.slice(0, 20).join(', ') || 'none yet'}${files.length > 20 ? ', …' : ''}.`] : []),
    `Area ${index + 1} of ${run.areas.length}: ${area.name}. Steps: ${area.steps.map(step => area.optional.includes(step) ? `${step} (optional: ask the person)` : step).join(', ')}.`,
    `After each step, run: ${pdd} workflow done STEP --summary "one line". It prints what to do next.`,
    ...(prLabel(run, area) === 'PR 2' && prOf(run, askArea(run).name) ? [`PR 1: ${prOf(run, askArea(run).name).url}. This area works on branch ${run.branch}, ${run.prBase === run.baseBranch ? `from the merged ${run.baseBranch}` : 'on top of PR 1'}.`] : []),
    area.gate === 'approve'
      ? `Gate: after the last step, show the person the result, ask them to approve or ask for changes, and stop. Never approve for them: ${approvalGuide(run, pdd)}`
      : area.then === 'ask-code'
      ? 'After the last step, pdd pushes the branch and opens PR 1 (prompt, Story and tests). Then show it and ask whether to make the code PR now. Never push, open a PR or merge yourself.'
      : `After the last step, pdd pushes the branch and opens ${prLabel(run, area)}. Never push, open a PR or merge yourself.`,
    `Read the PDD skills (pdd-prompting too) from ${join(packageRoot ?? PACKAGE_ROOT, 'skills')}: an installed copy with the same name may be older.`,
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
    const files = (await git(p, run.root, 'diff', '--name-only', `refs/remotes/origin/${base}...${branch}`)).split('\n').filter(path => path.endsWith('.prompt.md'));
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
    stories: paths.filter(path => path.endsWith('.md') && path.split('/').slice(0, -1).includes('user_stories') && !/^(?:plan|readme)\.md$/i.test(path.split('/').at(-1))).length };
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
  return `the ${failure.area} chat ${failure.phase === 'start' ? 'startup' : 'open'} was not confirmed (${failure.code}: ${failure.message}). Run pdd workflow open ${run.number} after Herdr is available.`;
};
const chatStatusWords = (run, chat) => run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase) ? `chat replacement pending at ${run.chatReplacement.phase}; run pdd workflow open ${run.number} --new` : activeChatFailure(run) ? chatFailureWords(run)
  : chat === 'unavailable' ? `Herdr status unavailable (server_unavailable); chat activity is unknown. Run pdd workflow open ${run.number} after Herdr is available.`
  : chat === 'starting' ? `the chat is starting, not confirmed: Herdr shows no agent in its tab. Run pdd workflow open ${run.number}.`
  : `chat startup is not confirmed. Run pdd workflow open ${run.number} after Herdr is available.`;
function clearChatFailure(run) {
  if (!run.chatFailure) return;
  const selected = run.chatFailure.area === run.areas[run.area]?.name;
  delete run.chatFailure;
  if (selected && !ended(run) && !run.gate && !openQuestion(run)) run.state = 'running';
}

// A gate whose chat still works: after a change request it revises, else it writes the gate message (0.1.6 tester: status
// said "waiting for you" about a minute before the chat had asked).
const revising = run => { const last = run.changes?.at(-1); return Boolean(last && !last.answer && last.stage === run.gate.area && last.at >= run.gate.at); };
// chat: what Herdr shows (chatState); facts: {drafts, nothing} read by the caller (gateFacts). describe itself makes no calls.
function describe(run, chat = null, { drafts = [], nothing = false } = {}) {
  const area = run.areas[run.area], pr1 = askArea(run) && prOf(run, askArea(run).name);
  if (run.state === 'cancelled') return run.cancelled?.state === 'replaced' ? 'replaced' : 'cancelled';
  if (activeChatFailure(run) || ['unconfirmed', 'unavailable', 'starting'].includes(chat)) return chatStatusWords(run, chat);
  if (openQuestion(run) && run.state !== 'completed') return `waiting for you: ${run.question.text.split('\n')[0]}`;
  if (chat === 'blocked' && run.state === 'running') return `waiting for you: the chat asks a question in its window (pdd workflow open ${run.number})`;
  if (chat === 'stopped' && run.state === 'running') return `the chat stopped. Run pdd workflow open ${run.number} to start it again.`;
  if (run.state === 'completed' && run.gate?.kind === 'ask-code') return `done at PR 1 (merged: ${pr1?.url}). ${codeLater(run)}`;
  if (run.state === 'completed') return 'complete: the PR is merged';
  if (run.gate && chat === 'working') return revising(run) ? `the agent works on your changes to the ${run.gate.area} area` : `the agent writes the gate message for the ${run.gate.area} area`;
  if (run.gate?.kind === 'approve-pr') return `waiting for you: ${nothing ? '' : 'try it, then '}approve to open ${prLabel(run, area) === 'the PR' ? 'the PR' : prLabel(run, area)} (or ask for changes)`;
  if (run.gate?.kind === 'ask-code' && drafts.length) return `PR 1 open (${pr1?.url}); waiting for you: approve the draft prompt${drafts.length > 1 ? 's' : ''} first, then make the code PR.`;
  if (run.gate?.kind === 'ask-code') return `PR 1 open (${pr1?.url}); waiting for you: code PR now, or stop and merge PR 1. ${codeLater(run)}`;
  if (run.gate) return `waiting for you: approve the ${run.gate.area} area or ask for changes`;
  if (prOf(run, area?.name) && area.gate === 'pr') return `waiting for you: review and merge ${prLabel(run, area)} on GitHub`;
  const step = area?.steps.find(item => !run.done[item]);
  return step ? `the agent works on ${step}` : 'the agent works';
}

async function startRunCommand({ name, issue, agent = 'codex', base, adoptCorpus, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  let workflow;
  try { workflow = readWorkflowAreas({ packageRoot, name, cwd, home: p.env.HOME || homedir() }); } catch (error) { return fail(error.message); }
  if (adoptCorpus !== undefined && (typeof adoptCorpus !== 'string' || !adoptCorpus.trim() || !workflow.areas.some(area=>area.replay_evidence===REPLAY_POLICY))) return {exitCode:2,message:'--adopt-corpus requires a declaration path and an explicitly replay-evidence-enabled workflow.'};
  if (!['codex', 'claude', 'gemini', 'agy'].includes(agent)) return fail('Choose --agent codex, --agent claude, --agent gemini or --agent agy.');
  // Every chat of the run uses this config folder; a missing one makes the agent stop at once (0.1.6 tester).
  const variable = homeVariable(agent), configDir = variable && p.env[variable] ? resolve(cwd, expandHome(p.env[variable], p.env)) : null;
  if (configDir && !isFolder(configDir)) return fail(`${variable} is "${configDir}", but that folder does not exist. Fix ${variable} and run the command again.`);
  const explicitBase = base !== undefined;
  const badBase = () => fail('Use --base with a branch name, for example feature/checkout.');
  if (explicitBase && (typeof base !== 'string' || !base || base === 'HEAD' || base.startsWith('-') || base.startsWith('refs/'))) return badBase();
  const context = await gitContext(cwd, p);
  if (!context) return fail('Run this inside a Git checkout of the repository that has the issue.');
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
  if (existing?.state === 'completed') return fail(`Issue #${number} already has a run (${existing.workflow}, ${describe(existing)}). Open it: pdd workflow open ${number}. Status: pdd workflow status ${number}.`);
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
  if (existing) {
    // An active run never blocks a new one (#2871): mark it replaced, name it once, then free it like a cancelled run.
    const replacing = !ended(existing);
    if (replacing) {
      const last = existing.updatedAt ?? existing.startedAt, minutes = Number.isFinite(last) ? Math.max(0, Math.floor((p.now() - last) / 60000)) : null;
      try { commitRun(existing, p, latest => { latest.state = 'cancelled'; latest.cancelled = { state: 'replaced', at: p.now() }; latest.gate = null; }); }
      catch (error) { return fail(`Issue #${number} has an active run ${existing.runId}, but pdd could not mark it replaced (${oneLine(error.message)}). Retry in a moment.`); }
      warnings.push(`warning: Issue #${number} had an active run ${existing.runId} (${existing.workflow}). pdd marked it replaced and starts a new run.`
        + ` Its worktree stays at ${existing.root} (branch ${existing.branch}), from checkout ${existing.sourceRoot}. Last activity: ${minutes === null ? 'unknown' : `${minutes} min ago`}.`
        + (minutes === null || minutes < 60 ? ' It may still be working; close its chat if it is.' : ''));
    }
    const released = await releaseIssueClaim({ cwd: context.toplevel, runId: existing.runId, issueNumber: number }, p.commandPorts);
    if (released.state !== 'released') return fail(`Issue #${number} has a ${replacing ? 'replaced' : 'cancelled'} run, but pdd could not free the issue: ${released.message}`);
    if (!replacing) warnings.push(`Issue #${number} had a cancelled run. Its worktree stays at ${existing.root} (branch ${existing.branch}). This run gets a new worktree and branch.`);
  }
  if (!explicitBase && adoptCorpus === undefined) {
    p.say(`Fetching origin/${baseBranch}…`);
    try { await p.execFile('git', ['fetch', 'origin', baseBranch], { cwd: context.toplevel }); }
    catch { warnings.push(`warning: "git fetch origin ${baseBranch}" failed; the worktree starts from the last fetched ${baseBranch}.`); }
  }
  const runId = randomUUID();
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
  // Keep the cancelled run's record next to the new one; only a plain issue number names the active run.
  if (existing) renameSync(runDir, `${runDir}-cancelled-${existing.runId.slice(0, 8)}`);
  const productMarkers = [...new Set(String(binding.issue.body ?? '').match(/<!-- pdd-product: run=[^\r\n]+? -->/g) ?? [])];
  if (productMarkers.length > 1) warnings.push('Warning: The issue has multiple planned-run markers; its product association is unverified.');
  const run = { v: 1, runId, workflow: name, skill: workflow.skill, skillDir: workflow.dir, repo: binding.repository,
    ...(productMarkers.length === 1 ? { productMarker: productMarkers[0] } : {}),
    issue: { number, title: binding.issue.title, url: binding.issue.url }, number, root: a.worktreePath, branch: a.branch,
    baseBranch, baseSha: a.baseSha, sourceRoot: a.sourceRoot, commonDir: a.commonDir, runDir, agent,
    configDir,
    startedAt: p.now(), state: 'running', areas: workflow.areas, area: 0, done: {}, gate: null, chats: [], decisions: [], changes: [],
    approvalRecord: null, pr: [], prState: null, cancelled: null, warnings, journalSeq: 0,
    previous: existing ? [...(existing.previous ?? []), { runId: existing.runId, root: existing.root, branch: existing.branch, runDir: `${runDir}-cancelled-${existing.runId.slice(0, 8)}` }] : [] };
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
    return fail([...warnings, `The worktree is ready at ${a.worktreePath}, but the ${first.name} chat startup was not confirmed (${error.code === 'ENOENT' ? causeOf(error) : `${error.code ?? 'error'}: ${oneLine(error.message)}`}).`,
      `Start it with: pdd workflow open ${number}`].join('\n'));
  }
  commitRun(run,p,()=>{});
  const chat = run.chats[0];
  return done([...warnings,
    `Started ${name} for ${run.repo}#${number} "${oneLine(run.issue.title)}".`,
    `Area 1 of ${run.areas.length}: ${first.name} (${first.steps.join(', ')}). ${agent === 'claude' ? 'Claude' : agent === 'gemini' ? 'Gemini' : agent === 'agy' ? 'Antigravity' : 'Codex'} works in Herdr session pdd, tab "${chat.label}".`,
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
export function runtimeLines(text) {
  return [...String(text ?? '').matchAll(LINE_PATTERN)].map(match => {
    const groups = [...match[1].matchAll(/\(([^)]*)\)/g)].map(group => group[1].trim());
    const story = groups.find(group => group && group.toUpperCase() !== 'DRAFT' && group !== 'all Stories') ?? null;
    const result = match[2].replace(/\s+/g, ' ').trim().replace(/[.,]$/, '');
    return { story, draft: groups.some(group => group.toUpperCase() === 'DRAFT'), result,
      line: `${PROMPT_TESTS_LABEL}${match[1].replace(/\s+/g, ' ')}: ${result}`, pass: result.includes('✓') && !result.includes('✗') };
  });
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
    try { return capture(root, { tests: source.tests, appMap: null }).sha256 === source.sha256; } catch { return false; }
  }
  return false;
}
export function storyCount(run, ports = {}) {
  const records = [...(run.runtimeHistory ?? []), ...Object.values(run.done ?? {}), ...(run.evidence ?? [])]
    .filter(record => runtimeLines(record.summary).length).sort((a, b) => (a.at ?? 0) - (b.at ?? 0));
  if (!records.length) return null;
  const fingerprint = (ports.fingerprint ?? gitFingerprint)(run.root), compatible = records.filter(record => matchesSource(record, run.root, fingerprint, ports.capture));
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
  const records = [...(run.runtimeHistory ?? []), ...Object.values(run.done ?? {}), ...(run.evidence ?? [])]
    .filter(record => runtimeLines(record.summary).length).sort((a, b) => (a.at ?? 0) - (b.at ?? 0));
  const root = comparisonRoot === undefined ? run.root : comparisonRoot;
  const current = new Map(), older = new Map(), fingerprint = root === null ? null : gitFingerprint(root);
  for (const record of records) {
    const compatible = root !== null && matchesSource(record, root, fingerprint);
    for (const row of latestStories(runtimeLines(record.summary))) {
      (compatible ? current : older).set(row.story, { story: row.story, pass: row.pass, current: compatible, result: row.result, at: record.at ?? 0 });
    }
  }
  return [...new Map([...older, ...current]).values()];
}
const storyText = count => `${count.pass} of ${count.total} Stories pass${count.unknown?.length ? ` · ${count.unknown.length} unknown` : ''}`;
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
  const saved = { runId: run.runId, runDir: run.runDir, root: run.root, baseSha: run.baseSha, baseBranch:run.baseBranch, workflow:run.workflow, number: run.number,
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
        return {content:observedProof,error:''};
      } catch (error) { return {content:'',error:error.code === 'ENOENT' ? 'missing' : 'Proof could not be read.'}; }
    }
  });
  if (prLabel(run, area) !== 'PR 1') {
    evidence.nativeLine = 'Native tests: unknown (no current machine counts).';
    try {
      const record = JSON.parse(observedProof);
      if (validateProofRecord(record) && record.runId === run.runId && record.headSha === observedHead?.headSha && record.baseSha === observedHead?.baseSha
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
function publicationRuntime(run, env) {
  if (run.publicationPending) return [];
  const fingerprint = gitFingerprint(run.root);
  const records = [...(run.runtimeHistory ?? []), ...Object.values(run.done ?? {}), ...(run.evidence ?? [])]
    .filter(record => runtimeLines(record.summary).length && matchesSource(record, run.root, fingerprint)).sort((a,b) => (a.at ?? 0) - (b.at ?? 0));
  const stories = new Map();
  for (const record of records) for (const line of runtimeLines(record.summary)) if (line.story) stories.set(line.story, { line, record });
  if (!stories.size) {
    const record = records.at(-1);
    return record ? [...runtimeTop(record.summary), ...reportLinks(record.summary, env)] : [];
  }
  const selected = [...stories.values()];
  const reports = selected.flatMap(({line, record}) => reportLinks(record.summary, env).filter(report => {
    const name = /^Report \(([^)]+)\):/.exec(report)?.[1];
    return !name || name === line.story;
  }));
  return [...selected.map(item => item.line.line), ...(selected.length > 1 ? [totalLine(selected.map(item => item.line))] : []), ...new Set(reports)];
}
function prBody(run, area, env, drafts = [], tests = true, evidence) {
  const steps = prSteps(run, area);
  const raw = Object.fromEntries(steps.map(step => [step, cleanSummary(run, step)]));
  const summaries = Object.fromEntries(steps.map(step => [step, oneLine(raw[step])]));
  // Agent text is inert everywhere in the body: the short Steps line is a code span too.
  const lines = steps.map(step => `- **${step}**: Agent note — not checked by pdd: ${summaries[step] ? codeSpan(shortLine(summaries[step])) : 'done'}`);
  const full = Object.fromEntries(steps.map(step => [step, keepLines(raw[step])]));
  // Only a PR that covers a verify step carries verify.md (PR 1 never does).
  let verify = null;
  if (steps.includes('verify')) {
    try { verify = redactTry(withoutForgedMachineLines(readFileSync(join(run.runDir, 'verify.md'), 'utf8').trim())); } catch { verify = '_verify.md was not written in the run folder._'; }
  }
  const label = prLabel(run, area), ask = askArea(run), pr1 = ask && prOf(run, ask.name);
  const head = label === 'PR 1' ? [evidence.issueReference, '', `PR 1 of this run: ${tests ? 'the prompt, Story and test cases' : 'the prompt and the Story'}. The code comes in PR 2 only when the person asks for it.`]
    : label === 'PR 2' ? [evidence.issueReference, '', `PR 2 of this run: the code. It builds on PR 1: ${pr1?.url}.`,
      ...(run.prBase && run.prBase !== run.baseBranch ? [`It is stacked on PR 1's branch \`${run.prBase}\`: merge PR 1 first.`] : [])]
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
  const runtime = publicationRuntime(run, env).filter(line => !line.startsWith('Report') || !shown.some(url => line.includes(` ${url} `)));
  const noted = runtime.some(line => hasReportLink(line, env)) || change && hasReportLink(change, env);
  const replayResult = area.replay_evidence === REPLAY_POLICY ? run.replayEvidence ?? readReplayEvidence(run) : null;
  const replay = replayResult ? [formatReplayEvidence(replayResult,{maxCharacters:0}), ''] : [];
  const prefix = [...failing, ...replay];
  const top = [...(verdict ? [`${AGENT_NOTE}: ${verdict}`] : []), ...(change ? [`${AGENT_NOTE}: ${change}${hasReportLink(change, env) ? ' (report links expire after 7 days)' : ''}`] : []), ...runtime];
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
  // Room for the full summaries with every summary left out comes first, so a cut is never silent. The top evidence,
  // approvals and verify.md then fit as before, and the full summaries get the room that is left.
  const least = fullSummaries(steps, full, 0);
  const { lifted, approvals } = publicationFit(preparedLines, approvalLines, Math.max(0, BODY_BUDGET - 200 - (verify === null ? 0 : 1000) - characters(body(null, [], [], least))), env);
  if(replayResult){
    const room=Math.max(0,BODY_BUDGET-200-(verify===null?0:1000)-characters(body(null,lifted,approvals,least)));
    prefix[failing.length]=formatReplayEvidence(replayResult,{maxCharacters:characters(replay[0])+room});
  }
  const verifyText = verify === null ? null : verifyFit(hideLocalPaths(verify, run), BODY_BUDGET - 200 - characters(body('', lifted, approvals, least)), env, false, true);
  return withSummaries(steps, full, section => body(verifyText, lifted, approvals, section), BODY_BUDGET - 200);
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
function inventoryCommits(inventory) {
  return commitSha(inventory.baseSha) && commitSha(inventory.headSha)
    ? `Test inventory commits: ${inventory.baseSha.slice(0,7)} → ${inventory.headSha.slice(0,7)}.`
    : 'Test inventory commits: unavailable.';
}

// Commit leftovers, then push to the area's PR or open it. Returns a failure result, or null when the PR is there.
async function publishAreaPr(run, area, p, lines, retry) {
  const label = prLabel(run, area), existing = prOf(run, area.name), title = oneLine(run.issue.title) || `Issue #${run.number}`;
  const status = await git(p, run.root, 'status', '--porcelain=v1', '--untracked-files=all');
  if (status) {
    const files = status.split('\n').map(row => row.slice(3)).filter(Boolean);
    await git(p, run.root, 'add', '-A');
    await git(p, run.root, 'commit', '-q', '-m', `${oneLine(run.issue.title)} (#${run.number})`);
    lines.push(`warning: pdd committed ${files.length} uncommitted file(s): ${files.slice(0, 10).join(', ')}${files.length > 10 ? ', …' : ''}.`);
  }
  const changedAdoption = await adoptionFailure(run,p);
  if(changedAdoption)return fail(changedAdoption);
  const codePr = label !== 'PR 1';
  if (codePr) {
    let baseSha = '', headSha = '', result;
    try {
      headSha = (await rawGit(p,run.root,'rev-parse','--verify','HEAD^{commit}')).trim();
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

  const bodyBase = run.prBase ?? run.baseBranch;
  const bodyDrafts = label === 'PR 1' ? await draftPrompts(run, p, run.branch, bodyBase) : [];
  const bodyTests = label === 'PR 1' ? (await worktreeContents(run, p)).tests.length > 0 : true;
  const markedReplayBody = (replay, pending = false) => {
    const evidence = pending ? { ...prepared, lines: ['Check evidence: publication-pending (source is being published).', ...prepared.lines.map(line => line.startsWith('Old-code proof:') ? 'Old-code proof: publication-pending (source is being published).' : line)] } : prepared;
    const body=prBody({...run,replayEvidence:replay,publicationPending:pending},area,p.env,bodyDrafts,bodyTests,evidence);
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
  const rememberPublication = pr => {
    if (codePr) { pr.publishedHeadSha = run.testInventory.headSha; pr.publicationBodySha256 = bodyIdentity(); }
  };
  if (existing) {
    let inventoryOnly = false;
    if (codePr && !opted && commitSha(existing.publishedHeadSha) && existing.publishedHeadSha === run.testInventory.headSha && existing.publicationBodySha256 === bodyIdentity()) {
      try {
        const remote = await rawGit(p,run.root,'ls-remote','origin',`refs/heads/${run.branch}`);
        inventoryOnly = remote.trim() === `${run.testInventory.headSha}\trefs/heads/${run.branch}`;
      } catch { /* Unavailable remote identity cannot weaken proof safety. */ }
    }
    if (!inventoryOnly) {
      let pending;
      try { pending=markedReplayBody({...run.replayEvidence,outcome:'blocked',reason:'Publication pending; source-bound replay status will be refreshed after the push.'},true); }
      catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail([...lines, `${oneLine(error.message)} No source was pushed. ${retry}.`].join('\n')); }
      const failed=await editReplay(pending);if(failed)return failed;
    }
    p.say(`Pushing ${run.branch} to ${label}…`);
    try {
      const reply = await p.execFile('git', ['push', 'origin', `${codePr && /^[a-f\d]{40,64}$/i.test(run.testInventory.headSha) ? run.testInventory.headSha : 'HEAD'}:refs/heads/${run.branch}`], { cwd: run.root });
      if (reply.code !== undefined && reply.code !== 0) throw Object.assign(Error(reply.stderr || 'git push failed'), {stderr:reply.stderr, code:reply.code});
    }
    catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail([...lines, `git push to ${run.branch} failed (${causeOf(error)}). Check the network and gh auth, then ${retry}.`].join('\n')); }
    if (codePr && await git(p,run.root,'rev-parse','--verify','HEAD^{commit}') !== run.testInventory.headSha) return fail('Source was pushed; the local head changed. The PR stays publication-pending; retry from the pushed source.');
    prepared = await publicationEvidence(run, area, p);
    let finalBody;
    try { finalBody=markedReplayBody(run.replayEvidence); }
    catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail([...lines, `${oneLine(error.message)} Source was pushed; the PR stays publication-pending. ${retry}.`].join('\n')); }
    const failed=await editReplay(finalBody,true,inventoryOnly);
    if (failed) {
      if (!inventoryOnly) return failed;
      lines.push(`warning: The code PR still shows the previous inventory; its displayed commit pair identifies the older comparison. The new comparison is ${commitSha(run.testInventory.baseSha)&&commitSha(run.testInventory.headSha)?`${run.testInventory.baseSha.slice(0,7)} → ${run.testInventory.headSha.slice(0,7)}`:'unavailable'}. The current full report ${run.testInventory.saved ? 'was saved locally in test-inventory.json in the run folder' : 'was not saved locally'}. Inventory refresh failed (${failed.message}); ${retry}.`);
    } else rememberPublication(existing);
    const applyPublication=publicationUpdate(run,codePr?['testInventory']:[]);
    const metadata=Object.fromEntries(['publishedHeadSha','publicationBodySha256'].filter(key=>Object.hasOwn(existing,key)).map(key=>[key,existing[key]]));
    commitRun(run,p,latest=>{applyPublication(latest);const pr=latest.pr.find(pr=>pr.url===existing.url&&pr.stage===existing.stage);if(pr)Object.assign(pr,metadata);});
    if (area.then === 'ask-code') await refreshReplayBaseline(run,p);
    lines.push(`Pushed the new commits to ${label}.`);
    return null;
  }
  const base = bodyBase;
  // PR 1 says "tests" only when it has a test file (0.1.6 tester: a browser-only Story had none).
  const tests = bodyTests;
  let body;
  try { body = prBody(run, area, p.env, bodyDrafts, tests, prepared); }
  catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail([...lines, `${oneLine(error.message)} No source was pushed. ${retry}.`].join('\n')); }
  let intent;
  p.say(`Pushing ${run.branch} and opening ${label} on GitHub…`);
  try {
    intent = await prepareWorkflowPr({ cwd: run.root, runId: run.runId, stageId: area.name, repository: run.repo, baseBranch: base,
      title: prTitle(title, label === 'PR 1' ? ` (${tests ? 'prompt, Story and tests' : 'prompt and Story'})` : label === 'PR 2' ? ' (code)' : '') }, p.commandPorts);
  } catch (error) {
    if(error?.code==='workflow_progress_refused')throw error;
    const why = error.code === 'workflow_github_topic_has_no_commits' ? `There are no new commits on ${run.branch}. Commit the change, then ${retry}.`
      : `pdd could not prepare ${label} (${causeOf(error)}). Fix it, then ${retry}.`;
    return fail([...lines, why].join('\n'));
  }
  const outcome = await publishWorkflowPr({ cwd: run.root, intent, body: `${body}\n<!-- ${intent.marker} -->\n` }, p.commandPorts);
  p.inspectProgress?.();
  // GitHub's refusal and a too-long body are certain: their message names the fix. Only a real doubt says "unconfirmed".
  if (!['open', 'merged'].includes(outcome.state) || !outcome.pr) return fail([...lines, `${label[0].toUpperCase()}${label.slice(1)} did not open: ${/ then try again\.$/.test(outcome.message)
    ? outcome.message.replace(/ then try again\.$/, ` then ${retry}.`) : `${outcome.message} ${retry[0].toUpperCase()}${retry.slice(1)} to retry.`}`].join('\n'));
  if (area.then === 'ask-code') await refreshReplayBaseline(run,p);
  const published = { stage: area.name, number: outcome.pr.number, url: outcome.pr.url, branch: run.branch, base };
  rememberPublication(published);
  const applyPublication=publicationUpdate(run,codePr?['testInventory']:[]);
  commitRun(run,p,latest=>{applyPublication(latest);if(!latest.pr.some(pr=>pr.url===published.url&&pr.stage===published.stage))latest.pr.push(published);});
  return null;
}

// The code-or-stop question after PR 1, as the chat must show it.
async function askCodeLines(run, area, p) {
  const summaries = area.steps.filter(item => run.done[item]).map(item => `  ${item}: ${oneLine(run.done[item].summary) || 'done'}`);
  const drafts = await pr1Drafts(run, p), url = prOf(run, area.name).url;
  // The code is built only from approved prompts, so the code PR is not offered while PR 1 has a draft prompt.
  if (drafts.length) return [`PR 1: ${url}`, ...summaries, draftLine(drafts),
    `Gate: show the person PR 1 and the Prompt tests line. Do not offer the code PR yet. Tell the person exactly: "PR 1 is open: ${url}. ${approveFirst(run, drafts)}" Stop there.`, approvalGuide(run)];
  return [`PR 1: ${url}`, ...summaries,
    `Gate: show the person PR 1, the Prompt tests line and the Try link, then ask exactly: "Do you want the code PR now, or stop here and merge PR 1 first? ${codeLater(run)}" Stop there.`,
    approvalGuide(run, p.pdd),
    `If they stop, tell them exactly: "PR 1 is open: ${prOf(run, area.name).url}. ${codeLater(run)}" pdd never merges.`];
}

async function finishPr(run, area, step, p, lines) {
  const label = prLabel(run, area), existing = prOf(run, area.name);
  const selectedArea=run.area,selectedGate=run.gate;
  lines.push(`pdd recorded ${step}. pdd opens ${label} now.`);
  const failed = await publishAreaPr(run, area, p, lines, `run done ${step} again`);
  if (failed) return failed;
  if(area.replay_evidence===REPLAY_POLICY)lines.push(formatReplayEvidence(run.replayEvidence));
  if (area.then === 'ask-code') {
    // New commits on an open PR 1 keep the question's time, so a yes the person already gave still counts
    // (a change request with pdd workflow changes moves it).
    const at=p.now();
    commitRun(run,p,latest=>{if(latest.area===selectedArea&&sameGate(latest.gate,selectedGate)){latest.state='waiting';latest.gate=existing && latest.gate?.kind==='ask-code'?latest.gate:{id:p.randomUUID(),area:area.name,at,kind:'ask-code'};}});
    const savedApproval = !!run.gate && (run.decisions ?? []).some(decision => decision.gateId === run.gate.id && decision.evidence);
    const shownGate = run.area===selectedArea && run.gate?.kind==='ask-code' ? (savedApproval ? snapshotLines(run.gate.promptSnapshot ?? []) : await showGate(run, p)) : [];
    return done([...lines, ...shownGate, ...await askCodeLines(run, area, p)].join('\n'));
  }
  commitRun(run,p,latest=>{if(latest.area===selectedArea&&sameGate(latest.gate,selectedGate)){latest.state='waiting';latest.gate=null;}});
  return done([...lines, `${label === 'the PR' ? 'PR' : label}: ${prOf(run, area.name).url}`, `Tell the person ${label} is open. pdd never merges. Stop here.`].join('\n'));
}

// Record saved Runtime evidence without progressing the workflow or contacting external services.
async function recordEvidenceCommand({ ref, summaryFile, cwd }, ports) {
  const p = deps(ports), found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  let receipt, source, lines;
  try {
    if (!summaryFile || !lstatSync(resolve(cwd, summaryFile)).isFile() || lstatSync(resolve(cwd, summaryFile)).size > 2 * 1024 * 1024) throw Error('Supply a regular saved JSON file of at most 2 MiB.');
    receipt = JSON.parse(readFileSync(resolve(cwd, summaryFile), 'utf8'));
    if (realpathSync(receipt.repo) !== realpathSync(run.root)) throw Error('The evidence belongs to a different repository/worktree.');
    if (!/^[a-f0-9]{64}$/.test(receipt.source_sha256 ?? '') || !Array.isArray(receipt.rows) || !receipt.rows.length) throw Error('Saved check JSON needs source_sha256 and nonempty rows.');
    const tests = receipt.rows.map(row => row?.test);
    if (tests.some(path => typeof path !== 'string' || !path) || new Set(tests).size !== tests.length) throw Error('Evidence test paths must be unique.');
    source = { kind: 'runtime-capture-v1', sha256: receipt.source_sha256, tests };
    if (!matchesSource({ source }, run.root, null)) throw Error('The saved source does not match the current selected files. Read a compatible receipt or run a fresh selected check.');
    const found = findTests({ root: run.root });
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
  const evidence={at:p.now(),summary:[...new Set(lines)].join('\n'),source,receipt};
  commitRun(run,p,latest=>{(latest.evidence??=[]).push(evidence);});
  return done(`Recorded source-verified saved evidence for ${run.repo}#${run.number}. Steps, gates and PRs are unchanged. This records evidence, not fresh execution or approval.`);
}

async function stepDoneCommand({ step, summary, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const run = await runForWorktree(cwd, p);
  if (!run) return fail('pdd workflow done works only in a run worktree. cd to the worktree that pdd made for this run.');
  if (run.state === 'cancelled') return done(`The run for #${run.number} was cancelled. Stop working on it.`);
  if (run.state === 'completed') return done(`The run for #${run.number} is complete. Stop.`);
  protectProgress(run,p);
  const area = run.areas[run.area], lines = [];
  if (!area.steps.includes(step)) lines.push(`warning: "${step}" is not a step of the ${area.name} area (${area.steps.join(', ')}). pdd recorded it anyway.`);
  else {
    const before = area.steps.slice(0, area.steps.indexOf(step)).filter(item => !run.done[item] && !area.optional.includes(item));
    if (before.length) lines.push(`warning: ${before.join(', ')} ${before.length > 1 ? 'are' : 'is'} not done yet. pdd recorded ${step} anyway.`);
  }
  const observedQuestion=run.question, observedGate=run.gate;
  const record = { at: p.now(), summary: keepLines(summary), area: area.name };
  const hasRuntime=runtimeLines(record.summary).length>0;
  if(hasRuntime)record.source={kind:'git-content-v1',sha256:gitFingerprint(run.root)};
  const replay=area.replay_evidence===REPLAY_POLICY && (area.steps.some(item=>item!==step&&!run.done[item]) || area.gate!=='pr' || area.before==='approve'&&!prOf(run,area.name))?await currentReplayEvidence(run,p):null;
  if(replay){record.replayEvidence=replay;lines.push(formatReplayEvidence(replay));}
  const applyDone=latest=>{
    if(equalFact(latest.question,observedQuestion))latest.question=null;
    const later=area.steps.includes(step) && latest.done[step]?area.steps.slice(area.steps.indexOf(step)+1).filter(item=>latest.done[item]):[];
    if(later.length){
      for(const item of later)delete latest.done[item];
      lines.push(`warning: ${step} ran again after ${later.join(', ')}. pdd cleared ${later.length>1?'those steps':'that step'}; run ${later.length>1?'them':'it'} again.`);
    }
    if(hasRuntime)(latest.runtimeHistory??=[]).push({...record,step});
    if(replay)latest.replayEvidence=replay;
    latest.done[step]=record;
  };
  let next, currentArea;
  const gateAt=p.now();
  commitRun(run,p,latest=>{
    applyDone(latest);
    next=area.steps.find(item=>!latest.done[item]);
    currentArea=latest.areas[latest.area]?.name===area.name;
    if(currentArea && equalFact(latest.gate,observedGate)){
      if(next){latest.state=latest.question?'waiting':'running';latest.gate=null;}
      else if(area.gate==='pr'&&area.before==='approve'&&!prOf(latest,area.name)){latest.gate={id:p.randomUUID(),area:area.name,at:gateAt,kind:'approve-pr'};latest.state='waiting';}
      else if(area.gate!=='pr'){latest.gate={id:p.randomUUID(),area:area.name,at:gateAt,kind:'approve'};latest.state='waiting';}
    }
  });
  if(!currentArea)return doneWithRequests(done(`pdd recorded ${step}.`),run,p);
  if (next) {
    lines.push(`pdd recorded ${step}.`, area.optional.includes(next)
      ? `Next step: ${next} (optional). Ask the person if they want it. If they do not, run: ${p.pdd} workflow done ${next} --summary "skipped"`
      : `Next step: ${next}.`, `When it is done, run: ${p.pdd} workflow done ${next} --summary "one line"`);
    return doneWithRequests(done(lines.join('\n')), run, p);
  }
  // Try before PR 1 (#13): the person tries the result and approves before pdd opens the area's PR.
  if (area.gate === 'pr' && area.before === 'approve' && !prOf(run, area.name)) {
    const contents = await worktreeContents(run, p);
    lines.push(...await showGate(run, p));
    lines.push(`pdd recorded ${step}. The ${area.name} area is done; pdd opens ${prLabel(run, area)} after the person approves.`,
      nothingToTry(run, area, contents)
        ? 'Gate: show the person the Prompt tests line of each Story (one per Story: ✓, ✗ or no verdict) with the report link, if there is one. There is nothing to try. Ask them to approve or ask for changes. Stop. Do not approve for them.'
        : 'Gate: show the person the Prompt tests line of each Story (one per Story: ✓, ✗ or no verdict) with the report link, and the Try link(s). Ask them to try it, then approve or ask for changes. Stop. Do not approve for them.',
      ...(prLabel(run, area) === 'PR 1' ? [`Tell the person what PR 1 holds, in these words: "${holdsLine(contents)}"`] : []),
      approvalGuide(run, p.pdd),
      'If they ask for changes, revise in this chat, run done again for the step you changed, and ask again.');
    return doneWithRequests(done(lines.join('\n')), run, p);
  }
  if (area.gate === 'pr') {
    return doneWithRequests(await finishPr(run,area,step,p,lines),run,p);
  }
  lines.push(...await showGate(run, p));
  lines.push(`pdd recorded ${step}. The ${area.name} area is done.`,
    'Gate: show the person the result, ask them to approve it or ask for changes, and stop. Do not approve for them.',
    approvalGuide(run, p.pdd),
    'If they ask for changes, revise in this chat, run done again for the step you changed, and ask again.');
  return doneWithRequests(done(lines.join('\n')), run, p);
}

// The code area works on <branch>-code: on PR 1's head while PR 1 is open (PR 2 stacks on it), else on the merged saved base branch.
async function codeBranch(run, area, p) {
  const pr1 = prOf(run, area.name), name = `${pr1.branch}-code`;
  const state = await (p.readPrStatus ?? readWorkflowPrStatus)({ cwd: run.root, url: pr1.url }, p.commandPorts);
  if (!['open', 'merged'].includes(state.state)) throw Error(`PR 1 is ${state.state}, so pdd cannot tell where the code branch should start.`);
  const fetch = async ref => {
    try {
      const reply = await p.execFile('git', ['fetch', 'origin', `refs/heads/${ref}:refs/remotes/origin/${ref}`], { cwd: run.root });
      if (reply.code !== undefined && reply.code !== 0) throw Error('fetch rejected');
    } catch { throw Error(`Could not fetch ${ref} from origin. No code branch was created; try again when the remote branch is available.`); }
  };
  if (state.state === 'merged') {
    await fetch(run.baseBranch);
    await git(p, run.root, 'switch', '-q', '-c', name, `refs/remotes/origin/${run.baseBranch}`);
    run.prBase = run.baseBranch;
  } else {
    await fetch(pr1.branch);
    await git(p, run.root, 'switch', '-q', '-c', name);
    run.prBase = pr1.branch;
  }
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
  if (behind && replayEnabled(run)) return {failed:`The prompt branch is behind its published head. Update the worktree from origin/${run.branch}, then ${approvalGuide(run, p.pdd)}.`};
  if (!ahead && !behind) await refreshReplayBaseline(run,p);
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
  await refreshReplayBaseline(run,p);
  const drafts = await pr1Drafts(run, p);
  return { drafts, lines: [what ? `pdd committed ${what} and pushed it to PR 1.` : `pdd pushed ${ahead} new commit${ahead > 1 ? 's' : ''} from the worktree to PR 1.`, ...await draftDescription(run, pr1, drafts, p)] };
}

// PR 1's description names its draft prompts; after a push to PR 1 that line must say the new truth. A failure only warns.
async function draftDescription(run, pr1, drafts, p) {
  try {
    const body = JSON.parse(String((await p.execFile('gh', ['pr', 'view', pr1.url, '--json', 'body'], { cwd: run.root })).stdout ?? '')).body;
    if (typeof body !== 'string') throw Error('PR 1 description unavailable.');
    const old = body.split('\n').find(line => line.startsWith('Draft prompts: '));
    const draftBody = !old ? body : drafts.length ? body.replace(old, draftLine(drafts)) : body.replace(`\n\n${old}`, '').replace(old, '');
    const area = askArea(run), evidence = await publicationEvidence(run, area, p), marker = `<!-- pdd-workflow:${run.runId}:${area.name} -->`;
    if (evidence.lines.some(line => line.includes('pdd-workflow:')) || String(draftBody).replace(marker, '').includes('pdd-workflow:')) throw Error('Remove supplied workflow ownership markers.');
    const owned = /^(?:Check evidence: publication-pending|Agent note — not checked by pdd: (?:Not fixed yet:|Not checked:|Defect:|Not caught because:|Proof \(defect fixed\):|Proof \(gap closed\):|Review:|Verdict:|Before[ :])|Not fixed yet:|Not checked:|Defect:|Not caught because:|Proof \(defect fixed\):|Proof \(gap closed\):|Old-code proof:|Tests vs base:|Review:|Evidence omitted:)/;
    const reference = new RegExp(`^(?:Part of|Closes|Refs) #${run.number}$`);
    const rows = String(draftBody).replace(marker, '').split('\n');
    let at = 0;
    const labelledTop = [];
    while (at < rows.length && owned.test(rows[at])) {
      if (/^Agent note — not checked by pdd: (?:Verdict:|Before[ :])/.test(rows[at])) labelledTop.push(rows[at]);
      at++;
    }
    while (at < rows.length && !rows[at].trim()) at++;
    const headerStart = at;
    while (at < rows.length && new RegExp(String.raw`^(?:Agent note — not checked by pdd: (?:Verdict:|Before[ :])|Verdict:|Before |Before:|${PROMPT_TESTS_WORDS}|Report(?: \([^)]*\))?:)`).test(rows[at])) at++;
    const priorTop = rows.slice(headerStart, at);
    const ordinaryTop = [...new Set([...labelledTop, ...priorTop.filter(line => /^(?:Agent note — not checked by pdd: )?(?:Verdict:|Before[ :])/.test(line)).map(line => line.startsWith(`${AGENT_NOTE}: `) ? line : `${AGENT_NOTE}: ${line}`)]), ...publicationRuntime(run, p.env)];
    const introduction = [];
    while (at < rows.length && !rows[at].trim()) at++;
    if (reference.test(rows[at] ?? '')) {
      at++;
      while (at < rows.length && !rows[at].trim()) at++;
      // Newly created PRs put their one-line introduction before approvals;
      // refreshed descriptions put it with the remaining ordinary prose.
      if (/^PR 1 of this run:/.test(rows[at] ?? '')) {
        at++;
        const contents = await worktreeContents(run, p);
        introduction.push(`PR 1 of this run: ${contents.tests.length ? 'the prompt, Story and test cases' : 'the prompt and the Story'}. The code comes in PR 2 only when the person asks for it.`, '');
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
    const footer = `\n\n${marker}\n`;
    const approvalLines = (evidence.approvalLines ?? []).map(line => hideLocalPaths(redactTry(line), run));
    const room = BODY_BUDGET - characters(footer) - characters(evidence.issueReference) - characters(ordinaryTop.join('\n')) - 8;
    const { lifted, approvals } = publicationFit(evidence.lines.map(line => hideLocalPaths(redactTry(line), run)), approvalLines, Math.max(0, room - Math.min(1000, characters(safeRemainder) + reserved)), p.env);
    const leading = [...lifted, ...(lifted.length ? [''] : []), ...ordinaryTop, ...(ordinaryTop.length ? [''] : []), evidence.issueReference, '', ...approvals, ...(approvals.length ? [''] : []), ''].join('\n');
    const fitted = verifyFit(safeRemainder, BODY_BUDGET - characters(leading) - characters(footer) - reserved, p.env, true);
    const placed = section => { const text = section.join('\n'); return fitted.includes(SLOT) ? fitted.replace(SLOT, () => text) : `${fitted}\n\n${text}`; };
    const nextBody = from < 0 ? `${leading}${fitted}${footer}` : withSummaries(steps, texts, section => `${leading}${placed(section)}${footer}`, BODY_BUDGET);
    if (nextBody === body) return [];
    const reply = await p.execFile('gh', ['pr', 'edit', pr1.url, '--body-file', '-'], { cwd: run.root, input: nextBody });
    if (reply.code !== undefined && reply.code !== 0) throw Object.assign(Error('PR 1 description update failed.'), { code: reply.code });
    return [`pdd updated the PR 1 description: ${drafts.length ? `draft prompts left: ${drafts.join(', ')}` : 'no draft prompts are left'}.`];
  } catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return [`warning: pdd could not update the PR 1 description (${error.code ?? 'error'}). ${run.publicationPending ? 'No source was pushed.' : 'The PR retains its previous evidence; after a source push it stays publication-pending.'}`]; }
}

// A terminal in the run's own chat pane (Herdr session pdd) belongs to the chat; a person's other Herdr tab does not.
const chatPane = (run, env) => env.HERDR_PANE_ID && /[\\/]sessions[\\/]([^\\/]+)[\\/][^\\/]+$/.exec(String(env.HERDR_SOCKET_PATH ?? ''))?.[1] === PDD_HERDR_SESSION
  ? (run.chats ?? []).find(chat => chat.paneId === env.HERDR_PANE_ID) ?? null : null;
async function startNextChat(run, p, packageRoot) {
  const area = run.areas[run.area], original = structuredClone(run);
  let prior = lastChat(run, area.name);
  p.say(`Starting the ${area.name} chat in Herdr…`);
  // The starting identity is saved before the native launch. A failed save or an ended run sends nothing.
  const checkpoint = async (chat, layout) => {
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
    if (!saveChatObservations(original, prior, chat, p)) endedMeanwhile();
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
    if (pr1) for (const path of (await rawGit(p, run.root, 'diff', '--name-only', '-z', `${run.baseSha}...${pr1.branch}`)).split('\0')) if (path.endsWith('.prompt.md')) paths.add(path);
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
    let applied=false;
    commitRun(run,p,latest=>{if(latest.gate&&equalFact(latest.gate,observedGate)){latest.gate.promptSnapshot=snapshot;applied=true;}});
    return applied ? snapshotLines(snapshot) : [];
  } catch (error) {
    commitRun(run,p,latest=>{if(latest.gate&&equalFact(latest.gate,observedGate))delete latest.gate.promptSnapshot;});
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
async function saveGateApproval(run, area, record, edits, p, snapshot = run.gate?.promptSnapshot) {
  // An id-less legacy gate gets a current identity only; timestamps never authorize reuse.
  if (run.gate && !run.gate.id) { const id=p.randomUUID(); commitRun(run,p,latest=>{if(latest.gate)latest.gate.id??=id;}); }
  const gateId = run.gate?.id ?? p.randomUUID(), gateAt = run.gate?.at;
  const existing = run.decisions.find(decision => decision.gateId === gateId && decision.evidence);
  if (existing && !edits.length) { run.approvalRecord = { ...(run.approvalRecord?.gateId === gateId ? run.approvalRecord : {}), gateId, kind: existing.via, area: area.name, at: existing.at, evidence: existing.evidence }; return existing; }
  const at = p.now(), evidence = { id: p.randomUUID(), route: record.via, actor: approvalActor(p.env), at, words: record.text ?? null,
    prompts: (snapshot ?? edits).map(({path,proseSha256}) => ({path,proseSha256})) };
  p.inspectProgress?.();
  const fs = p.fs ?? { writeFileSync }, changed = [];
  try {
    for (const edit of edits) { changed.push(edit); fs.writeFileSync(join(run.root, edit.path), edit.next); }
    await recordPromptApproval({ ...await promptApprovalContext(run, p), evidence }, p);
  } catch (error) {
    const left = [];
    for (const edit of changed.reverse()) { try { fs.writeFileSync(join(run.root, edit.path), edit.text); } catch { left.push(edit.path); } }
    throw Error(`${error.message}${left.length ? ` Rollback failed for: ${left.join(', ')}.` : ''}`);
  }
  const decision = { gateId, stage: area.name, decision: 'approve', via: record.via, at, gateAt, ...(record.text !== undefined ? {text: record.text} : {}), evidence };
  const approvalRecord = { gateId, kind: record.via, area: area.name, at, ...(record.via === 'chat' ? { userMessage: record.text, userMessageAt: record.at, sessionId: record.sessionId } : {}), evidence };
  commitRun(run,p,latest=>{latest.decisions.push(decision);latest.approvalRecord=approvalRecord;});
  return decision;
}
async function approveRunCommand({ ref, cwd, said: approvalWords, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run, area = run.areas[run.area], label = `${run.repo}#${run.number} "${oneLine(run.issue.title)}"`;
  const selectedQuestion=run.question,selectedGate=run.gate,selectedArea=run.area;
  const askCode = area.then === 'ask-code', beforePr = run.gate?.kind === 'approve-pr';
  if (ended(run) && !(askCode && run.gate?.kind === 'ask-code')) return fail(`The run for ${run.repo}#${run.number} is ${run.state}. There is nothing to approve.`);
  if (area.gate === 'pr' && !askCode && !beforePr) return fail(`Nothing to approve for #${run.number}: the ${area.name} area ends with ${prLabel(run, area)}, which pdd opens after its last step.${prOf(run, area.name) ? ` ${prLabel(run, area) === 'the PR' ? 'PR' : prLabel(run, area)}: ${prOf(run, area.name).url}` : ''}`);
  const approvalRecorded=protectProgress(run,p,{approval:true});
  const missing = missingHome(run, p.env);
  if (missing) return fail(missing);
  const agent = isAgentSession(p.env), pane = chatPane(run, p.env), viaChat = agent || !p.isTTY || Boolean(pane);
  let policy;
  try { policy = readApprovalPolicy({root: run.sourceRoot}, p); }
  catch (error) { return fail(error.message); }
  if (policy.strictApprovals && (approvalWords !== undefined || viaChat)) return fail(`Only the person can approve in a terminal. Run pdd workflow approve ${run.number} in a normal terminal.`);
  if (approvalWords === undefined && viaChat) return fail(approvalGuide(run, p.pdd));
  try { if (approvalWords !== undefined) approvalWords = await readSaidWords(approvalWords, p); p.inspectProgress(); } catch (error) { return fail(error.message); }
  if (approvalWords !== undefined && (!run.gate || area.steps.some(step => !run.done[step]))) return fail('The gate is not ready. Finish its steps and run done first.');
  if(!beforePr){const adoptedFailure=await adoptionFailure(run,p);if(adoptedFailure)return fail(adoptedFailure);}
  if (askCode && run.gate?.kind === 'ask-code') {
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
  let edits = [];
  try {
    if (run.gate && area.steps.every(step => run.done[step])) {
      const current = await gatePromptSnapshot(run, p);
      if (approvalWords !== undefined && !samePromptReview(current, run.gate.promptSnapshot)) return fail('The selected prompts changed or this gate has no saved review. Show the gate again with done and ask the person again.');
      edits = await approveGatePrompts(run, p);
      if (approvalWords === undefined) { p.say(snapshotLines(current).join('\n')); commitRun(run,p,latest=>{latest.gate.promptSnapshot=current;}); }
    } else readPromptApprovals(await promptApprovalContext(run, p), p);
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
  const invocationAt=p.now();
  p.inspectProgress();
  let approvalSnapshot = run.gate?.promptSnapshot;
  try {
    if (approvalSnapshot) {
      const current = await gatePromptSnapshot(run, p);
      if (!samePromptReview(current, approvalSnapshot)) return fail('The selected prompts changed. Show the gate again and ask the person again.');
      approvalSnapshot = current;
      edits = await approveGatePrompts(run, p, current);
    }
  } catch (error) { return fail(`Cannot inspect selected prompts: ${error.message}. Show the gate again and ask the person again.`); }
  let saved;
  try { if (run.gate || beforePr || !askCode) saved = await saveGateApproval(run, area, record, edits, p, approvalSnapshot); }
  catch (error) { return fail(`Approval failed: ${error.message}`); }
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
      await sendToChat(currentChat(run), `pdd opened PR 1: ${url}. The person approved it in their terminal. PR 1 has draft prompts, so the code PR waits. Tell them exactly: "PR 1 is open: ${url}. ${approveFirst(run, drafts)}" Then stop.
${approvalGuide(run)}`, p);
      return done([...head, `PR 1: ${url}`, approveFirst(run, drafts)].join('\n'));
    }
    if (!await confirm(p, `Make the code PR now and approve the code gate and all selected draft prompts for ${label}? PR 1: ${url} (y/N) `)) {
      await sendToChat(currentChat(run), `pdd opened PR 1: ${url}. The person approved it in their terminal and stops here for now. Tell them exactly: "PR 1 is open: ${url}. ${codeLater(run)}" Then stop.
${approvalGuide(run)}`, p);
      return done([...head, `PR 1: ${url}`, `Stopped at PR 1. ${codeLater(run)}`].join('\n'));
    }
  }
  if (beforePr && askCode) saved = null;
  if (!saved) {
    try { saved = await saveGateApproval(run, area, record, edits, p); }
    catch (error) { return fail(`Approval failed: ${error.message}`); }
  }
  let based = '';
  if (askCode) {
    const adoptedFailure=await adoptionFailure(run,p);if(adoptedFailure)return fail(adoptedFailure);
    // Reached at the code gate, or right after PR 1 opened when the terminal said yes to the code PR.
    p.say('Making the code branch…');
    try { based = await codeBranch(run, area, p); }
    catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail(`${oneLine(error.message)} Check PR 1, then ${approvalRetry(run, p.pdd)}`); }
  }
  if (askCode && approvalWords === undefined && beforePr) carried.push(...await draftDescription(run, prOf(run, area.name), await pr1Drafts(run, p), p));
  const now = invocationAt;
  const branch=run.branch,prBase=run.prBase,observedQuestion=selectedQuestion,areaIndex=selectedArea;
  commitRun(run,p,latest=>{


    if(askCode){latest.branch=branch;latest.prBase=prBase;}
    if(equalFact(latest.question,observedQuestion))latest.question=null;
    if(latest.area===areaIndex){if(sameGate(latest.gate,selectedGate))latest.gate=null;latest.area=areaIndex+1;latest.state=latest.question?'waiting':'running';latest.doneAt=null;}
  });
  approvalRecorded();
  const next = run.areas[run.area];
  let chat;
  try { chat = await startNextChat(run, p, packageRoot); }
  catch (error) {
    if(error?.code==='workflow_progress_refused')throw error; return fail(`${carried.map(line => `${line}\n`).join('')}Approved the ${area.name} area of ${label}.${said} The ${next.name} chat startup was not confirmed (${error.code ?? 'error'}). Start it: pdd workflow open ${run.number}`); }
  return done([...carried, `Approved the ${area.name} area of ${label}.${said}${based}`,
    `Started area ${run.area + 1} of ${run.areas.length}: ${next.name} (${next.steps.join(', ')}) in a new chat: Herdr session pdd, tab "${chat.label}".`,
    `Watch it: pdd workflow open ${run.number}`, ...(agent ? ['This chat\'s work is done. Stop here.'] : [])].join('\n'));
}

// The agent asks the person in the middle of a step: status shows the question until the next done or the answer.
async function askPersonCommand({ text, cwd }, ports) {
  const p = deps(ports);
  const run = await runForWorktree(cwd, p);
  if (!run) return fail('pdd workflow ask works only in a run worktree. cd to the worktree that pdd made for this run.');
  if (ended(run)) return done(`The run for #${run.number} is ${run.state}. Stop working on it.`);
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
    typeof entry.text !== 'string' || !['pending', 'uncertain', 'delivered'].includes(entry.state) || !['answer', 'change'].includes(entry.kind) ||
    typeof entry.area !== 'string' || !entry.area || typeof entry.paneId !== 'string' || !entry.paneId || !Number.isFinite(entry.at) ||
    entry.inFlight !== undefined && typeof entry.inFlight !== 'boolean') || new Set(journal.requests.map(entry => entry.id)).size !== journal.requests.length) throw Error('Malformed delivery journal');
  return journal;
}
const uptakeQuote = value => "'" + value.replaceAll("'", "'\"'\"'") + "'";
const uptakeCommand = (id, p) => `${p.pdd ?? pddFor(p, PACKAGE_ROOT)} ${PUBLIC_COMMAND_ROUTES.find(route => route.id === 'workflow.request-uptake').prefix.join(' ')} ${uptakeQuote(id)} --summary ${uptakeQuote('what I changed')}`;
const deliveryTime = (value, p = {}) => typeof value !== 'number' || !Number.isFinite(value) || Math.abs(value) > 8640000000000000 ? 'unknown' : new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit', hourCycle: 'h23', ...(p.timeZone ? { timeZone: p.timeZone } : {}) }).format(new Date(value));
const uptakeReceipt = (entry, p) => `Request ${entry.id}: delivered at ${deliveryTime(entry.deliveredAt, p)}; ${entry.ackedAt == null ? 'not yet acknowledged by the agent' : `acknowledged at ${deliveryTime(entry.ackedAt, p)}: ${entry.ackSummary ?? ''}`}.`;
function requestSnapshot(run, p) {
  try {
    const entries = readDeliveryJournal(run, p).requests;
    return { requests: entries.filter(entry => entry.kind === 'change' && entry.state === 'delivered')
      .map(entry => ({ id: entry.id, text: entry.text, area: entry.area, deliveredAt: entry.deliveredAt ?? null, ackedAt: entry.ackedAt ?? null, ackSummary: entry.ackSummary ?? null })),
      pendingRequests: entries.filter(entry => !entry.inFlight && entry.state === 'pending').map(({ id, text, area, paneId }) => ({ id, text, area, paneId })),
      uncertainRequests: entries.filter(entry => !entry.inFlight && entry.state === 'uncertain').map(({ id, text, area, paneId }) => ({ id, text, area, paneId })),
      inFlightRequests: entries.filter(entry => entry.inFlight).map(({ id, text, area, paneId }) => ({ id, text, area, paneId })) };
  } catch { return { requests: null, inFlightRequests: null, pendingRequests: null, uncertainRequests: null, requestWarning: 'Change-request visibility unavailable: could not read the delivery journal. Check the run folder.' }; }
}
const protectedRequestAdvice = entry => `Request ${entry.id}: ${entry.text}. Original area ${entry.area}, pane ${entry.paneId}. Wait for the current send to finish before checking the original chat or typing anything. If it remains stuck after waiting, pdd will not automatically clear or resend protected ownership. First verify the original chat before manually supplying anything absent.`;
function requestLines(snapshot, { openOnly = false, agent = false, ended = false, p = {} } = {}) {
  if (snapshot.requestWarning) return [snapshot.requestWarning];
  return [...snapshot.requests.filter(entry => (!ended || !openOnly) && (!openOnly || entry.ackedAt == null)).map(entry =>
    `${uptakeReceipt(entry, p)} Area ${entry.area}: ${entry.text}${agent ? `\nTell the person about this outstanding request. After actually addressing this request, run: ${uptakeCommand(entry.id, p)}` : ""}`), ...snapshot.pendingRequests.map(entry => `Request ${entry.id}: ${ended ? 'pending, not sent; run ended. Original' : 'pending, saved for the original'} ${entry.area} chat, pane ${entry.paneId}: ${entry.text}`), ...snapshot.uncertainRequests.map(entry => `Request ${entry.id}: uncertain, may already be in the original ${entry.area} chat, pane ${entry.paneId}: ${entry.text}. Check that original chat.`), ...snapshot.inFlightRequests.map(entry => agent ? `Request ${entry.id}: delivery in progress. Tell the person about this outstanding request.` : protectedRequestAdvice(entry))];
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

export async function changeRun({ ref, text, cwd }, ports) {
  const p = deps(ports), found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  let run = found.run;
  const selectedIdentity=runIdentity(run);
  if (ended(run)) return fail(`The run for ${run.repo}#${run.number} is ${run.state}.`);
  const request = oneLine(text), answer = Boolean(openQuestion(run)), kind = answer ? 'answer' : 'change';
  if (!request) return fail('Write the change request after the issue number.');
  if (!answer && run.gate && looksLikeApproval(request)) return { exitCode: 2, message: `This looks like an approval. Tell your agent you approve this gate, or run pdd workflow approve ${run.number} in a terminal.
Nothing was sent to the chat.` };
  const area = run.areas[run.area], chat = currentChat(run);
  if (!chat) return fail(`The ${area.name} area has no chat. Start it: pdd workflow open ${run.number}`);
  const latest = () => readRun(run.runDir), matches = entry => entry.area === area.name && entry.paneId === chat.paneId;
  const targetCurrent = saved => saved && runIdentity(saved)===selectedIdentity && !ended(saved) && saved.areas[saved.area]?.name === area.name && currentChat(saved)?.paneId === chat.paneId;
  const retry = `Retry: pdd workflow changes ${run.number} '${request.replace(/'/g, `'\\''`)}'`;
  const kept = `Your request is kept. Wait briefly or open it: pdd workflow open ${run.number}. ${retry}`;
  const warning = `An earlier request is uncertain and may already be in the chat. Check the original chat: pdd workflow open ${run.number}; type it there if absent. pdd will not automatically resend it.`;
  const uncertain = () => fail(`Your request is uncertain and may already be in the chat. Check the original chat: pdd workflow open ${run.number}; type it there if absent. pdd will not automatically resend it.`);
  const progress = entry => fail(`Delivery to the original ${entry.area} chat is in progress or needs inspection. ${accepted.id !== entry.id ? 'Your request is saved pending. ' : ''}${protectedRequestAdvice(entry)} Open it: pdd workflow open ${run.number}.`);
  const already = () => done(`Your request was already delivered to the ${area.name} chat.${accepted.kind === 'change' ? `\n${uptakeReceipt(accepted, p)}` : ''}`);
  const failure = sent => {
    if (sent.uncertain) return uncertain();
    if (sent.code === 'chat_target_changed') return fail(`The original ${area.name} chat target changed. ${kept}`);
    if (sent.code === 'chat_still_starting') return fail(`The ${area.name} chat is still starting. ${kept}`);
    if (sent.code === 'agent_blocked') return fail(`The ${area.name} chat shows a question dialog. Answer it in the chat: pdd workflow open ${run.number}. ${kept}`);
    if (sent.code === 'agent_not_found') return fail(`The ${area.name} chat is not running. ${kept}`);
    return fail(`pdd could not send the text to the ${area.name} chat (${sent.code}). ${kept}`);
  };
  let accepted;
  try {
    accepted = await deliveryJournal(run, p, journal => {
      let entry = journal.requests.find(item => matches(item) && item.kind === kind && item.text === request && item.state !== 'delivered');
      if (!entry) { entry = { id: (p.deliveryToken ?? randomUUID)(), text: request, kind, area: area.name, paneId: chat.paneId, state: 'pending', at: p.now(), question: run.question ?? null, gate: run.gate ?? null }; journal.requests.push(entry); }
      return { ...entry };
    });
  } catch (error) { return fail(error.code === 'delivery_busy' ? `Another command is saving a request. Wait briefly, then retry. ${retry}` : `Could not save your request; it was not sent. Check the run folder and retry. ${retry}`); }
  const owner = { pid: p.ownerPid ?? process.pid, hostname: deliveryHost(p), token: (p.deliveryToken ?? randomUUID)() };
  activeDeliveries.add(owner.token);
  try {
    const snapshot = await deliveryJournal(run, p, journal => ({ accepted: { ...journal.requests.find(item => item.id === accepted.id) }, queue: journal.requests.filter(item => matches(item) && item.state !== 'delivered').map(item => ({ ...item })) }));
    accepted = snapshot.accepted; const queue = snapshot.queue;
    if (accepted.state === 'delivered') return already();
    let warnings = queue.some(entry => entry.state === 'uncertain'), sentAccepted = false;
    if (accepted.state === 'uncertain') return uncertain();
    if (accepted.inFlight) return progress(accepted);
    for (const entry of queue) {
      if (entry.state === 'uncertain') continue;
      if (entry.inFlight) return progress(entry);
      run = latest(); if (!targetCurrent(run)) return failure({ code: 'chat_target_changed' });
      const message = entry.kind === 'answer' ? `${ANSWER_PREFIX}: ${entry.text} Go on with the step.`
        : `${CHANGE_PREFIX}: ${entry.text} Revise in this chat, run done again for the step you changed, then show the result and ask again.\nRequest ${entry.id}. After addressing it, record agent uptake with a short note:\n${uptakeCommand(entry.id, p)}`;
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
        try { return await deliveryJournal(run, p, journal => {
          if (!targetCurrent(latest())) return false;
          const saved = journal.requests.find(item => item.id === entry.id);
          if (!saved || saved.state !== 'pending' || saved.inFlight) return false;
          const first = journal.requests.find(item => matches(item) && item.state === 'pending');
          if (first?.id !== saved.id) return false;
          saved.inFlight = true; saved.owner = owner; claimed = true; return true;
        }); } catch { custodyFailed = true; return false; }
      } });
      if (custodyFailed) return fail(`Could not save submission intent; your request was not sent. ${kept}`);
      let observed;
      try {
        observed = await deliveryJournal(run, p, journal => {
          const saved = journal.requests.find(item => item.id === entry.id);
          if (!saved) throw Error('Saved request unavailable');
          if (!claimed || saved.owner?.token !== owner.token) return { ...saved };
          delete saved.inFlight; delete saved.owner;
          if (!sent.ok) { saved.state = sent.uncertain ? 'uncertain' : 'pending'; saved.code = sent.code; return { ...saved }; }
          const now = p.now(); saved.state = 'delivered'; saved.deliveredAt = now; delete saved.code;
          commitRun(run,p,current=>{
          current.changes.push({ stage: entry.area, round: current.changes.filter(change => change.stage === entry.area).length + 1, text: entry.text, at: now, ...(entry.kind === 'answer' ? { answer: true } : {}) });
          if (targetCurrent(current)) {
            if (equalFact(current.question,entry.question))current.question=null;
            if(entry.kind==='answer'){if(!current.gate&&!current.question)current.state='running';}
            else if(current.gate&&equalFact(current.gate,entry.gate)){current.gate.id=p.randomUUID();current.gate.at=now;delete current.gate.promptSnapshot;}
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
    return done((answer ? `Sent your answer to the ${area.name} chat of #${run.number}. The agent goes on with the step.`
      : `Sent your change request to the ${area.name} chat of #${run.number}.${run.gate ? ' The gate stays open.' : ''}`) + (!answer ? `\n${uptakeReceipt(accepted, p)}` : '') + (warnings ? `\n${warning}` : ''));
  } catch (error) { return fail(`Could not update the saved request. Wait briefly, then retry; check the original chat (${error.code ?? 'journal unavailable'}).`); }
  finally { activeDeliveries.delete(owner.token); }
}

async function cancelRunCommand({ ref, cwd }, ports) {
  const p = deps(ports);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  if (run.state === 'cancelled') return done(`The run for ${run.repo}#${run.number} is already cancelled.`);
  p.say('Closing the chat tabs in Herdr…');
  const { warnings } = await closeChats(run, {...p, checkpoint: async (_chat, layout) => {
    if (layout) {
      // Sample the outside clock before ordinary ownership so concurrent progress
      // is visible to the checkpoint's fresh read rather than a nested save.
      const at = p.now();
      commitRun(run,{...p,now:()=>at},latest=>{latest.layout=structuredClone(layout);});
    }
  }});
  const cancelled={state:'cancelled',at:p.now()};
  commitRun(run,p,latest=>{latest.state='cancelled';latest.cancelled=cancelled;latest.gate=null;});
  return done([...warnings, `Cancelled the run for ${run.repo}#${run.number} and closed its Herdr tabs.`,
    `The worktree stays at ${run.root} (branch ${run.branch}).`].join('\n'));
}

async function refreshPr(run, p) {
  if (!run.pr?.length || run.state === 'cancelled') return;
  const cwd=existsSync(run.root)?run.root:run.sourceRoot,observations=[];
  for(const pr of run.pr)observations.push({url:pr.url,number:pr.number,stage:pr.stage,fields:await (p.readPrStatus??readWorkflowPrStatus)({cwd,url:pr.url},p.commandPorts)});
  const checkedAt=p.now();
  if(!observations.some(observation=>{
    const pr=run.pr.find(pr=>pr.url===observation.url&&pr.number===observation.number&&pr.stage===observation.stage);
    return Object.entries(observation.fields).some(([key,value])=>!equalFact(pr[key],value));
  }))return;
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
  });
}

// What Herdr shows for the current chat of a running run or a run at a gate, with one Herdr call: 'blocked' (a question
// dialog), 'working', 'stopped' (the saved chat state is ended: evidence, never "not seen yet"), 'starting' (an unconfirmed
// start after the shared grace), 'unavailable', or null (idle, still within the grace, or pdd cannot tell, and status keeps
// its words). A lifecycle change is saved into the same chat of the run record.
async function chatState(run, p) {
  if (run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase)) return 'unconfirmed';
  if (ended(run)) return null;
  const area = run.areas[run.area], failure = activeChatFailure(run), chat = currentChat(run);
  if (!chat) return failure || !run.gate && !prOf(run, area?.name) ? 'unconfirmed' : null;
  if (!(run.state === 'running' || run.gate || failure)) return null;
  const live = await chatSession(chat, p);
  // A never-seen chat after the grace counts as ended only when its own native session shows that the agent ran.
  const own = sessionEvidenceDue(chat, live, p.now()) && !observedSession(chat, chat.agent ?? run.agent) ? await ownSession({ run, chat, since: launchAnchor(chat), ports: p }) : null;
  const observed = observeLifecycle(chat, live, p.now(), chat.agent ?? run.agent, own?.kind === 'match' ? own.id : null);
  // Status saves only positive facts: the exact live agent (running) or end evidence. An unclear observation changes nothing.
  const next = structuredClone(chat);
  if (observed.state === 'ended' || observed.state === 'running' && observed.exact) applyLifecycle(next, observed);
  if (live.alive) delete next.startUnconfirmed;
  const recovered = live.alive && failure;
  if (!sameFact(next, chat) || recovered) {
    commitRun(run,p,latest=>{
      const saved=latest.chats.find(item=>sameChat(item,chat));
      if(saved&&sameFact(saved,chat))copyObservation(saved,next);
      if(recovered&&equalFact(latest.chatFailure,failure))clearChatFailure(latest);
    });
  }
  if (live.alive) return ['blocked', 'working'].includes(live.status) ? live.status : null;
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
  if (run.gate?.kind === 'ask-code') return { drafts: await pr1Drafts(run, p) };
  if (run.gate?.kind === 'approve-pr') return { nothing: nothingToTry(run, run.areas[run.area], await worktreeContents(run, p)) };
  return {};
}

function detail(run, chat = null, facts = {}) {
  const drafts = facts.drafts ?? [], stories = storyCount(run);
  const area = run.areas[run.area], tab = currentChat(run) ?? run.chats?.at(-1);
  const ci = pr => ({ passing: 'CI passing', failing: 'CI failing', pending: 'CI running', none: 'no CI checks' }[pr.ci] ?? 'CI unknown');
  const steps = (area?.steps ?? []).map(step => `${step} ${run.done[step] ? 'done' : 'to do'}${run.done[step]?.summary ? ` ("${clip(oneLine(run.done[step].summary), 120)}")` : ''}`);
  const pending = run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase);
  const next = pending ? `pdd workflow open ${run.number} --new` : activeChatFailure(run) || ['unconfirmed', 'unavailable', 'starting'].includes(chat) ? `pdd workflow open ${run.number}`
    : run.gate ? approvalGuide(run)
    : ended(run) ? null : prOf(run, area?.name) ? `Review and merge ${run.pr.length > 1 && run.prBase && run.prBase !== run.baseBranch ? 'PR 1, then PR 2,' : 'the PR'} on GitHub. pdd never merges.` : `pdd workflow open ${run.number}`;
  return [`${run.repo}#${run.number} "${oneLine(run.issue.title)}" · ${run.workflow} · ${run.agent}`,
    `State: ${describe(run, chat, facts)}`,
    ...(pending ? [`Chat replacement pending: ${run.chatReplacement.phase}; retry pdd workflow open ${run.number} --new, or end with pdd workflow cancel ${run.number}.`] : []),
    ...(pending && run.chatReplacement.phase==='launchRequested' ? ['After startup grace, --new sends the saved launch once only if authoritative inspection proves the latest request never ran; unknown or agent processes keep it pending.'] : []),
    ...(area ? [`Area ${run.area + 1} of ${run.areas.length}: ${area.name} — ${steps.join(', ')}`] : []),
    ...(tab && !ended(run) ? [`Chat: Herdr session pdd, tab "${tab.label}" — pdd workflow open ${run.number}`] : []),
    ...(run.pr ?? []).map(pr => { const label = prLabel(run, run.areas.find(item => item.name === pr.stage) ?? {}); return `${label === 'the PR' ? 'PR' : label}: ${pr.url} — ${pr.state ?? 'open'}, ${ci(pr)}${pr.base && pr.base !== run.baseBranch ? ` (stacked on ${pr.base})` : ''}`; }),
    ...(drafts.length ? [draftLine(drafts)] : []),
    ...(stories ? [`Stories: ${storyText(stories)}${stories.failing.length ? ` (✗ ${stories.failing.join(', ')})` : ''}`,
      ...(stories.unknown?.length ? [`Unknown Stories: ${stories.unknown.join(', ')}`] : []),
      ...(stories.evidence ? [stories.evidence] : [])] : []),
    `Worktree: ${run.root} (branch ${run.branch})`, `Run folder: ${run.runDir}`, `Review without resuming: pdd workflow view ${run.repo}#${run.number}`, ...(next ? [`Next: ${next}`] : [])].join('\n');
}

// One list line per run, grouped by what it needs: the person, the agent, a PR review, nothing.
const GROUPS = ['waiting', 'working', 'pr-open', 'done', 'cancelled'];
function summary(run, timeZone, chat = null, { drafts = [], nothing = false } = {}) {
  const area = run.areas[run.area], ask = askArea(run), running = run.state === 'running';
  const replacementPending = run.chatReplacement && !['launched','rolledBack','ended'].includes(run.chatReplacement.phase);
  const problem = replacementPending || activeChatFailure(run) || ['unconfirmed', 'unavailable', 'starting'].includes(chat);
  const question = openQuestion(run), writing = !problem && Boolean(run.gate) && !question && chat === 'working';
  const group = run.state === 'cancelled' ? 'cancelled' : run.state === 'completed' ? 'done' : problem ? 'waiting' : writing ? 'working'
    : run.gate || question || running && ['blocked', 'stopped'].includes(chat) ? 'waiting' : prOf(run, area?.name) ? 'pr-open' : 'working';
  const step = area?.steps.find(item => !run.done[item]);
  const words = group === 'cancelled' ? (run.cancelled?.state === 'replaced' ? 'replaced' : 'cancelled')
    : group === 'done' ? (run.gate?.kind === 'ask-code' ? 'done at PR 1' : 'done')
    : replacementPending ? `chat replacement pending at ${run.chatReplacement.phase}; run pdd workflow open ${run.number} --new`
    : problem ? chatStatusWords(run, chat)
    : question ? `waiting for you: ${question.text.split('\n')[0]}`
    : !run.gate && running && chat === 'blocked' ? `waiting for you: the chat asks a question in its window`
    : !run.gate && running && chat === 'stopped' ? `the chat stopped: run pdd workflow open ${run.number}`
    : writing ? (revising(run) ? 'agent working on your changes' : 'agent writing the gate message')
    : run.gate?.kind === 'ask-code' && drafts.length ? `waiting for you: approve the draft prompt${drafts.length > 1 ? 's' : ''}, then the code PR (PR 1 open)`
    : run.gate?.kind === 'ask-code' ? 'waiting for you: code PR now or stop (PR 1 open)'
    : run.gate?.kind === 'approve-pr' ? `waiting for you: ${nothing ? '' : 'try it, then '}approve to open ${area.then === 'ask-code' ? 'PR 1' : 'the PR'}`
    : run.gate ? `waiting for you: approve the ${run.gate.area}`
    : group === 'pr-open' ? `${!ask ? 'PR' : area.then === 'ask-code' ? 'PR 1' : 'PR 2'} open`
    : step ? `agent working on ${step}` : 'agent working';
  const ref = `${run.repo}#${run.number}`;
  const when = Number.isFinite(run.updatedAt) ? new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit', hourCycle: 'h23', ...(timeZone ? { timeZone } : {}) }).format(new Date(run.updatedAt)) : 'unknown time';
  const prs = (run.pr ?? []).map(pr => ({ number: pr.number, url: pr.url, state: pr.state ?? 'open' })), stories = storyCount(run);
  return { ref, repo: run.repo, number: run.number, workflow: run.workflow, area: area?.name ?? null, group, words, prs, stories,
    updatedAt: run.updatedAt ?? null, root: run.root, runDir: run.runDir, viewCommand: `pdd workflow view ${ref}`,
    line: [ref, run.workflow, area?.name ?? '?', words, ...(stories ? [storyText(stories)] : []), ...(prs.length ? [`PR ${prs.map(pr => `#${pr.number}`).join(' ')}`] : []), when].join(' · ') };
}

function ownershipLines(owner) {
  return owner?[`Workflow progress ownership: ${owner.path}; PID ${owner.pid??'unknown'}, host ${owner.hostname??'unknown'}, token ${owner.token??'unknown'}.${owner.warning?` ${owner.warning}.`:''} If no pdd command is running, inspect and remove this ownership folder, then retry.`]:[];
}

async function listStatus(runs, { json, cancelled, scope, snapshotOnly=false }, p) {
  const reading = runs.filter(run => run.state === 'waiting' && run.pr?.length).reduce((sum, run) => sum + run.pr.length, 0);
  if (reading) p.say(`Reading ${reading} PR${reading === 1 ? '' : 's'} from GitHub…`);
  for (const run of runs) if (!snapshotOnly && !readRunOwnership(run.runDir,p) && run.state === 'waiting' && run.pr?.length) { try { await refreshPr(run, p); } catch(error) { if(error?.code==='workflow_run_save_failed')throw error; /* A PR read failure keeps the saved state. */ } }
  const all = [];
  for (const run of runs) {
    const ordinaryOwnership=readRunOwnership(run.runDir,p);
    const item = summary(run, p.timeZone, ordinaryOwnership||snapshotOnly?null:await chatState(run, p), ended(run)||ordinaryOwnership||snapshotOnly ? {} : await gateFacts(run, p));
    const snapshot = requestSnapshot(run, p);
    all.push({ ...item, ...snapshot, ordinaryOwnership, line: [item.line, ...ownershipLines(ordinaryOwnership), ...requestLines(snapshot, { openOnly: true, ended: ended(run), p })].join('\n') });
  }
  const hidden = cancelled ? 0 : all.filter(item => item.group === 'cancelled').length;
  const shown = all.filter(item => cancelled || item.group !== 'cancelled')
    .sort((a, b) => GROUPS.indexOf(a.group) - GROUPS.indexOf(b.group) || (b.updatedAt ?? 0) - (a.updatedAt ?? 0));
  if (json) return done(JSON.stringify({ runs: shown.map(({ line, ...item }) => item) }, null, 2));
  if (!shown.length) return done([`No pdd runs ${scope}.${hidden ? ` ${hidden} cancelled run${hidden > 1 ? 's' : ''} hidden; add --cancelled to see ${hidden > 1 ? 'them' : 'it'}.` : ''}`, 'Start one with: pdd workflow run NAME ISSUE'].join('\n'));
  return done([...shown.map(item => item.line),
    ...(hidden ? [`${hidden} cancelled run${hidden > 1 ? 's' : ''} hidden; add --cancelled to see ${hidden > 1 ? 'them' : 'it'}.`] : []),
    `Review without resuming: pdd workflow view ${shown[0].ref}`, `Open one: pdd workflow open ${shown[0].ref}`].join('\n'));
}

async function runStatusCommand({ ref, cwd, all = false, json = false, cancelled = false }, ports, snapshotOnly=false) {
  const p = deps(ports);
  if (ref === undefined && (all || !(await gitContext(cwd, p)))) return listStatus(allRuns({ cancelled }, p), { json, cancelled, scope: 'on this machine', snapshotOnly }, p);
  if (ref === undefined && !(await runForWorktree(cwd, p))) return listStatus(await listRuns({ cwd, cancelled }, p), { json, cancelled, scope: 'in this repository', snapshotOnly }, p);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  if (found.run.pr?.length && found.run.state !== 'cancelled') p.say(`Reading ${found.run.pr.length === 1 ? 'the PR' : `${found.run.pr.length} PRs`} from GitHub…`);
  const ordinaryOwnership=readRunOwnership(found.run.runDir,p);
  if(!ordinaryOwnership&&!snapshotOnly)await refreshPr(found.run, p);
  const run = found.run, facts = ended(run)||ordinaryOwnership||snapshotOnly ? {} : await gateFacts(run, p), chat = ordinaryOwnership||snapshotOnly?null:await chatState(run, p);
  const snapshot = requestSnapshot(run, p);
  if (json) { const { line, ...item } = summary(run, p.timeZone, chat, facts); return done(JSON.stringify({ runs: [{ ...item, ...snapshot, ordinaryOwnership }] }, null, 2)); }
  return done([detail(run, chat, facts), ...ownershipLines(ordinaryOwnership), ...requestLines(snapshot, { ended: ended(run), p })].join('\n'));
}

const replacementPhases = ['intent', 'closeRequested', 'closed', 'createRequested', 'prepared', 'launchRequested', 'launched', 'rolledBack', 'ended'];
function validReplacement(record, run) {
  if (!record || typeof record !== 'object' || Array.isArray(record) || Object.keys(record).some(key => !['id', 'area', 'phase', 'at', 'original', 'replacement', 'recovery'].includes(key)) || !validSessionId(record.id) || !Number.isSafeInteger(record.at) || record.at < 0 || !replacementPhases.includes(record.phase) || !run.areas.slice(0, run.area + 1).some(area => area.name === record.area)) return false;
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
function saveChatObservations(run, original, observed, p, { error, phase = 'open', reset = false, checkpoint = false, layout = null } = {}) {
  const area = original?.area ?? observed?.area ?? run.areas[run.area].name;
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
    // A late failed open of an area that is no longer current keeps its own record, but never replaces a current failure.
    if (error && phase === 'open' && fresh.areas[fresh.area].name !== area && !activeChatFailure(fresh))
      fresh.chatFailure = { area, phase, code: oneLine(error.code ?? 'error').slice(0, 100), message: oneLine(error.message ?? 'Herdr request failed').slice(0, 500), at: p.now() };
    if (fresh.areas[fresh.area].name === area && sameFact(fresh.chatFailure, run.chatFailure)) {
      const stateFields = ['state', 'area', 'done', 'gate', 'question', 'approvalRecord', 'decisions'];
      const unchanged = stateFields.every(key => sameFact(fresh[key], run[key]));
      if (error) {
        fresh.chatFailure = { area, phase, code: oneLine(error.code ?? 'error').slice(0, 100), message: oneLine(error.message ?? 'Herdr request failed').slice(0, 500), at: p.now() };
        if (unchanged) fresh.state = 'waiting';
      } else if (fresh.chatFailure) {
        if (unchanged) clearChatFailure(fresh);
        else delete fresh.chatFailure;
      }
    }
  });
}
async function openRunLocked({ ref, cwd, area, newSession = false, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  if (ended(run)) return fail(`The run for ${run.repo}#${run.number} is ${run.state}. Its worktree is ${run.root}.`);
  const selected = area === undefined ? run.area : run.areas.findIndex(item => item.name === area);
  let chat = [...(run.chats ?? [])].reverse().find(item => item.area === run.areas[selected]?.name), started = false, handedOff = false;
  if (selected < 0) return fail(`Unknown area ${area}. Valid areas: ${run.areas.map(item => item.name).join(', ')}.`);
  if (selected > run.area || area !== undefined && !chat) return fail(`The area ${area} has no recorded chat at or before the current area.`);
  const historical = selected < run.area;
  const areaOriginal = area !== undefined && !newSession ? structuredClone(chat) : null;
  let defaultOriginal = chat ? structuredClone(chat) : undefined;
  if (newSession && historical) return fail(`Select the current area ${run.areas[run.area].name} to start a new session; earlier areas cannot be replaced.`);
  if (newSession && !chat && (!run.chatReplacement || ['launched','rolledBack','ended'].includes(run.chatReplacement.phase))) return fail('The current area has no saved chat to replace. Open it first.');
  const missing = missingHome(run, p.env);
  if (missing) return fail(missing);
  const pending = run.chatReplacement;
  if (pending !== undefined) {
    if (!validReplacement(pending, run)) return fail('The saved chat replacement record is malformed or unknown. Inspect it before opening a chat.');
    if (!['launched', 'rolledBack', 'ended'].includes(pending.phase) && !newSession) return fail(`Chat replacement is pending at ${pending.phase}. Retry: pdd workflow open ${run.number} --new`);
  }

  try {
    if (newSession) {
      const recovering = pending && !['launched','rolledBack','ended'].includes(pending.phase);
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
      const checkpoint = async record => {
        if (!validReplacement(record, run)) throw Object.assign(Error('Invalid replacement checkpoint'), { code: 'invalid_replacement_checkpoint' });
        const admit = fresh => {
          if (!fresh || ended(fresh)) throw Object.assign(Error('The run ended during replacement.'), {code:'run_ended'});
          const prior = fresh.chatReplacement;
          const sameAttempt = prior && prior.id === record.id && prior.at === record.at && sameFact(prior.original, record.original);
          if (record.phase === 'intent' && !sameAttempt) {
            if (prior && !['launched','rolledBack','ended'].includes(prior.phase)) throw Error('Replacement already pending');
            if (prior?.id === record.id) throw Error('Invalid replacement transition');
          } else if (!sameAttempt || record.phase === 'intent' && prior.phase !== 'intent') throw Error('Invalid replacement transition');
          return sameAttempt;
        };
        admit(readRun(run.runDir));
        commitRun(run, p, fresh => {
          if (!admit(fresh)) (fresh.abandonedChats ??= []).push({ ...record.original, replacementId: record.id, abandonedAt: record.at, reason: 'explicit-new-session' });
          fresh.chatReplacement = structuredClone(record);
          if (['launchRequested', 'launched', 'rolledBack'].includes(record.phase)) {
            fresh.chats = fresh.chats.filter(item => item.area !== record.area);
            fresh.chats.push(record.phase === 'rolledBack' ? {...record.original, messageFile: record.original.originalMessageFile} : {...record.replacement});
          }
          if (['launched','rolledBack','ended'].includes(record.phase) && record.area === fresh.areas[fresh.area]?.name) clearChatFailure(fresh);
        });
      };
      chat = await restartChat({ run, chat, message, pending: pending && !['launched','rolledBack','ended'].includes(pending.phase) ? pending : undefined }, { ...p, checkpoint });
      if (run.chatReplacement?.phase === 'ended') return done(`Ended the historical ${chat.area} replacement attempt without launching or resuming it. The current chat and progress are kept.`);
      if (run.chatReplacement?.phase === 'rolledBack') return done(`Restored the usable ${chat.area} chat. The same replacement attempt was rolled back.`);
      if (run.chatReplacement?.recovery?.resumeRequested) return done(`Resumed this attempt's ${chat.area} session in Herdr session pdd; no second first message was sent. The run, completed work, gates and approvals are kept.`);
      return done(`Started one fresh ${chat.area} chat in Herdr session pdd. The run, completed work, gates and approvals are kept.`);
    }
    if (!chat) { chat = await startNextChat(run, p, packageRoot); defaultOriginal = structuredClone(chat); started = true; }
    p.say(`Opening the ${chat.area} chat in Herdr…`);
    const opened = await openChat({ run, chat }, { ...p, beforeAttach: async () => {
      if (areaOriginal) saveAreaObservations(run, areaOriginal, chat, p);
      else saveChatObservations(run, defaultOriginal, chat, p);
      handedOff = true;
      p.releaseRunLock?.();
    } });
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
    return done([...shownGate, ...(gateRun.gate ? [approvalGuide(gateRun, p.pdd)] : []), started ? `Started the ${chat.area} chat in ${where}.` : opened.resumed ? `Resumed the ${chat.area} chat in ${where}.` : `The ${chat.area} chat is in ${where}.`,
      ...(opened.attached ? [] : [p.env.HERDR_ENV === '1' ? 'pdd focused that tab. If you are in another Herdr session, run: herdr session attach pdd' : 'See it with: herdr session attach pdd'])].join('\n'));
  } catch (error) {
    if (newSession) return fail(`Chat replacement ${run.chatReplacement?.phase ?? 'refused'} (${error.code ?? 'error'}: ${oneLine(error.message)}).${run.chatReplacement ? ` Retry: pdd workflow open ${run.number} --new` : ''}`);
    if (!handedOff) {
      if (areaOriginal) saveAreaObservations(run, areaOriginal, chat, p);
      else saveChatObservations(run, defaultOriginal, chat, p, { error, phase: chat ? 'open' : 'start' });
    }
    // A starting chat is not a failed one: say so, with the one safe next step.
    if (['chat_start_unconfirmed', 'chat_start_failed'].includes(error.code)) return fail(oneLine(error.message));
    return fail(`pdd could not open the ${run.areas[selected].name} chat (${error.code ?? 'error'}: ${oneLine(error.message)}).`);
  }
}

const openRunCommand = (args, ports) => lockedMutation(args, ports, openRunLocked);

export const startRun=saveGuard(startRunCommand);

export const recordEvidence=saveGuard(recordEvidenceCommand);

export const stepDone=saveGuard(stepDoneCommand);

export const approveRun=saveGuard(approveRunCommand);

export const askPerson=saveGuard(askPersonCommand);

export const cancelRun=saveGuard(cancelRunCommand);

export const runStatus=saveGuard(async(options,ports)=>{
  try{return await runStatusCommand(options,ports);}
  catch(error){
    if(error?.code==='workflow_run_save_failed'&&error.cause?.code==='workflow_run_busy')return runStatusCommand(options,ports,true);
    throw error;
  }
});

export const openRun=saveGuard(openRunCommand);
