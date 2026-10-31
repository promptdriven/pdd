// Generated from prompts/cli/workflow-runner.prompt.md (sha256: e425fed6c33bcdafc1f4d673460978e07dc83966e4505b46414f988a0a545385).
import { execFile as execFileCallback } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { existsSync, lstatSync, mkdirSync, readFileSync, realpathSync, renameSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { createInterface } from 'node:readline/promises';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { readWorkflowAreas } from './workflow-areas.mjs';
import { resolveWorkflowIssue, prepareWorkflowPr, publishWorkflowPr, readWorkflowPrStatus } from './workflow-github.mjs';
import { allocateIssueWorktree, releaseIssueClaim } from './workflow-worktree.mjs';
import { allRuns, currentChat, gitContext, listRuns, readRun, resolveRun, runDirFor, runForWorktree, writeRun } from './workflow-runs.mjs';
import { startChat, sendToChat, chatSession, openChat, closeChats, expandHome, homeVariable, isFolder } from './workflow-chat.mjs';
import { captureSource, findTests, gitFiles, interfaceBlocks } from './runtime-preflight.mjs';
import { storyLines } from './runtime-output.mjs';
import { PDD_HERDR_SESSION } from './workflow-herdr-layout.mjs';
import { causeText } from './runtime-output.mjs';
import { preparePrEvidence } from './workflow-pr-evidence.mjs';
import { collectTestInventory } from './workflow-inventory.mjs';
import {REPLAY_POLICY,sourceFingerprint as gitFingerprint,pinReplayVectors,readReplayEvidence,formatReplayEvidence} from './workflow-replay.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const CHANGE_PREFIX = 'The person asks for changes';
const ANSWER_PREFIX = 'The person answers your question';
// At the code gate a chat reply must say yes in plain words; at other gates any reply from the person counts.
const YES_WORDS = /\b(?:yes|approved?|build the code|go ahead|code pr now|continue)\b/i;
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
// A step summary keeps its line breaks (0.1.6: the chat pastes one Runtime check line per line); blank lines go.
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
  return { ...ports, env, execFile, commandPorts: ports.execFile ? { execFile: ports.execFile } : {}, now: ports.now ?? Date.now,
    isTTY: ports.isTTY ?? Boolean(process.stdin.isTTY && process.stderr.isTTY), say: ports.say ?? (() => {}) };
}
// The real reason of a failed gh, git or Herdr call, in plain words.
function causeOf(error) {
  if (error?.code === 'ENOENT') return `${String(error.path ?? error.message ?? '').match(/\b(herdr|gh|git)\b/)?.[1] ?? 'a needed program'} is not installed or not on PATH`;
  if (error?.code === 'workflow_github_command_unavailable') return 'gh is not installed or not on PATH';
  return causeText(error?.stderr || error?.detail) || String(error?.code ?? 'error');
}
export const pddCommand = (packageRoot = PACKAGE_ROOT) => [process.execPath, join(packageRoot, 'bin', 'pdd.mjs')].map(shell).join(' ');
const pddFor = (p, packageRoot) => p.pdd ?? pddCommand(packageRoot ?? PACKAGE_ROOT);
async function git(p, cwd, ...args) { return String((await p.execFile('git', args, { cwd })).stdout ?? '').trim(); }

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
  for (const path of await changedFiles(run,p,true)) {
    if (path.endsWith('.json') && isScenario(readFileSync(join(run.root,path),'utf8'))) paths.push(path);
  }
  return paths;
}
const replayEnabled = run => run.areas.some(area => area.replay_evidence === REPLAY_POLICY);
async function refreshReplayBaseline(run,p) {
  if (!replayEnabled(run)) return;
  try { run.replayBaseline = pinReplayVectors(run.root,await scenarioInventory(run,p)); }
  catch { run.replayBaseline = {schema_version:'pdd.replay-vectors.v1',vectors:[],outcome:'blocked',reason:'The changed scenario inventory is unavailable; repair unreadable or malformed JSON candidates and Git listing failures.'}; }
  writeRun(run,p);
}
async function currentReplayEvidence(run,p) {
  let reason;
  try {
    const saved = new Set(run.replayBaseline?.vectors?.map(vector=>vector.path) ?? []);
    const missing = (await scenarioInventory(run,p)).filter(path=>!saved.has(path));
    if (missing.length) reason = `Current scenario paths are missing from the approved anchor: ${missing.join(', ')}. Return to prompt space.`;
  } catch { reason = 'The current changed scenario inventory is unavailable; repair unreadable or malformed JSON candidates and Git listing failures.'; }
  const evidence = readReplayEvidence(run);
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
  const area = run.areas[index], pdd = p.pdd, earlier = run.areas.slice(0, index).flatMap(item => item.steps);
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
      ? `Gate: after the last step, show the person the result, ask them to approve or ask for changes, and stop. Never approve for them: they approve in their own words, or run pdd workflow approve ${run.number}.`
      : area.then === 'ask-code'
      ? 'After the last step, pdd pushes the branch and opens PR 1 (prompt, Story and tests). Then show it and ask whether to make the code PR now. Never push, open a PR or merge yourself.'
      : `After the last step, pdd pushes the branch and opens ${prLabel(run, area)}. Never push, open a PR or merge yourself.`,
    `Read the PDD skills (pdd-prompting too) from ${join(packageRoot ?? PACKAGE_ROOT, 'skills')}: an installed copy with the same name may be older.`,
  ].join('\n') + '\n';
}

// The one sentence a person gets when they stop at PR 1 (0.1.4: testers saw the chat drop it when it was a hint).
const codeLater = run => `To make the code PR later, run \`pdd workflow approve ${run.number}\`.`;
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
const approveFirst = (run, drafts) => `Approve the prompt${drafts.length > 1 ? 's' : ''} first: cd ${shell(run.root)} && ${drafts.map(path => `pdd approve ${shell(path)}`).join(' && ')}. Then run pdd workflow approve ${run.number} to start the code PR.`;

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
const chatStatusWords = (run, chat) => activeChatFailure(run) ? chatFailureWords(run)
  : chat === 'unavailable' ? `Herdr status unavailable (server_unavailable); chat activity is unknown. Run pdd workflow open ${run.number} after Herdr is available.`
  : `chat startup is not confirmed. Run pdd workflow open ${run.number} after Herdr is available.`;
function recordChatFailure(run, error, phase, p) {
  run.chatFailure = { area: run.areas[run.area].name, phase, code: oneLine(error.code ?? 'error').slice(0, 100), message: oneLine(error.message ?? 'Herdr request failed').slice(0, 500), at: p.now() };
  if (!ended(run)) run.state = 'waiting';
  writeRun(run, p);
}
function clearChatFailure(run) {
  if (!run.chatFailure) return;
  delete run.chatFailure;
  if (!ended(run) && !run.gate && !openQuestion(run)) run.state = 'running';
}

// A gate whose chat still works: after a change request it revises, else it writes the gate message (0.1.6 tester: status
// said "waiting for you" about a minute before the chat had asked).
const revising = run => { const last = run.changes?.at(-1); return Boolean(last && !last.answer && last.stage === run.gate.area && last.at >= run.gate.at); };
// chat: what Herdr shows (chatState); facts: {drafts, nothing} read by the caller (gateFacts). describe itself makes no calls.
function describe(run, chat = null, { drafts = [], nothing = false } = {}) {
  const area = run.areas[run.area], pr1 = askArea(run) && prOf(run, askArea(run).name);
  if (run.state === 'cancelled') return 'cancelled';
  if (activeChatFailure(run) || ['unconfirmed', 'unavailable'].includes(chat)) return chatStatusWords(run, chat);
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

export async function startRun({ name, issue, agent = 'codex', base, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  let workflow;
  try { workflow = readWorkflowAreas({ packageRoot, name, cwd, home: p.env.HOME || homedir() }); } catch (error) { return fail(error.message); }
  if (!['codex', 'claude'].includes(agent)) return fail('Choose --agent codex or --agent claude.');
  // Every chat of the run uses this config folder; a missing one makes the agent stop at once (0.1.6 tester).
  const variable = homeVariable(agent), configDir = p.env[variable] ? resolve(cwd, expandHome(p.env[variable], p.env)) : null;
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
  if (existing && existing.state !== 'cancelled') return fail(`Issue #${number} already has a run (${existing.workflow}, ${describe(existing)}). Open it: pdd workflow open ${number}. Status: pdd workflow status ${number}.`);
  const warnings = [], baseBranch = explicitBase ? base : binding.defaultBranch;
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
  if (existing) {
    const released = await releaseIssueClaim({ cwd: context.toplevel, runId: existing.runId, issueNumber: number }, p.commandPorts);
    if (released.state !== 'released') return fail(`Issue #${number} has a cancelled run, but pdd could not free the issue: ${released.message}`);
    warnings.push(`Issue #${number} had a cancelled run. Its worktree stays at ${existing.root} (branch ${existing.branch}). This run gets a new worktree and branch.`);
  }
  if (!explicitBase) {
    p.say(`Fetching origin/${baseBranch}…`);
    try { await p.execFile('git', ['fetch', 'origin', baseBranch], { cwd: context.toplevel }); }
    catch { warnings.push(`warning: "git fetch origin ${baseBranch}" failed; the worktree starts from the last fetched ${baseBranch}.`); }
  }
  const runId = randomUUID();
  p.say(`Making the worktree and branch for #${number}…`);
  const allocated = await allocateIssueWorktree({ cwd: context.toplevel, repository: binding.repository, issueNumber: number, runId,
    workflowName: name, baseRef: `refs/remotes/origin/${baseBranch}` }, p.commandPorts);
  if (allocated.state !== 'ready' || !allocated.assignment) return fail(`pdd could not make the worktree for #${number}: ${allocated.message}`);
  const a = allocated.assignment;
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
  writeRun(run, p);
  const first = workflow.areas[0];
  try { await startNextChat(run, p, packageRoot); }
  catch (error) {
    run.warnings.push(`The ${first.name} chat startup was not confirmed (${error.code ?? 'error'}).`); writeRun(run, p);
    return fail([...warnings, `The worktree is ready at ${a.worktreePath}, but the ${first.name} chat startup was not confirmed (${error.code === 'ENOENT' ? causeOf(error) : `${error.code ?? 'error'}: ${oneLine(error.message)}`}).`,
      `Start it with: pdd workflow open ${number}`].join('\n'));
  }
  writeRun(run, p);
  const chat = run.chats[0];
  return done([...warnings,
    `Started ${name} for ${run.repo}#${number} "${oneLine(run.issue.title)}".`,
    `Area 1 of ${run.areas.length}: ${first.name} (${first.steps.join(', ')}). ${agent === 'claude' ? 'Claude' : 'Codex'} works in Herdr session pdd, tab "${chat.label}".`,
    ...(agent === 'claude' && !claudeTrusts(run.sourceRoot, run.configDir, p.env) ? ['Claude may first ask you to trust the new worktree folder. Open the chat and choose "Yes, I trust this folder".'] : []),
    `Base: origin/${run.baseBranch}`,
    `Worktree: ${run.root} (branch ${run.branch})`,
    `Run folder: ${runDir}`,
    `Watch the chat: pdd workflow open ${number}`,
    `Status:         pdd workflow status ${number}`,
    `When the ${first.name} area is ready, approve it in the chat or run: pdd workflow approve ${number}`,
    'You can close this terminal. The chat keeps working in Herdr.'].join('\n'));
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
// Runtime check lines in a step summary (0.1.6): "Runtime check (<story>) (DRAFT)?: …" per Story, and the overall
// "Runtime check: …". The chat pastes the lines that pdd check prints, one per line or joined with "; "; a result ends
// at a line break, ";", a "Report" line, a link or the next Runtime check.
export function runtimeLines(text) {
  return [...String(text ?? '').matchAll(/Runtime check((?:\s*\([^)]*\))*):\s*(.*?)(?=\n|\s*(?:;|\bReport\b|https?:\/\/|Runtime check|$))/gs)].map(match => {
    const groups = [...match[1].matchAll(/\(([^)]*)\)/g)].map(group => group[1].trim());
    const story = groups.find(group => group && group.toUpperCase() !== 'DRAFT' && group !== 'all Stories') ?? null;
    const result = match[2].replace(/\s+/g, ' ').trim().replace(/[.,]$/, '');
    return { story, draft: groups.some(group => group.toUpperCase() === 'DRAFT'), result,
      line: `Runtime check${match[1].replace(/\s+/g, ' ')}: ${result}`, pass: result.includes('✓') && !result.includes('✗') };
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
  return `Runtime check (all Stories)${stories.some(line => line.draft) ? ' (DRAFT)' : ''}: ${result}`;
}
// The Runtime check lines for the top of a PR: with Story names, one line per Story and then pdd's total (when there
// are two or more); without, the lines as the chat wrote them.
function runtimeTop(text) {
  const lines = runtimeLines(text), stories = latestStories(lines);
  if (!stories.length) return lines.map(line => line.line);
  return [...stories.map(line => line.line), ...(stories.length > 1 ? [totalLine(stories)] : [])];
}
export function matchesSource(record, root, fingerprint) {
  const source = record.source;
  if (!source?.sha256) return false;
  if (source.kind === 'git-content-v1') return fingerprint !== null && fingerprint === source.sha256;
  if (source.kind === 'runtime-capture-v1') {
    try { return captureSource(root, { tests: source.tests, appMap: null }).sha256 === source.sha256; } catch { return false; }
  }
  return false;
}
export function storyCount(run) {
  const records = [...(run.runtimeHistory ?? []), ...Object.values(run.done ?? {}), ...(run.evidence ?? [])]
    .filter(record => runtimeLines(record.summary).length).sort((a, b) => (a.at ?? 0) - (b.at ?? 0));
  if (!records.length) return null;
  const fingerprint = gitFingerprint(run.root), compatible = records.filter(record => matchesSource(record, run.root, fingerprint));
  const lines = (compatible.length ? compatible : records).flatMap(record => runtimeLines(record.summary));
  const named = latestStories(lines), counted = named.length ? named : lines.slice(-1);
  const unknown = line => !compatible.length || !line.pass && !line.result.includes('✗');
  const result = { pass: compatible.length ? counted.filter(line => line.pass).length : 0, total: counted.length,
    failing: counted.filter(line => !unknown(line) && !line.pass && line.story).map(line => line.story) };
  const unresolved = counted.filter(unknown).map(line => line.story ?? 'all Stories');
  if (unresolved.length) result.unknown = unresolved;
  if (!compatible.length) result.evidence = 'Source changed, unavailable, or not recorded; saved results are unverified.';
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
const verdictLine = text => String(text).match(/\bVerdict:[^\n]*?(?=;?\s*(?:\n|\bBefore\s*[✗✓:]|\bRuntime check\b|\bReport\b|$))/)?.[0].trim() ?? null;
const changeLine = text => String(text).match(/\bBefore\s*[✗✓:][^\n]*?(?=;?\s*(?:\n|\bVerdict:|\bRuntime check\b|\bReport\b|$))/)?.[0].trim() ?? null;

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
// verify.md in at most `room` characters: the whole report when it fits. Else each <details> block becomes one line; if it is
// still too long, its first lines that fit (cut at a line end, a code fence closed), then the lines of the cut part that report
// a failure. A note says that this is a summary and where the full report is, so no failure is dropped in silence.
function verifyFit(text, room, env, description = false) {
  const full = description ? text : verifyBody(text);
  if (characters(full) <= room) return full;
  const note = what => description
    ? `_The existing PR 1 description has ${characters(text).toLocaleString('en-US')} characters. It was shortened to fit the complete description's 60,000-character budget: ${what}._`
    : `_The full verify report has ${characters(text).toLocaleString('en-US')} characters, more than a PR description can hold (GitHub's limit is 65,536). This is a summary: ${what}. The PR author has the full report: verify.md in the run folder._`;
  const lines = [], hiddenEvidence = new Set();
  let depth = 0, summary = null;
  for (const line of full.split('\n')) {
    const opens = (line.match(/<details\b/gi) ?? []).length, closes = (line.match(/<\/details>/gi) ?? []).length;
    if (!depth && !opens) { lines.push(line); continue; }
    if (reportsFailure(line) && !/^\s*(`{3,}|~{3,})/.test(line)) hiddenEvidence.add(line.replace(/<\/?(?:details|summary)\b[^>]*>/gi, ''));
    for (const reference of reportLinks(line, env)) hiddenEvidence.add(reference);
    summary ??= /<summary>(.*?)<\/summary>/i.exec(line)?.[1].trim() || null;
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
async function publicationEvidence(run, area, p) {
  const saved = { runId: run.runId, runDir: run.runDir, root: run.root, baseSha: run.baseSha, baseBranch:run.baseBranch, workflow:run.workflow, number: run.number,
    steps: run.areas.flatMap(item => item.steps).map(step => ({ step, summary: run.done[step]?.summary ?? '' })) };
  return preparePrEvidence({ run: saved, isCode: prLabel(run, area) !== 'PR 1' }, {
    currentHead: async ({ root, baseBranch }) => {
      try { await git(p,root,'check-ref-format',`refs/heads/${baseBranch}`);await git(p,root,'fetch','origin',`refs/heads/${baseBranch}:refs/remotes/origin/${baseBranch}`);const headSha=await git(p,root,'rev-parse','--verify','HEAD^{commit}');return {headSha,baseSha:await git(p,root,'merge-base',headSha,`refs/remotes/origin/${baseBranch}`),error:''}; }
      catch { return { headSha: '', baseSha:'', error: 'Current Git head unavailable.' }; }
    }
  });
}
function evidenceFit(lines, room, env) {
  if (characters(lines.join('\n')) <= room) return lines;
  const kept = [], omitted = [];
  const notice = rows => `Evidence omitted: ${rows.length} labels, ${rows.filter(reportsFailure).length} failure lines, ${rows.flatMap(line => reportLinks(line, env)).length} report references. The full evidence remains in the run folder.`;
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
function prBody(run, area, env, drafts = [], tests = true, evidence) {
  const index = run.areas.indexOf(area), from = run.areas.slice(0, index).map((item, at) => item.gate === 'pr' ? at + 1 : 0).reduce((a, b) => Math.max(a, b), 0);
  const steps = run.areas.slice(from, index + 1).flatMap(item => item.steps).filter(step => run.done[step]);
  const raw = Object.fromEntries(steps.map(step => [step, hideLocalPaths(redactTry(withoutForgedMachineLines(run.done[step].summary)), run)]));
  const summaries = Object.fromEntries(steps.map(step => [step, oneLine(raw[step])]));
  const lines = steps.map(step => `- **${step}**: ${shortLine(summaries[step]) || 'done'}`);
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
  const failing = verify?.split('\n').find(row => row.trim())?.trim().startsWith('✗') ? [verify.split('\n').find(row => row.trim()).trim()] : [];
  // The Runtime check line and its report link go on top (#18).
  // The check step's result wins; else the latest step that reports a Runtime check. One line per Story (0.1.6), then the overall line.
  // Lines are read from the summary as stored, with its line breaks.
  const checked = /Runtime check/.test(raw.check ?? '') ? raw.check : Object.values(raw).reverse().find(text => /Runtime check/.test(text));
  // A bug check starts its summary with the verdict and "Before ✗ … → after ✓ …" (0.1.7): they go above the Runtime check
  // lines, and their report links are not listed again.
  const sources = [raw.check, ...Object.values(raw).reverse()].filter(Boolean);
  const verdict = sources.map(text => verdictLine(text)).find(Boolean), change = sources.map(text => changeLine(text)).find(Boolean);
  const shown = change?.match(/https?:\/\/[^\s;]+/g) ?? [];
  const reports = checked ? reportLinks(checked, env).filter(row => !shown.some(url => row.includes(` ${url} `))) : [];
  const report = reports[0] ?? null, noted = report || (change && hasReportLink(change, env));
  const runtime = checked ? [...runtimeTop(checked), ...reports] : [];
  const replay = area.replay_evidence === REPLAY_POLICY ? [formatReplayEvidence(run.replayEvidence ?? readReplayEvidence(run)), ''] : [];
  const prefix = [...failing, ...replay];
  const top = [...(verdict ? [verdict] : []), ...(change ? [hasReportLink(change, env) ? `${change} (report links expire after 7 days)` : change] : []), ...runtime];
  if (evidence.lines.some(line => line.includes('pdd-workflow:'))) throw Error('Remove supplied workflow ownership markers from the report; pdd preserves its own marker.');
  const inventory = run.testInventory && label !== 'PR 1' ? [run.testInventory.text.trimEnd(), ...(run.testInventory.saved ? [] : ['warning: The full test inventory report was not saved.']), inventoryCommits(run.testInventory)] : [];
  const reviewAt = evidence.lines.findIndex(line => line.startsWith('Review:'));
  const slot = reviewAt < 0 ? evidence.lines.length : reviewAt;
  const preparedLines = [...evidence.lines.slice(0, slot), ...inventory, ...evidence.lines.slice(slot)].map(line => hideLocalPaths(redactTry(line), run));
  const body = (text, lifted) => hideLocalPaths([...lifted, ...prefix, ...top, ...(prefix.length || lifted.length || top.length ? [''] : []), ...head, ...(run.productMarker ? ['', run.productMarker] : []), ...(drafts.length ? ['', draftLine(drafts)] : []), '', `Made with \`pdd workflow run ${run.workflow}\`.`, '', '## Steps', ...lines,
    ...(!noted && hasReportLink([...lines, ...preparedLines, verify ?? ''].join('\n'), env) ? ['', 'Interpreter report links expire after 7 days.'] : []),
    ...(text !== null ? ['', '## Verify', '', text] : []), ''].join('\n'), run);
  const lifted = evidenceFit(preparedLines, Math.max(0, BODY_BUDGET - 200 - (verify === null ? 0 : 1000) - characters(body(null, []))), env);
  return verify === null ? body(null, lifted) : body(verifyFit(hideLocalPaths(verify, run), BODY_BUDGET - 200 - characters(body('', lifted)), env), lifted);
}

const commitSha = value => /^(?:[a-f\d]{40}|[a-f\d]{64})$/i.test(value);
function inventoryCommits(inventory) {
  return commitSha(inventory.baseSha) && commitSha(inventory.headSha)
    ? `Test inventory commits: ${inventory.baseSha.slice(0,7)} → ${inventory.headSha.slice(0,7)}.`
    : 'Test inventory commits: unavailable.';
}

// Commit leftovers, then push to the area's PR or open it. Returns a failure result, or null when the PR is there.
async function publishAreaPr(run, area, p, lines, retry) {
  const label = prLabel(run, area), existing = prOf(run, area.name), title = oneLine(run.issue.title).slice(0, 220) || `Issue #${run.number}`;
  const status = await git(p, run.root, 'status', '--porcelain=v1', '--untracked-files=all');
  if (status) {
    const files = status.split('\n').map(row => row.slice(3)).filter(Boolean);
    await git(p, run.root, 'add', '-A');
    await git(p, run.root, 'commit', '-q', '-m', `${oneLine(run.issue.title)} (#${run.number})`);
    lines.push(`warning: pdd committed ${files.length} uncommitted file(s): ${files.slice(0, 10).join(', ')}${files.length > 10 ? ', …' : ''}.`);
  }
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
  if (opted) {run.replayEvidence=await currentReplayEvidence(run,p);writeRun(run,p);}
  const bodyBase = run.prBase ?? run.baseBranch;
  const bodyDrafts = label === 'PR 1' ? await draftPrompts(run, p, run.branch, bodyBase) : [];
  const bodyTests = label === 'PR 1' ? (await worktreeContents(run, p)).tests.length > 0 : true;
  const markedReplayBody = (replay, pending = false) => {
    const evidence = pending && label !== 'PR 1' ? { ...prepared, lines: prepared.lines.map(line => line.startsWith('Old-code proof:') ? 'Old-code proof: publication-pending (source is being published).' : line) } : prepared;
    const body=prBody({...run,replayEvidence:replay},area,p.env,bodyDrafts,bodyTests,evidence);
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
    if (!inventoryOnly && (opted || label !== 'PR 1')) {
      let pending;
      try { pending=markedReplayBody({...run.replayEvidence,outcome:'blocked',reason:'Publication pending; source-bound replay status will be refreshed after the push.'},true); }
      catch (error) { return fail([...lines, `${oneLine(error.message)} No source was pushed. ${retry}.`].join('\n')); }
      const failed=await editReplay(pending);if(failed)return failed;
    }
    p.say(`Pushing ${run.branch} to ${label}…`);
    try {
      const reply = await p.execFile('git', ['push', 'origin', `${codePr && /^[a-f\d]{40,64}$/i.test(run.testInventory.headSha) ? run.testInventory.headSha : 'HEAD'}:refs/heads/${run.branch}`], { cwd: run.root });
      if (reply.code !== undefined && reply.code !== 0) throw Object.assign(Error(reply.stderr || 'git push failed'), {stderr:reply.stderr, code:reply.code});
    }
    catch (error) { return fail([...lines, `git push to ${run.branch} failed (${causeOf(error)}). Check the network and gh auth, then ${retry}.`].join('\n')); }
    prepared = await publicationEvidence(run, area, p);
    let finalBody;
    try { finalBody=markedReplayBody(run.replayEvidence); }
    catch (error) { return fail([...lines, `${oneLine(error.message)} Source was pushed; the PR stays publication-pending. ${retry}.`].join('\n')); }
    const failed=await editReplay(finalBody,true,inventoryOnly);
    if (failed) {
      if (!inventoryOnly) return failed;
      lines.push(`warning: The code PR still shows the previous inventory; its displayed commit pair identifies the older comparison. The new comparison is ${commitSha(run.testInventory.baseSha)&&commitSha(run.testInventory.headSha)?`${run.testInventory.baseSha.slice(0,7)} → ${run.testInventory.headSha.slice(0,7)}`:'unavailable'}. The current full report ${run.testInventory.saved ? 'was saved locally in test-inventory.json in the run folder' : 'was not saved locally'}. Inventory refresh failed (${failed.message}); ${retry}.`);
    } else rememberPublication(existing);
    if (area.then === 'ask-code') await refreshReplayBaseline(run,p);
    lines.push(`Pushed the new commits to ${label}.`);
    return null;
  }
  const base = bodyBase;
  // PR 1 says "tests" only when it has a test file (0.1.6 tester: a browser-only Story had none).
  const tests = bodyTests;
  let body;
  try { body = prBody(run, area, p.env, bodyDrafts, tests, prepared); }
  catch (error) { return fail([...lines, `${oneLine(error.message)} No source was pushed. ${retry}.`].join('\n')); }
  let intent;
  p.say(`Pushing ${run.branch} and opening ${label} on GitHub…`);
  try {
    intent = await prepareWorkflowPr({ cwd: run.root, runId: run.runId, stageId: area.name, repository: run.repo, baseBranch: base,
      title: label === 'PR 1' ? `${title} (${tests ? 'prompt, Story and tests' : 'prompt and Story'})` : label === 'PR 2' ? `${title} (code)` : title }, p.commandPorts);
  } catch (error) {
    const why = error.code === 'workflow_github_topic_has_no_commits' ? `There are no new commits on ${run.branch}. Commit the change, then ${retry}.`
      : `pdd could not prepare ${label} (${causeOf(error)}). Fix it, then ${retry}.`;
    return fail([...lines, why].join('\n'));
  }
  const outcome = await publishWorkflowPr({ cwd: run.root, intent, body: `${body}\n<!-- ${intent.marker} -->\n` }, p.commandPorts);
  // GitHub's refusal and a too-long body are certain: their message names the fix. Only a real doubt says "unconfirmed".
  if (!['open', 'merged'].includes(outcome.state) || !outcome.pr) return fail([...lines, `${label[0].toUpperCase()}${label.slice(1)} did not open: ${/ then try again\.$/.test(outcome.message)
    ? outcome.message.replace(/ then try again\.$/, ` then ${retry}.`) : `${outcome.message} ${retry[0].toUpperCase()}${retry.slice(1)} to retry.`}`].join('\n'));
  if (area.then === 'ask-code') await refreshReplayBaseline(run,p);
  const published = { stage: area.name, number: outcome.pr.number, url: outcome.pr.url, branch: run.branch, base };
  rememberPublication(published);
  run.pr.push(published);
  return null;
}

// The code-or-stop question after PR 1, as the chat must show it.
async function askCodeLines(run, area, p) {
  const summaries = area.steps.filter(item => run.done[item]).map(item => `  ${item}: ${oneLine(run.done[item].summary) || 'done'}`);
  const drafts = await pr1Drafts(run, p), url = prOf(run, area.name).url;
  // The code is built only from approved prompts, so the code PR is not offered while PR 1 has a draft prompt.
  if (drafts.length) return [`PR 1: ${url}`, ...summaries, draftLine(drafts),
    `Gate: show the person PR 1 and the Runtime check line. Do not offer the code PR yet. Tell the person exactly: "PR 1 is open: ${url}. ${approveFirst(run, drafts)}" Stop there.`];
  return [`PR 1: ${url}`, ...summaries,
    `Gate: show the person PR 1, the Runtime check line and the Try link, then ask exactly: "Do you want the code PR now, or stop here and merge PR 1 first? ${codeLater(run)}" Stop there.`,
    `If they want the code PR now (in their own words), run: ${p.pdd} workflow approve ${run.number}`,
    `If they stop, tell them exactly: "PR 1 is open: ${prOf(run, area.name).url}. ${codeLater(run)}" pdd never merges.`];
}

async function finishPr(run, area, step, p, lines) {
  const label = prLabel(run, area), existing = prOf(run, area.name);
  lines.push(`pdd recorded ${step}. pdd opens ${label} now.`);
  const failed = await publishAreaPr(run, area, p, lines, `run done ${step} again`);
  if (failed) return failed;
  if (area.then === 'ask-code') {
    // New commits on an open PR 1 keep the question's time, so a yes the person already gave still counts
    // (a change request with pdd workflow changes moves it).
    run.state = 'waiting'; run.gate = existing && run.gate?.kind === 'ask-code' ? run.gate : { area: area.name, at: p.now(), kind: 'ask-code' }; writeRun(run, p);
    return done([...lines, ...await askCodeLines(run, area, p)].join('\n'));
  }
  run.state = 'waiting'; run.gate = null; writeRun(run, p);
  return done([...lines, `${label === 'the PR' ? 'PR' : label}: ${prOf(run, area.name).url}`, `Tell the person ${label} is open. pdd never merges. Stop here.`].join('\n'));
}

// Record saved Runtime evidence without progressing the workflow or contacting external services.
export async function recordEvidence({ ref, summaryFile, cwd }, ports) {
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
    if (rows.some(row => row.summary_line !== expected.get(row.story))) throw Error('Evidence summary_line does not match its structured Story results.');
  } catch (error) { return fail(`Evidence not recorded: ${oneLine(error.message)}`); }
  (run.evidence ??= []).push({ at: p.now(), summary: [...new Set(lines)].join('\n'), source, receipt });
  writeRun(run, p);
  return done(`Recorded source-verified saved evidence for ${run.repo}#${run.number}. Steps, gates and PRs are unchanged. This records evidence, not fresh execution or approval.`);
}

export async function stepDone({ step, summary, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const run = await runForWorktree(cwd, p);
  if (!run) return fail('pdd workflow done works only in a run worktree. cd to the worktree that pdd made for this run.');
  if (run.state === 'cancelled') return done(`The run for #${run.number} was cancelled. Stop working on it.`);
  if (run.state === 'completed') return done(`The run for #${run.number} is complete. Stop.`);
  const area = run.areas[run.area], lines = [];
  if (!area.steps.includes(step)) lines.push(`warning: "${step}" is not a step of the ${area.name} area (${area.steps.join(', ')}). pdd recorded it anyway.`);
  else {
    const before = area.steps.slice(0, area.steps.indexOf(step)).filter(item => !run.done[item] && !area.optional.includes(item));
    if (before.length) lines.push(`warning: ${before.join(', ')} ${before.length > 1 ? 'are' : 'is'} not done yet. pdd recorded ${step} anyway.`);
  }
  run.question = null;
  // A step that runs again (for example build after failed vectors) makes the later steps of its area stale.
  const later = area.steps.includes(step) && run.done[step] ? area.steps.slice(area.steps.indexOf(step) + 1).filter(item => run.done[item]) : [];
  if (later.length) {
    for (const item of later) delete run.done[item];
    lines.push(`warning: ${step} ran again after ${later.join(', ')}. pdd cleared ${later.length > 1 ? 'those steps' : 'that step'}; run ${later.length > 1 ? 'them' : 'it'} again.`);
  }
  const record = { at: p.now(), summary: keepLines(summary), area: area.name };
  if (runtimeLines(record.summary).length) {
    record.source = { kind: 'git-content-v1', sha256: gitFingerprint(run.root) };
    (run.runtimeHistory ??= []).push({ ...record, step });
  }
  if (area.replay_evidence === REPLAY_POLICY) { run.replayEvidence=await currentReplayEvidence(run,p); record.replayEvidence=run.replayEvidence;lines.push(formatReplayEvidence(run.replayEvidence)); }
  run.done[step] = record;
  const next = area.steps.find(item => !run.done[item]);
  if (next) {
    run.state = 'running'; run.gate = null; writeRun(run, p);
    lines.push(`pdd recorded ${step}.`, area.optional.includes(next)
      ? `Next step: ${next} (optional). Ask the person if they want it. If they do not, run: ${p.pdd} workflow done ${next} --summary "skipped"`
      : `Next step: ${next}.`, `When it is done, run: ${p.pdd} workflow done ${next} --summary "one line"`);
    return done(lines.join('\n'));
  }
  // Try before PR 1 (#13): the person tries the result and approves before pdd opens the area's PR.
  if (area.gate === 'pr' && area.before === 'approve' && !prOf(run, area.name)) {
    const contents = await worktreeContents(run, p);
    run.gate = { area: area.name, at: p.now(), kind: 'approve-pr' }; run.state = 'waiting'; writeRun(run, p);
    lines.push(`pdd recorded ${step}. The ${area.name} area is done; pdd opens ${prLabel(run, area)} after the person approves.`,
      nothingToTry(run, area, contents)
        ? 'Gate: show the person the Runtime check line of each Story (one per Story: ✓, ✗ or no verdict) with the report link, if there is one. There is nothing to try. Ask them to approve or ask for changes. Stop. Do not approve for them.'
        : 'Gate: show the person the Runtime check line of each Story (one per Story: ✓, ✗ or no verdict) with the report link and simulation details (the Try link when it opens a page). Ask them to try it, then approve or ask for changes. Stop. Do not approve for them. Run pdd simulate <story>: it automatically opens a shell for a command-line program, localhost with an example request for HTTP routes, the Simulator page for screens, or its Form tab for typed operations. Run pdd simulate for the whole project; use --page to choose the page.',
      ...(prLabel(run, area) === 'PR 1' ? [`Tell the person what PR 1 holds, in these words: "${holdsLine(contents)}"`] : []),
      `When the person approves in their own words, run: ${p.pdd} workflow approve ${run.number}`,
      'If they ask for changes, revise in this chat, run done again for the step you changed, and ask again.');
    return done(lines.join('\n'));
  }
  if (area.gate === 'pr') return finishPr(run, area, step, p, lines);
  run.gate = { area: area.name, at: p.now(), kind: 'approve' }; run.state = 'waiting'; writeRun(run, p);
  lines.push(`pdd recorded ${step}. The ${area.name} area is done.`,
    'Gate: show the person the result, ask them to approve it or ask for changes, and stop. Do not approve for them. You may offer pdd simulate <story> before the check: it automatically opens a shell for a command-line program, localhost with an example request for HTTP routes, the Simulator page for screens, or its Form tab for typed operations. Run pdd simulate for the whole project; use --page to choose the page.',
    `When the person approves in their own words, run: ${p.pdd} workflow approve ${run.number}`,
    'If they ask for changes, revise in this chat, run done again for the step you changed, and ask again.');
  return done(lines.join('\n'));
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
  const go = `cd ${shell(run.root)} && `, again = `Then run pdd workflow approve ${run.number} again.`, what = approved.length ? `your approval of ${listed(approved)}` : null;
  if (approved.length) {
    try { await git(p, run.root, 'commit', '-q', '-m', `Approve ${approved.join(', ')}`, '--', ...approved); }
    catch { return { failed: `pdd could not commit ${what}. Run: ${go}git commit -m ${shell(`Approve ${approved.join(', ')}`)} -- ${approved.map(shell).join(' ')}\n${again}` }; }
  }
  try { await p.execFile('git', ['fetch', 'origin', run.branch], { cwd: run.root }); } catch { /* The last fetched PR 1 head decides. */ }
  const remote = `refs/remotes/origin/${run.branch}`;
  let ahead = 0, behind = false;
  try { ahead = Number(await git(p, run.root, 'rev-list', '--count', `${remote}..HEAD`)) || 0; behind = Number(await git(p, run.root, 'rev-list', '--count', `HEAD..${remote}`)) > 0; } catch {
    if (replayEnabled(run)) return {failed:`Cannot verify the published prompt-space head. Fetch the prompt branch and run pdd workflow approve ${run.number} again.`};
    ahead = 0;
  }
  if (behind && replayEnabled(run)) return {failed:`The prompt branch is behind its published head. Update the worktree from origin/${run.branch}, then run pdd workflow approve ${run.number} again.`};
  if (!ahead && !behind) await refreshReplayBaseline(run,p);
  if (ahead && behind && what) return { failed: `PR 1 has commits that this worktree does not have, so pdd did not push ${what}. Run: ${go}git pull --rebase origin ${shell(run.branch)} && git push origin HEAD:refs/heads/${run.branch}\n${again}` };
  if (!ahead || behind) {
    const drafts = approved.length ? await pr1Drafts(run, p) : before;
    return { drafts, lines: await draftDescription(run, pr1, drafts, p) };
  }
  try { await rawGit(p,run.root,'push','origin',`HEAD:refs/heads/${run.branch}`); }
  catch { return { failed: `pdd could not push ${what ?? `the worktree's new commit${ahead > 1 ? 's' : ''}`} to PR 1. Run: ${go}git push origin HEAD:refs/heads/${run.branch}\n${again}` }; }
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
    const rows = String(draftBody).replace(marker, '').split('\n');
    const owned = /^(?:Not fixed yet:|Not checked:|Defect:|Not caught because:|Proof \(defect fixed\):|Proof \(gap closed\):|Old-code proof:|Tests vs base:|Review:|Evidence omitted:)/;
    const reference = new RegExp(`^(?:Part of|Closes|Refs) #${run.number}$`);
    let at = 0;
    while (at < rows.length && !rows[at].trim()) at++;
    while (at < rows.length && owned.test(rows[at])) at++;
    while (at < rows.length && !rows[at].trim()) at++;
    if (reference.test(rows[at] ?? '')) at++;
    while (at < rows.length && !rows[at].trim()) at++;
    const remainder = rows.slice(at).join('\n');
    const safeRemainder = hideLocalPaths(redactTry(remainder), run);
    const footer = `\n\n${marker}\n`;
    const room = BODY_BUDGET - characters(footer) - characters(evidence.issueReference) - 4;
    const lifted = evidenceFit(evidence.lines.map(line => hideLocalPaths(redactTry(line), run)), Math.max(0, room - Math.min(1000, characters(safeRemainder))), p.env);
    const leading = [...lifted, ...(lifted.length ? [''] : []), evidence.issueReference, '', ''].join('\n');
    const fitted = verifyFit(safeRemainder, BODY_BUDGET - characters(leading) - characters(footer), p.env, true);
    const nextBody = `${leading}${fitted}${footer}`;
    if (nextBody === body) return [];
    const reply = await p.execFile('gh', ['pr', 'edit', pr1.url, '--body-file', '-'], { cwd: run.root, input: nextBody });
    if (reply.code !== undefined && reply.code !== 0) throw Object.assign(Error('PR 1 description update failed.'), { code: reply.code });
    return [`pdd updated the PR 1 description: ${drafts.length ? `draft prompts left: ${drafts.join(', ')}` : 'no draft prompts are left'}.`];
  } catch (error) { return [`warning: pdd could not update the PR 1 description (${error.code ?? 'error'}). Its "Draft prompts" line is out of date.`]; }
}

// A terminal in the run's own chat pane (Herdr session pdd) belongs to the chat; a person's other Herdr tab does not.
const chatPane = (run, env) => env.HERDR_PANE_ID && /[\\/]sessions[\\/]([^\\/]+)[\\/][^\\/]+$/.exec(String(env.HERDR_SOCKET_PATH ?? ''))?.[1] === PDD_HERDR_SESSION
  ? (run.chats ?? []).find(chat => chat.paneId === env.HERDR_PANE_ID) ?? null : null;
// The evidence result in plain words (approval-evidence names "native sessions").
const noReply = (evidence, who) => evidence?.code === 'user_message_missing' ? `there is no reply from ${who} after the gate question` : 'pdd could not read this chat';

// Claude Code's ! prefix runs a person's command with CLAUDECODE=1 (0.1.6 tester), so pdd names what it sees.
const agentMarker = env => env.CLAUDECODE ? `CLAUDECODE=${env.CLAUDECODE}` : env.CODEX_THREAD_ID ? 'CODEX_THREAD_ID is set' : 'stdin is not a terminal';

async function startNextChat(run, p, packageRoot) {
  const area = run.areas[run.area];
  p.say(`Starting the ${area.name} chat in Herdr…`);
  try {
    run.chats.push(await startChat({ run, area: area.name, message: await areaMessage(run, run.area, p, packageRoot) }, p));
    clearChatFailure(run);
    writeRun(run, p);
    return run.chats.at(-1);
  } catch (error) {
    if (error.chat?.area === area.name) run.chats.push(error.chat);
    recordChatFailure(run, error, 'start', p);
    throw error;
  }
}

export async function approveRun({ ref, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run, area = run.areas[run.area], label = `${run.repo}#${run.number} "${oneLine(run.issue.title)}"`;
  const askCode = area.then === 'ask-code', beforePr = run.gate?.kind === 'approve-pr';
  if (ended(run) && !(askCode && run.gate?.kind === 'ask-code')) return fail(`The run for ${run.repo}#${run.number} is ${run.state}. There is nothing to approve.`);
  if (area.gate === 'pr' && !askCode && !beforePr) return fail(`Nothing to approve for #${run.number}: the ${area.name} area ends with ${prLabel(run, area)}, which pdd opens after its last step.${prOf(run, area.name) ? ` ${prLabel(run, area) === 'the PR' ? 'PR' : prLabel(run, area)}: ${prOf(run, area.name).url}` : ''}`);
  const missing = missingHome(run, p.env);
  if (missing) return fail(missing);
  const agent = isAgentSession(p.env), pane = chatPane(run, p.env), viaChat = agent || !p.isTTY || Boolean(pane);
  let carried = [];
  if (askCode && run.gate?.kind === 'ask-code') {
    if (replayEnabled(run)) {
      try {
        const dirty = await unpublishedScenarios(run,p);
        if (dirty.length) return fail(`Unpublished scenario edits remain: ${dirty.join(', ')}. Publish them in prompt space, then run pdd workflow approve ${run.number} again.`);
      } catch { return fail(`Cannot verify published scenario bytes. Repair the scenario inventory, then run pdd workflow approve ${run.number} again.`); }
    }
    // The code is built only from approved prompts; pdd never approves them itself.
    p.say('Reading PR 1 on GitHub…');
    const carry = await syncPr1(run, p);
    if (carry.failed) return fail(carry.failed);
    if (carry.drafts.length) return fail(approveFirst(run, carry.drafts));
    carried = carry.lines;
  }
  if (!run.gate) {
    const why = `The ${area.name} area of #${run.number} is not at its gate yet (not done: ${area.steps.filter(step => !run.done[step]).join(', ')}).`;
    if (viaChat) return fail(`${why} Finish the steps and run done first.`);
    if (!await confirm(p, `${why} Approve anyway? (y/N) `)) return fail('Not approved. The run is unchanged.');
  }
  let record;
  if (viaChat) {
    const chat = currentChat(run);
    if (!chat) return fail(`The ${area.name} area has no chat to read. The person approves in a terminal: pdd workflow approve ${run.number}`);
    if (!chat.session?.id) { const live = await chatSession(chat, p); if (live.sessionId) chat.session = { agent: run.agent, id: live.sessionId }; }
    const read = p.readApprovalEvidence ?? (await import('./approval-evidence.mjs')).readApprovalEvidence;
    const configDir = expandHome(chat.configDir, p.env);
    const evidence = await read({ stage: { agent: run.agent, root: run.root, startedAt: chat.startedAt, endedAt: p.now(), ...(chat.session?.id ? { sessionId: chat.session.id } : {}) },
      gateAskedAt: run.gate.at, decision: 'approve', ignorePrefixes: [CHANGE_PREFIX, ANSWER_PREFIX] },
    { env: p.env, now: p.now, ...(configDir ? (run.agent === 'claude' ? { claudeConfigDir: configDir } : { codexHome: configDir }) : {}) });
    // The chat's own agent gets plain words to tell the person (0.1.6 tester: the chat said "PDD rejected recording your
    // earlier "Go on""); a person in an agent-like terminal or in the chat's pane learns how to approve.
    if (evidence?.ok !== true && p.env.PDD_AGENT_SESSION) return fail([`Only the person can approve, with a reply after your gate question. pdd found none: ${noReply(evidence, 'the person')}.`,
      `Do not explain this check to the person. Tell them plainly: "I still need your approval for this step. Reply "I approve" here, or run pdd workflow approve ${run.number} in your terminal." Then stop and wait.`].join('\n'));
    if (evidence?.ok !== true) return fail([`pdd sees ${pane ? `the ${area.name} chat's own Herdr pane (${pane.paneId})` : `an agent environment (${agentMarker(p.env)})`}, so it cannot ask you y/N here.`,
      `No approval was found in the ${area.name} chat: ${noReply(evidence, 'you')}.`,
      `To approve, run pdd workflow approve ${run.number} in ${pane ? 'another terminal tab' : 'a normal terminal'}. Or answer the gate question in the ${area.name} chat: pdd workflow open ${run.number}`].join('\n'));
    if (askCode && !beforePr && !YES_WORDS.test(evidence.userMessage ?? '')) return fail(`Not sure you approved. Run \`pdd workflow approve ${run.number}\` in your terminal.`);
    record = { via: 'chat', text: evidence.userMessage, sessionId: evidence.sessionId, at: evidence.userMessageAt };
    if (!chat.session?.id && evidence.sessionId) chat.session = { agent: run.agent, id: evidence.sessionId };
  } else {
    if (!await confirm(p, beforePr ? `Approve the ${area.name} area and open ${prLabel(run, area) === 'the PR' ? 'the PR' : prLabel(run, area)} for ${label}? (y/N) `
      : askCode ? `Make the code PR now for ${label}? PR 1: ${prOf(run, area.name)?.url} (y/N) ` : `Approve the ${area.name} area for ${label}? (y/N) `)) return fail([...carried, 'Not approved. The run is unchanged.'].join('\n'));
    record = { via: 'terminal' };
  }
  const said = record.text !== undefined ? ` The person wrote: "${oneLine(record.text).slice(0, 300)}".` : '';
  if (beforePr) {
    // Try before PR 1 (#13): the approval opens the area's PR; the code question comes after it.
    const lines = [], failed = await publishAreaPr(run, area, p, lines, `run pdd workflow approve ${run.number} again`);
    if (failed) return failed;
    const at = p.now(), url = prOf(run, area.name).url;
    run.decisions.push({ stage: area.name, decision: 'approve', via: record.via, at, ...(record.text !== undefined ? { text: record.text } : {}) });
    run.approvalRecord = { kind: record.via, area: area.name, at, ...(record.text !== undefined ? { userMessage: record.text, userMessageAt: record.at, sessionId: record.sessionId } : {}) };
    run.state = 'waiting'; run.gate = askCode ? { area: area.name, at, kind: 'ask-code' } : null; run.question = null; writeRun(run, p);
    const head = [`Approved the ${area.name} area of ${label}.${said} pdd opened ${prLabel(run, area) === 'the PR' ? 'the PR' : prLabel(run, area)}.`, ...lines];
    if (!askCode) return done([...head, `PR: ${url}`, 'pdd never merges.'].join('\n'));
    if (viaChat) return done([...head, ...await askCodeLines(run, area, p)].join('\n'));
    // A draft prompt in PR 1: pdd does not offer the code PR, and says how to approve the prompt first.
    const drafts = await pr1Drafts(run, p);
    if (drafts.length) {
      await sendToChat(currentChat(run), `pdd opened PR 1: ${url}. The person approved it in their terminal. PR 1 has draft prompts, so the code PR waits. Tell them exactly: "PR 1 is open: ${url}. ${approveFirst(run, drafts)}" Then stop.`, p);
      return done([...head, `PR 1: ${url}`, approveFirst(run, drafts)].join('\n'));
    }
    if (!await confirm(p, `Make the code PR now for ${label}? PR 1: ${url} (y/N) `)) {
      await sendToChat(currentChat(run), `pdd opened PR 1: ${url}. The person approved it in their terminal and stops here for now. Tell them exactly: "PR 1 is open: ${url}. ${codeLater(run)}" Then stop.`, p);
      return done([...head, `PR 1: ${url}`, `Stopped at PR 1. ${codeLater(run)}`].join('\n'));
    }
  }
  let based = '';
  if (askCode) {
    // Reached at the code gate, or right after PR 1 opened when the terminal said yes to the code PR.
    p.say('Making the code branch…');
    try { based = await codeBranch(run, area, p); }
    catch (error) { return fail(`${oneLine(error.message)} Nothing changed. Check PR 1, then run pdd workflow approve ${run.number} again.`); }
  }
  const now = p.now();
  run.decisions.push({ stage: area.name, decision: 'approve', via: record.via, at: now, ...(record.text !== undefined ? { text: record.text } : {}) });
  run.approvalRecord = { kind: record.via, area: area.name, at: now, ...(record.text !== undefined ? { userMessage: record.text, userMessageAt: record.at, sessionId: record.sessionId } : {}) };
  run.gate = null; run.question = null; run.area++; run.state = 'running'; run.doneAt = null; writeRun(run, p);
  const next = run.areas[run.area];
  let chat;
  try { chat = await startNextChat(run, p, packageRoot); }
  catch (error) { return fail(`${carried.map(line => `${line}\n`).join('')}Approved the ${area.name} area of ${label}.${said} The ${next.name} chat startup was not confirmed (${error.code ?? 'error'}). Start it: pdd workflow open ${run.number}`); }
  return done([...carried, `Approved the ${area.name} area of ${label}.${said}${based}`,
    `Started area ${run.area + 1} of ${run.areas.length}: ${next.name} (${next.steps.join(', ')}) in a new chat: Herdr session pdd, tab "${chat.label}".`,
    `Watch it: pdd workflow open ${run.number}`, ...(agent ? ['This chat\'s work is done. Stop here.'] : [])].join('\n'));
}

// The agent asks the person in the middle of a step: status shows the question until the next done or the answer.
export async function askPerson({ text, cwd }, ports) {
  const p = deps(ports);
  const run = await runForWorktree(cwd, p);
  if (!run) return fail('pdd workflow ask works only in a run worktree. cd to the worktree that pdd made for this run.');
  if (ended(run)) return done(`The run for #${run.number} is ${run.state}. Stop working on it.`);
  const question = String(text ?? '').trim().slice(0, 500);
  if (!question) return fail('Write the question after pdd workflow ask.');
  run.question = { text: question, at: p.now(), area: run.areas[run.area].name }; if (!run.gate) run.state = 'waiting';
  writeRun(run, p);
  return done([`pdd shows the person: waiting for you: ${question.split('\n')[0]}`,
    'Now ask the question in a plain chat message (not a question dialog) and end your turn.',
    `The person answers in this chat, or from their shell with: pdd workflow changes ${run.number} "answer". Then go on with the step and run done as usual.`].join('\n'));
}

export async function changeRun({ ref, text, cwd }, ports) {
  const p = deps(ports);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run, area = run.areas[run.area], chat = currentChat(run);
  if (ended(run)) return fail(`The run for ${run.repo}#${run.number} is ${run.state}.`);
  // After pdd workflow ask the text is the person's answer; otherwise it is a change request.
  const request = oneLine(text), answer = Boolean(openQuestion(run));
  if (request && !answer && run.gate && looksLikeApproval(request)) return { exitCode: 2, message: `This looks like an approval. To approve, run: pdd workflow approve ${run.number}\nNothing was sent to the chat.` };
  if (!chat) return fail(`The ${area.name} area has no chat. Start it: pdd workflow open ${run.number}`);
  if (!request) return fail('Write the change request after the issue number.');
  const sent = await sendToChat(chat, answer ? `${ANSWER_PREFIX}: ${request} Go on with the step.`
    : `${CHANGE_PREFIX}: ${request} Revise in this chat, run done again for the step you changed, then show the result and ask again.`, p);
  if (!sent.ok) return fail(sent.code === 'agent_not_found' ? `The ${area.name} chat is not running. Open it with "pdd workflow open ${run.number}", then type the text there.`
    : sent.code === 'agent_blocked' ? `The ${area.name} chat shows a question dialog, and pdd cannot type into it. Answer it in the chat: pdd workflow open ${run.number}`
    : `pdd could not send the text to the ${area.name} chat (${sent.code}). Open it: pdd workflow open ${run.number}`);
  const now = p.now();
  run.changes.push({ stage: area.name, round: run.changes.filter(change => change.stage === area.name).length + 1, text: request, at: now, ...(answer ? { answer: true } : {}) });
  if (answer) { run.question = null; if (!run.gate) run.state = 'running'; }
  else if (run.gate) { run.gate.at = now; run.question = null; }
  writeRun(run, p);
  return done(answer ? `Sent your answer to the ${area.name} chat of #${run.number}. The agent goes on with the step.`
    : `Sent your change request to the ${area.name} chat of #${run.number}.${run.gate ? ` The gate stays open. Approve when you are happy: pdd workflow approve ${run.number}` : ''}`);
}

export async function cancelRun({ ref, cwd }, ports) {
  const p = deps(ports);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  if (run.state === 'cancelled') return done(`The run for ${run.repo}#${run.number} is already cancelled.`);
  p.say('Closing the chat tabs in Herdr…');
  const { warnings } = await closeChats(run, p);
  run.state = 'cancelled'; run.cancelled = { state: 'cancelled', at: p.now() }; run.gate = null; writeRun(run, p);
  return done([...warnings, `Cancelled the run for ${run.repo}#${run.number} and closed its Herdr tabs.`,
    `The worktree stays at ${run.root} (branch ${run.branch}).`].join('\n'));
}

async function refreshPr(run, p) {
  if (!run.pr?.length || run.state === 'cancelled') return;
  const cwd = existsSync(run.root) ? run.root : run.sourceRoot, before = JSON.stringify([run.state, run.pr]);
  for (const pr of run.pr) Object.assign(pr, await (p.readPrStatus ?? readWorkflowPrStatus)({ cwd, url: pr.url }, p.commandPorts));
  const last = run.pr.at(-1), area = run.areas.find(item => item.name === last.stage);
  run.prState = { state: last.state, ci: last.ci, checkedAt: p.now() };
  if (last.state === 'merged' && area === run.areas.at(-1)) run.state = 'completed';
  if (last.state === 'merged' && area?.then === 'ask-code' && run.gate?.kind === 'ask-code') { run.state = 'completed'; run.doneAt = 'PR 1'; }
  // Only a real change is written, so the run's last-change time stays true.
  if (JSON.stringify([run.state, run.pr]) !== before) writeRun(run, p);
}

// What Herdr shows for the current chat of a running run or a run at a gate, with one Herdr call: 'blocked' (a question
// dialog), 'working', 'stopped' (no agent runs in its pane: it ended or never started), or null (idle, or pdd cannot tell,
// and status keeps its words). Herdr sees a new agent only after it starts, so a chat counts as stopped only after a while.
const STOPPED = new Set(['agent_not_found', 'server_not_running']);
const START_GRACE_MS = 30_000;
async function chatState(run, p) {
  if (ended(run)) return null;
  const area = run.areas[run.area], failure = activeChatFailure(run), chat = currentChat(run);
  if (!chat) return failure || !run.gate && !prOf(run, area?.name) ? 'unconfirmed' : null;
  if (!(run.state === 'running' || run.gate || failure)) return null;
  const live = await chatSession(chat, p);
  if (live.alive) {
    if (failure || chat.startUnconfirmed) { clearChatFailure(run); delete chat.startUnconfirmed; writeRun(run, p); }
    return ['blocked', 'working'].includes(live.status) ? live.status : null;
  }
  if (failure) return 'unconfirmed';
  if (live.code === 'server_unavailable') return 'unavailable';
  return STOPPED.has(live.code) && p.now() - Math.max(chat.startedAt ?? 0, chat.resumedAt ?? 0) >= START_GRACE_MS ? 'stopped' : null;
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
  const next = activeChatFailure(run) || ['unconfirmed', 'unavailable'].includes(chat) ? `pdd workflow open ${run.number}`
    : run.gate?.kind === 'ask-code' && drafts.length ? `cd ${shell(run.root)} && ${drafts.map(path => `pdd approve ${shell(path)}`).join(' && ')}, then pdd workflow approve ${run.number} (make the code PR)`
    : run.gate?.kind === 'ask-code' ? `pdd workflow approve ${run.number}  (make the code PR)   or stop here and merge PR 1`
    : run.gate ? `pdd workflow approve ${run.number}   or   pdd workflow changes ${run.number} "what to change"`
    : ended(run) ? null : prOf(run, area?.name) ? `Review and merge ${run.pr.length > 1 && run.prBase && run.prBase !== run.baseBranch ? 'PR 1, then PR 2,' : 'the PR'} on GitHub. pdd never merges.` : `pdd workflow open ${run.number}`;
  return [`${run.repo}#${run.number} "${oneLine(run.issue.title)}" · ${run.workflow} · ${run.agent}`,
    `State: ${describe(run, chat, facts)}`,
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
  const problem = activeChatFailure(run) || ['unconfirmed', 'unavailable'].includes(chat);
  const question = openQuestion(run), writing = !problem && Boolean(run.gate) && !question && chat === 'working';
  const group = run.state === 'cancelled' ? 'cancelled' : run.state === 'completed' ? 'done' : problem ? 'waiting' : writing ? 'working'
    : run.gate || question || running && ['blocked', 'stopped'].includes(chat) ? 'waiting' : prOf(run, area?.name) ? 'pr-open' : 'working';
  const step = area?.steps.find(item => !run.done[item]);
  const words = group === 'cancelled' ? 'cancelled'
    : group === 'done' ? (run.gate?.kind === 'ask-code' ? 'done at PR 1' : 'done')
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

async function listStatus(runs, { json, cancelled, scope }, p) {
  const reading = runs.filter(run => run.state === 'waiting' && run.pr?.length).reduce((sum, run) => sum + run.pr.length, 0);
  if (reading) p.say(`Reading ${reading} PR${reading === 1 ? '' : 's'} from GitHub…`);
  for (const run of runs) if (run.state === 'waiting' && run.pr?.length) { try { await refreshPr(run, p); } catch { /* A PR read failure keeps the saved state. */ } }
  const all = [];
  for (const run of runs) all.push(summary(run, p.timeZone, await chatState(run, p), ended(run) ? {} : await gateFacts(run, p)));
  const hidden = cancelled ? 0 : all.filter(item => item.group === 'cancelled').length;
  const shown = all.filter(item => cancelled || item.group !== 'cancelled')
    .sort((a, b) => GROUPS.indexOf(a.group) - GROUPS.indexOf(b.group) || (b.updatedAt ?? 0) - (a.updatedAt ?? 0));
  if (json) return done(JSON.stringify({ runs: shown.map(({ line, ...item }) => item) }, null, 2));
  if (!shown.length) return done([`No pdd runs ${scope}.${hidden ? ` ${hidden} cancelled run${hidden > 1 ? 's' : ''} hidden; add --cancelled to see ${hidden > 1 ? 'them' : 'it'}.` : ''}`, 'Start one with: pdd workflow run NAME ISSUE'].join('\n'));
  return done([...shown.map(item => item.line),
    ...(hidden ? [`${hidden} cancelled run${hidden > 1 ? 's' : ''} hidden; add --cancelled to see ${hidden > 1 ? 'them' : 'it'}.`] : []),
    `Review without resuming: pdd workflow view ${shown[0].ref}`, `Open one: pdd workflow open ${shown[0].ref}`].join('\n'));
}

export async function runStatus({ ref, cwd, all = false, json = false, cancelled = false }, ports) {
  const p = deps(ports);
  if (ref === undefined && (all || !(await gitContext(cwd, p)))) return listStatus(allRuns({ cancelled }, p), { json, cancelled, scope: 'on this machine' }, p);
  if (ref === undefined && !(await runForWorktree(cwd, p))) return listStatus(await listRuns({ cwd, cancelled }, p), { json, cancelled, scope: 'in this repository' }, p);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  if (found.run.pr?.length && found.run.state !== 'cancelled') p.say(`Reading ${found.run.pr.length === 1 ? 'the PR' : `${found.run.pr.length} PRs`} from GitHub…`);
  await refreshPr(found.run, p);
  const run = found.run, facts = ended(run) ? {} : await gateFacts(run, p), chat = await chatState(run, p);
  if (json) { const { line, ...item } = summary(run, p.timeZone, chat, facts); return done(JSON.stringify({ runs: [item] }, null, 2)); }
  return done(detail(run, chat, facts));
}

export async function openRun({ ref, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  if (ended(run)) return fail(`The run for ${run.repo}#${run.number} is ${run.state}. Its worktree is ${run.root}.`);
  const missing = missingHome(run, p.env);
  if (missing) return fail(missing);
  let chat = currentChat(run), started = false;
  try {
    if (!chat) { chat = await startNextChat(run, p, packageRoot); started = true; }
    p.say(`Opening the ${chat.area} chat in Herdr…`);
    const opened = await openChat({ run, chat }, p);
    if (opened.restartAvailable) {
      run.abandonedChats = [...(run.abandonedChats ?? []), { ...chat, abandonedAt: p.now(), reason: 'tab-and-agent-missing' }];
      run.chats = run.chats.filter(item => item !== chat);
      const message = `The saved tab and agent are gone. The stale start was cleared; the run and worktree are kept. Run pdd workflow open ${run.number} to start the ${chat.area} chat again.`;
      recordChatFailure(run, { code: 'chat_start_reset', message }, 'open', p);
      return fail(message);
    }
    clearChatFailure(run);
    writeRun(run, p);
    const where = `Herdr session pdd, tab "${chat.label}"`;
    return done([started ? `Started the ${chat.area} chat in ${where}.` : opened.resumed ? `Resumed the ${chat.area} chat in ${where}.` : `The ${chat.area} chat is in ${where}.`,
      ...(opened.attached ? [] : [p.env.HERDR_ENV === '1' ? 'pdd focused that tab. If you are in another Herdr session, run: herdr session attach pdd' : 'See it with: herdr session attach pdd'])].join('\n'));
  } catch (error) {
    recordChatFailure(run, error, chat ? 'open' : 'start', p);
    return fail(`pdd could not open the ${run.areas[run.area].name} chat (${error.code ?? 'error'}: ${oneLine(error.message)}).`);
  }
}
