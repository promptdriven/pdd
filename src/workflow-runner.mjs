// Generated from prompts/cli/workflow-runner.prompt.md (sha256: 612d1f4c923e7896029ca17bab2e78573113ade1ed24e360dfda4793b7a853b8).
import { execFile as execFileCallback } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, renameSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';
import { createInterface } from 'node:readline/promises';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { readWorkflowAreas } from './workflow-areas.mjs';
import { resolveWorkflowIssue, prepareWorkflowPr, publishWorkflowPr, readWorkflowPrStatus } from './workflow-github.mjs';
import { allocateIssueWorktree, releaseIssueClaim } from './workflow-worktree.mjs';
import { allRuns, currentChat, gitContext, listRuns, readRun, resolveRun, runDirFor, runForWorktree, writeRun } from './workflow-runs.mjs';
import { startChat, sendToChat, chatSession, openChat, closeChats } from './workflow-chat.mjs';
import { interfaceBlocks } from './runtime-preflight.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const CHANGE_PREFIX = 'The person asks for changes';
const ANSWER_PREFIX = 'The person answers your question';
// At the code gate a chat reply must say yes in plain words; at other gates any reply from the person counts.
const YES_WORDS = /\b(?:yes|approved?|build the code|go ahead|code pr now|continue)\b/i;
// Try links (/s/<token>/) open a live session; they never go into a PR body. Report links (/r/) stay.
const redactTry = text => String(text).replace(/https?:\/\/[^\s)<>\]"'`]*?\/s\/[^/\s)<>\]"'`]+(?:\/[^\s)<>\]"'`]*)?/g, '(Try link removed)');
const ordinary = promisify(execFileCallback);
const shell = value => /^[A-Za-z0-9_@%+=:,./-]+$/.test(value) ? value : `'${value.replace(/'/g, `'\\''`)}'`;
const oneLine = value => String(value ?? '').replace(/\s+/g, ' ').trim();
// A step summary keeps its line breaks (0.1.6: the chat pastes one Runtime check line per line); blank lines go.
const keepLines = value => String(value ?? '').split('\n').map(oneLine).filter(Boolean).join('\n');
const done = message => ({ exitCode: 0, message });
const fail = message => ({ exitCode: 1, message });
const ended = run => ['cancelled', 'completed'].includes(run.state);
const isAgentSession = env => Boolean(env.PDD_AGENT_SESSION || env.CLAUDECODE || env.CODEX_THREAD_ID);

function deps(ports = {}) {
  const env = ports.env ?? process.env;
  const execFile = ports.execFile ?? ((file, args, { cwd }) => ordinary(file, args, { cwd, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 }));
  return { ...ports, env, execFile, commandPorts: ports.execFile ? { execFile: ports.execFile } : {}, now: ports.now ?? Date.now,
    isTTY: ports.isTTY ?? Boolean(process.stdin.isTTY && process.stderr.isTTY) };
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

function claudeTrusts(folder, env) {
  try {
    const file = env.CLAUDE_CONFIG_DIR ? join(env.CLAUDE_CONFIG_DIR, '.claude.json') : join(env.HOME || homedir(), '.claude.json');
    return JSON.parse(readFileSync(file, 'utf8')).projects?.[folder]?.hasTrustDialogAccepted === true;
  } catch { return false; }
}

async function changedFiles(run, p) {
  try {
    const tracked = (await git(p, run.root, 'diff', '--name-only', run.baseSha)).split('\n');
    const untracked = (await git(p, run.root, 'ls-files', '--others', '--exclude-standard')).split('\n');
    return [...new Set([...tracked, ...untracked].filter(Boolean))];
  } catch { return []; }
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

// The *.prompt.md files that a branch changes against its base and whose Runtime interface is still "draft".
async function draftPrompts(run, p, branch, base) {
  try {
    const files = (await git(p, run.root, 'diff', '--name-only', `refs/remotes/origin/${base}...${branch}`)).split('\n').filter(path => path.endsWith('.prompt.md'));
    const drafts = [];
    for (const path of files) {
      let text;
      try { text = String((await p.execFile('git', ['show', `${branch}:${path}`], { cwd: run.root })).stdout ?? ''); } catch { continue; }
      if (interfaceBlocks(text).some(block => { try { return JSON.parse(block[1])?.status === 'draft'; } catch { return false; } })) drafts.push(path);
    }
    return drafts;
  } catch { return []; }
}
const draftLine = drafts => `Draft prompts: ${drafts.join(', ')}. Approve them before you merge.`;
async function pr1Drafts(run, p) {
  const ask = askArea(run), pr1 = ask && prOf(run, ask.name);
  return pr1 ? draftPrompts(run, p, pr1.branch, pr1.base) : [];
}

// blocked: Herdr shows the chat waiting in a question dialog (read by the caller; describe itself makes no calls).
function describe(run, blocked = false) {
  const area = run.areas[run.area], pr1 = askArea(run) && prOf(run, askArea(run).name);
  if (run.state === 'cancelled') return 'cancelled';
  if (run.question && run.state !== 'completed') return `waiting for you: ${run.question.text.split('\n')[0]}`;
  if (blocked && run.state === 'running') return `waiting for you: the chat asks a question in its window (pdd workflow open ${run.number})`;
  if (run.state === 'completed' && run.gate?.kind === 'ask-code') return `done at PR 1 (merged: ${pr1?.url}). ${codeLater(run)}`;
  if (run.state === 'completed') return 'complete: the PR is merged';
  if (run.gate?.kind === 'approve-pr') return `waiting for you: try it, then approve to open ${prLabel(run, area) === 'the PR' ? 'the PR' : prLabel(run, area)} (or ask for changes)`;
  if (run.gate?.kind === 'ask-code') return `PR 1 open (${pr1?.url}); waiting for you: code PR now, or stop and merge PR 1. ${codeLater(run)}`;
  if (run.gate) return `waiting for you: approve the ${run.gate.area} area or ask for changes`;
  if (prOf(run, area?.name) && area.gate === 'pr') return `waiting for you: review and merge ${prLabel(run, area)} on GitHub`;
  const step = area?.steps.find(item => !run.done[item]);
  return step ? `the agent works on ${step}` : 'the agent works';
}

export async function startRun({ name, issue, agent = 'codex', cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  let workflow;
  try { workflow = readWorkflowAreas({ packageRoot, name, cwd, home: p.env.HOME || homedir() }); } catch (error) { return fail(error.message); }
  if (!['codex', 'claude'].includes(agent)) return fail('Choose --agent codex or --agent claude.');
  const context = await gitContext(cwd, p);
  if (!context) return fail('Run this inside a Git checkout of the repository that has the issue.');
  let binding;
  try { binding = await resolveWorkflowIssue({ cwd: context.toplevel, issue }, p.commandPorts); }
  catch (error) { return fail(`pdd could not read issue ${issue} with gh (${error.code ?? 'error'}). Check "gh auth status", the origin remote and the issue number.`); }
  const number = binding.issue.number, runDir = runDirFor(context.commonDir, number), existing = readRun(runDir);
  if (existing && existing.state !== 'cancelled') return fail(`Issue #${number} already has a run (${existing.workflow}, ${describe(existing)}). Open it: pdd workflow open ${number}. Status: pdd workflow status ${number}.`);
  const warnings = [];
  if (existing) {
    const released = await releaseIssueClaim({ cwd: context.toplevel, runId: existing.runId, issueNumber: number }, p.commandPorts);
    if (released.state !== 'released') return fail(`Issue #${number} has a cancelled run, but pdd could not free the issue: ${released.message}`);
    warnings.push(`Issue #${number} had a cancelled run. Its worktree stays at ${existing.root} (branch ${existing.branch}). This run gets a new worktree and branch.`);
  }
  try { await p.execFile('git', ['fetch', 'origin', binding.defaultBranch], { cwd: context.toplevel }); }
  catch { warnings.push(`warning: "git fetch origin ${binding.defaultBranch}" failed; the worktree starts from the last fetched ${binding.defaultBranch}.`); }
  const runId = randomUUID();
  const allocated = await allocateIssueWorktree({ cwd: context.toplevel, repository: binding.repository, issueNumber: number, runId,
    workflowName: name, baseRef: `refs/remotes/origin/${binding.defaultBranch}` }, p.commandPorts);
  if (allocated.state !== 'ready' || !allocated.assignment) return fail(`pdd could not make the worktree for #${number}: ${allocated.message}`);
  const a = allocated.assignment;
  // Keep the cancelled run's record next to the new one; only a plain issue number names the active run.
  if (existing) renameSync(runDir, `${runDir}-cancelled-${existing.runId.slice(0, 8)}`);
  const run = { v: 1, runId, workflow: name, skill: workflow.skill, skillDir: workflow.dir, repo: binding.repository,
    issue: { number, title: binding.issue.title, url: binding.issue.url }, number, root: a.worktreePath, branch: a.branch,
    baseBranch: binding.defaultBranch, baseSha: a.baseSha, sourceRoot: a.sourceRoot, commonDir: a.commonDir, runDir, agent,
    configDir: (agent === 'claude' ? p.env.CLAUDE_CONFIG_DIR : p.env.CODEX_HOME) || null,
    startedAt: p.now(), state: 'running', areas: workflow.areas, area: 0, done: {}, gate: null, chats: [], decisions: [], changes: [],
    approvalRecord: null, pr: [], prState: null, cancelled: null, warnings, journalSeq: 0,
    previous: existing ? [...(existing.previous ?? []), { runId: existing.runId, root: existing.root, branch: existing.branch, runDir: `${runDir}-cancelled-${existing.runId.slice(0, 8)}` }] : [] };
  mkdirSync(runDir, { recursive: true });
  writeRun(run, p);
  const first = workflow.areas[0];
  try { run.chats.push(await startChat({ run, area: first.name, message: await areaMessage(run, 0, p, packageRoot) }, p)); }
  catch (error) {
    run.warnings.push(`The ${first.name} chat did not start (${error.code ?? 'error'}).`); writeRun(run, p);
    return fail([...warnings, `The worktree is ready at ${a.worktreePath}, but the ${first.name} chat did not start (${error.code ?? 'error'}: ${oneLine(error.message)}).`,
      `Start it with: pdd workflow open ${number}`].join('\n'));
  }
  writeRun(run, p);
  const chat = run.chats[0];
  return done([...warnings,
    `Started ${name} for ${run.repo}#${number} "${oneLine(run.issue.title)}".`,
    `Area 1 of ${run.areas.length}: ${first.name} (${first.steps.join(', ')}). ${agent === 'claude' ? 'Claude' : 'Codex'} works in Herdr session pdd, tab "${chat.label}".`,
    ...(agent === 'claude' && !claudeTrusts(run.sourceRoot, p.env) ? ['Claude may first ask you to trust the new worktree folder. Open the chat and choose "Yes, I trust this folder".'] : []),
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
function runtimeLines(text) {
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
// The step summary that holds the run's runtime result: the check step's, else the latest one with a Runtime check.
const checkSummary = (run, steps = Object.keys(run.done ?? {})) => /Runtime check/.test(run.done?.check?.summary ?? '') ? run.done.check.summary
  : steps.map(step => run.done[step]?.summary ?? '').reverse().find(text => /Runtime check/.test(text)) ?? null;
// "N of M Stories pass" from the latest check lines; a summary with only an overall line is one Story.
function storyCount(run) {
  const lines = runtimeLines(checkSummary(run));
  if (!lines.length) return null;
  const named = latestStories(lines), counted = named.length ? named : lines.slice(-1);
  return { pass: counted.filter(line => line.pass).length, total: counted.length, failing: counted.filter(line => !line.pass && line.story).map(line => line.story) };
}
const storyText = count => `${count.pass} of ${count.total} Stories pass`;
const shortLine = text => text.length <= 200 ? text : `${text.slice(0, 199).replace(/\s+\S*$/, '')}…`;
// Report links in a check summary, each once: "Report (<story>): <url>" keeps the Story name; a bare link has none.
function reportLinks(text, env) {
  const links = new Map();
  for (const [, story, url] of String(text ?? '').matchAll(/(?:\bReport\s*(?:\(([^)]*)\))?:\s*)?(https?:\/\/[^\s)<>\]"';]+)/g)) {
    if (hasReportLink(url, env) && !links.has(url)) links.set(url, story && story.trim().toUpperCase() !== 'DRAFT' ? story.trim() : null);
  }
  return [...links].map(([url, story]) => `Report${story ? ` (${story})` : ''}: ${url} (report links expire after 7 days)`);
}

function prBody(run, area, env, drafts = []) {
  const index = run.areas.indexOf(area), from = run.areas.slice(0, index).map((item, at) => item.gate === 'pr' ? at + 1 : 0).reduce((a, b) => Math.max(a, b), 0);
  const steps = run.areas.slice(from, index + 1).flatMap(item => item.steps).filter(step => run.done[step]);
  const raw = Object.fromEntries(steps.map(step => [step, hideLocalPaths(redactTry(run.done[step].summary), run)]));
  const summaries = Object.fromEntries(steps.map(step => [step, oneLine(raw[step])]));
  const lines = steps.map(step => `- **${step}**: ${shortLine(summaries[step]) || 'done'}`);
  // Only a PR that covers a verify step carries verify.md (PR 1 never does).
  let verify = null;
  if (steps.includes('verify')) {
    try { verify = redactTry(readFileSync(join(run.runDir, 'verify.md'), 'utf8').trim()); } catch { verify = '_verify.md was not written in the run folder._'; }
  }
  const label = prLabel(run, area), ask = askArea(run), pr1 = ask && prOf(run, ask.name);
  const head = label === 'PR 1' ? [`Part of #${run.number}`, '', 'PR 1 of this run: the prompt, Story and test cases. The code comes in PR 2 only when the person asks for it.']
    : label === 'PR 2' ? [`Closes #${run.number}`, '', `PR 2 of this run: the code. It builds on PR 1: ${pr1?.url}.`,
      ...(run.prBase && run.prBase !== run.baseBranch ? [`It is stacked on PR 1's branch \`${run.prBase}\`: merge PR 1 first.`] : [])]
    : [`Closes #${run.number}`];
  // verify writes "✗ N vectors fail" as its first line when cases still fail; the person must see it first.
  const failing = verify?.split('\n').find(row => row.trim())?.trim().startsWith('✗') ? [verify.split('\n').find(row => row.trim()).trim()] : [];
  // The Runtime check line and its report link go on top (#18).
  // The check step's result wins; else the latest step that reports a Runtime check. One line per Story (0.1.6), then the overall line.
  // Lines are read from the summary as stored, with its line breaks.
  const checked = /Runtime check/.test(raw.check ?? '') ? raw.check : Object.values(raw).reverse().find(text => /Runtime check/.test(text));
  const reports = checked ? reportLinks(checked, env) : [];
  const report = reports[0] ?? null;
  const runtime = checked ? [...runtimeTop(checked), ...reports] : [];
  const top = [...failing, ...runtime];
  return hideLocalPaths([...top, ...(top.length ? [''] : []), ...head, ...(drafts.length ? ['', draftLine(drafts)] : []), '', `Made with \`pdd workflow run ${run.workflow}\`.`, '', '## Steps', ...lines,
    ...(!report && hasReportLink([...lines, verify ?? ''].join('\n'), env) ? ['', 'Runtime report links expire after 7 days.'] : []),
    ...(verify !== null ? ['', '## Verify', '', verify] : []), ''].join('\n'), run);
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
  if (existing) {
    try { await p.execFile('git', ['push', 'origin', `HEAD:refs/heads/${run.branch}`], { cwd: run.root }); }
    catch { return fail([...lines, `git push to ${run.branch} failed. Check the network and gh auth, then ${retry}.`].join('\n')); }
    lines.push(`Pushed the new commits to ${label}.`);
    return null;
  }
  const bodyFile = join(run.runDir, `pr-${area.name}.md`), base = run.prBase ?? run.baseBranch;
  writeFileSync(bodyFile, prBody(run, area, p.env, label === 'PR 1' ? await draftPrompts(run, p, run.branch, base) : []));
  let intent;
  try {
    intent = await prepareWorkflowPr({ cwd: run.root, runId: run.runId, stageId: area.name, repository: run.repo, baseBranch: base, bodyFile,
      title: label === 'PR 1' ? `${title} (prompt, Story and tests)` : label === 'PR 2' ? `${title} (code)` : title }, p.commandPorts);
  } catch (error) {
    const why = error.code === 'workflow_github_topic_has_no_commits' ? `There are no new commits on ${run.branch}. Commit the change, then ${retry}.`
      : `pdd could not prepare ${label} (${error.code ?? 'error'}). Fix it, then ${retry}.`;
    return fail([...lines, why].join('\n'));
  }
  const outcome = await publishWorkflowPr({ cwd: run.root, intent }, p.commandPorts);
  if (!['open', 'merged'].includes(outcome.state) || !outcome.pr) return fail([...lines, `${label} did not open: ${outcome.message} ${retry[0].toUpperCase()}${retry.slice(1)} to retry.`].join('\n'));
  run.pr.push({ stage: area.name, number: outcome.pr.number, url: outcome.pr.url, branch: run.branch, base });
  return null;
}

// The code-or-stop question after PR 1, as the chat must show it.
async function askCodeLines(run, area, p) {
  const summaries = area.steps.filter(item => run.done[item]).map(item => `  ${item}: ${oneLine(run.done[item].summary) || 'done'}`);
  const drafts = await pr1Drafts(run, p);
  return [`PR 1: ${prOf(run, area.name).url}`, ...summaries, ...(drafts.length ? [draftLine(drafts), 'The code PR waits until the person approves those prompts.'] : []),
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
  run.done[step] = { at: p.now(), summary: keepLines(summary), area: area.name };
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
    run.gate = { area: area.name, at: p.now(), kind: 'approve-pr' }; run.state = 'waiting'; writeRun(run, p);
    lines.push(`pdd recorded ${step}. The ${area.name} area is done; pdd opens ${prLabel(run, area)} after the person approves.`,
      'Gate: show the person the Runtime check line of each Story (one per Story, ✓ or ✗) with the report link, and the Try link(s). Ask them to try it, then approve or ask for changes. Stop. Do not approve for them.',
      `When the person approves in their own words, run: ${p.pdd} workflow approve ${run.number}`,
      'If they ask for changes, revise in this chat, run done again for the step you changed, and ask again.');
    return done(lines.join('\n'));
  }
  if (area.gate === 'pr') return finishPr(run, area, step, p, lines);
  run.gate = { area: area.name, at: p.now(), kind: 'approve' }; run.state = 'waiting'; writeRun(run, p);
  lines.push(`pdd recorded ${step}. The ${area.name} area is done.`,
    'Gate: show the person the result, ask them to approve it or ask for changes, and stop. Do not approve for them.',
    `When the person approves in their own words, run: ${p.pdd} workflow approve ${run.number}`,
    'If they ask for changes, revise in this chat, run done again for the step you changed, and ask again.');
  return done(lines.join('\n'));
}

// The code area works on <branch>-code: on PR 1's head while PR 1 is open (PR 2 stacks on it), else on the merged default branch.
async function codeBranch(run, area, p) {
  const pr1 = prOf(run, area.name), name = `${pr1.branch}-code`;
  const state = await (p.readPrStatus ?? readWorkflowPrStatus)({ cwd: run.root, url: pr1.url }, p.commandPorts);
  if (!['open', 'merged'].includes(state.state)) throw Error(`PR 1 is ${state.state}, so pdd cannot tell where the code branch should start.`);
  const fetch = async ref => { try { await p.execFile('git', ['fetch', 'origin', ref], { cwd: run.root }); } catch { /* A stale ref only makes the PR base older. */ } };
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

async function startNextChat(run, p, packageRoot) {
  const area = run.areas[run.area];
  run.chats.push(await startChat({ run, area: area.name, message: await areaMessage(run, run.area, p, packageRoot) }, p));
  writeRun(run, p);
  return run.chats.at(-1);
}

export async function approveRun({ ref, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run, area = run.areas[run.area], label = `${run.repo}#${run.number} "${oneLine(run.issue.title)}"`;
  const askCode = area.then === 'ask-code', beforePr = run.gate?.kind === 'approve-pr';
  if (ended(run) && !(askCode && run.gate?.kind === 'ask-code')) return fail(`The run for ${run.repo}#${run.number} is ${run.state}. There is nothing to approve.`);
  if (area.gate === 'pr' && !askCode && !beforePr) return fail(`Nothing to approve for #${run.number}: the ${area.name} area ends with ${prLabel(run, area)}, which pdd opens after its last step.${prOf(run, area.name) ? ` ${prLabel(run, area) === 'the PR' ? 'PR' : prLabel(run, area)}: ${prOf(run, area.name).url}` : ''}`);
  const agent = isAgentSession(p.env), viaChat = agent || !p.isTTY;
  if (askCode && run.gate?.kind === 'ask-code') {
    const drafts = await pr1Drafts(run, p);
    if (drafts.length) return fail(`Approve the draft prompts first: ${drafts.join(', ')}. The code is built from approved prompts; pdd never approves them itself.`);
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
    const evidence = await read({ stage: { agent: run.agent, root: run.root, startedAt: chat.startedAt, endedAt: p.now(), ...(chat.session?.id ? { sessionId: chat.session.id } : {}) },
      gateAskedAt: run.gate.at, decision: 'approve', ignorePrefixes: [CHANGE_PREFIX, ANSWER_PREFIX] },
    { env: p.env, now: p.now, ...(chat.configDir ? (run.agent === 'claude' ? { claudeConfigDir: chat.configDir } : { codexHome: chat.configDir }) : {}) });
    if (evidence?.ok !== true) return fail(`Only the person can approve. Ask them in this chat and wait for their answer, then run this again. Or the person runs "pdd workflow approve ${run.number}" in a terminal. (${oneLine(evidence?.message) || 'no chat evidence'})`);
    if (askCode && !beforePr && !YES_WORDS.test(evidence.userMessage ?? '')) return fail(`Not sure you approved. Run \`pdd workflow approve ${run.number}\` in your terminal.`);
    record = { via: 'chat', text: evidence.userMessage, sessionId: evidence.sessionId, at: evidence.userMessageAt };
    if (!chat.session?.id && evidence.sessionId) chat.session = { agent: run.agent, id: evidence.sessionId };
  } else {
    if (!await confirm(p, beforePr ? `Approve the ${area.name} area and open ${prLabel(run, area) === 'the PR' ? 'the PR' : prLabel(run, area)} for ${label}? (y/N) `
      : askCode ? `Make the code PR now for ${label}? PR 1: ${prOf(run, area.name)?.url} (y/N) ` : `Approve the ${area.name} area for ${label}? (y/N) `)) return fail('Not approved. The run is unchanged.');
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
    run.state = 'waiting'; run.gate = askCode ? { area: area.name, at, kind: 'ask-code' } : null; writeRun(run, p);
    const head = [`Approved the ${area.name} area of ${label}.${said} pdd opened ${prLabel(run, area) === 'the PR' ? 'the PR' : prLabel(run, area)}.`, ...lines];
    if (!askCode) return done([...head, `PR: ${url}`, 'pdd never merges.'].join('\n'));
    if (viaChat) return done([...head, ...await askCodeLines(run, area, p)].join('\n'));
    if (!await confirm(p, `Make the code PR now for ${label}? PR 1: ${url} (y/N) `)) {
      await sendToChat(currentChat(run), `pdd opened PR 1: ${url}. The person approved it in their terminal and stops here for now. Tell them exactly: "PR 1 is open: ${url}. ${codeLater(run)}" Then stop.`, p);
      return done([...head, `PR 1: ${url}`, `Stopped at PR 1. ${codeLater(run)}`].join('\n'));
    }
    const drafts = await pr1Drafts(run, p);
    if (drafts.length) return fail([...head, `PR 1: ${url}`, `Approve the draft prompts first: ${drafts.join(', ')}. Then run pdd workflow approve ${run.number} to make the code PR.`].join('\n'));
  }
  let based = '';
  if (askCode) {
    // Reached at the code gate, or right after PR 1 opened when the terminal said yes to the code PR.
    try { based = await codeBranch(run, area, p); }
    catch (error) { return fail(`${oneLine(error.message)} Nothing changed. Check PR 1, then run pdd workflow approve ${run.number} again.`); }
  }
  const now = p.now();
  run.decisions.push({ stage: area.name, decision: 'approve', via: record.via, at: now, ...(record.text !== undefined ? { text: record.text } : {}) });
  run.approvalRecord = { kind: record.via, area: area.name, at: now, ...(record.text !== undefined ? { userMessage: record.text, userMessageAt: record.at, sessionId: record.sessionId } : {}) };
  run.gate = null; run.area++; run.state = 'running'; run.doneAt = null; writeRun(run, p);
  const next = run.areas[run.area];
  let chat;
  try { chat = await startNextChat(run, p, packageRoot); }
  catch (error) { return fail(`Approved the ${area.name} area of ${label}.${said} The ${next.name} chat did not start (${error.code ?? 'error'}). Start it: pdd workflow open ${run.number}`); }
  return done([`Approved the ${area.name} area of ${label}.${said}${based}`,
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
  if (!chat) return fail(`The ${area.name} area has no chat. Start it: pdd workflow open ${run.number}`);
  const request = oneLine(text);
  if (!request) return fail('Write the change request after the issue number.');
  // After pdd workflow ask the text is the person's answer; otherwise it is a change request.
  const answer = Boolean(run.question);
  const sent = await sendToChat(chat, answer ? `${ANSWER_PREFIX}: ${request} Go on with the step.`
    : `${CHANGE_PREFIX}: ${request} Revise in this chat, run done again for the step you changed, then show the result and ask again.`, p);
  if (!sent.ok) return fail(sent.code === 'agent_not_found' ? `The ${area.name} chat is not running. Open it with "pdd workflow open ${run.number}", then type the text there.`
    : sent.code === 'agent_blocked' ? `The ${area.name} chat shows a question dialog, and pdd cannot type into it. Answer it in the chat: pdd workflow open ${run.number}`
    : `pdd could not send the text to the ${area.name} chat (${sent.code}). Open it: pdd workflow open ${run.number}`);
  const now = p.now();
  run.changes.push({ stage: area.name, round: run.changes.filter(change => change.stage === area.name).length + 1, text: request, at: now, ...(answer ? { answer: true } : {}) });
  if (answer) { run.question = null; if (!run.gate) run.state = 'running'; }
  else if (run.gate) run.gate.at = now;
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

async function chatBlocked(run, p) {
  const chat = run.state === 'running' ? currentChat(run) : null;
  return chat ? (await chatSession(chat, p)).status === 'blocked' : false;
}

function detail(run, drafts = [], blocked = false) {
  const area = run.areas[run.area], chat = currentChat(run) ?? run.chats?.at(-1);
  const ci = pr => ({ passing: 'CI passing', failing: 'CI failing', pending: 'CI running', none: 'no CI checks' }[pr.ci] ?? 'CI unknown');
  const steps = (area?.steps ?? []).map(step => `${step} ${run.done[step] ? 'done' : 'to do'}${run.done[step]?.summary ? ` ("${oneLine(run.done[step].summary).slice(0, 120)}")` : ''}`);
  const next = run.gate?.kind === 'ask-code' ? `pdd workflow approve ${run.number}  (make the code PR)   or stop here and merge PR 1`
    : run.gate ? `pdd workflow approve ${run.number}   or   pdd workflow changes ${run.number} "what to change"`
    : ended(run) ? null : prOf(run, area?.name) ? `Review and merge ${run.pr.length > 1 && run.prBase && run.prBase !== run.baseBranch ? 'PR 1, then PR 2,' : 'the PR'} on GitHub. pdd never merges.` : `pdd workflow open ${run.number}`;
  return [`${run.repo}#${run.number} "${oneLine(run.issue.title)}" · ${run.workflow} · ${run.agent}`,
    `State: ${describe(run, blocked)}`,
    ...(area ? [`Area ${run.area + 1} of ${run.areas.length}: ${area.name} — ${steps.join(', ')}`] : []),
    ...(chat && !ended(run) ? [`Chat: Herdr session pdd, tab "${chat.label}" — pdd workflow open ${run.number}`] : []),
    ...(run.pr ?? []).map(pr => { const label = prLabel(run, run.areas.find(item => item.name === pr.stage) ?? {}); return `${label === 'the PR' ? 'PR' : label}: ${pr.url} — ${pr.state ?? 'open'}, ${ci(pr)}${pr.base && pr.base !== run.baseBranch ? ` (stacked on ${pr.base})` : ''}`; }),
    ...(drafts.length ? [draftLine(drafts)] : []),
    ...(storyCount(run) ? [`Stories: ${storyText(storyCount(run))}${storyCount(run).failing.length ? ` (✗ ${storyCount(run).failing.join(', ')})` : ''}`] : []),
    `Worktree: ${run.root} (branch ${run.branch})`, `Run folder: ${run.runDir}`, ...(next ? [`Next: ${next}`] : [])].join('\n');
}

// One list line per run, grouped by what it needs: the person, the agent, a PR review, nothing.
const GROUPS = ['waiting', 'working', 'pr-open', 'done', 'cancelled'];
function summary(run, timeZone, blocked = false) {
  const area = run.areas[run.area], ask = askArea(run);
  const group = run.state === 'cancelled' ? 'cancelled' : run.state === 'completed' ? 'done'
    : run.gate || run.question || blocked && run.state === 'running' ? 'waiting' : prOf(run, area?.name) ? 'pr-open' : 'working';
  const step = area?.steps.find(item => !run.done[item]);
  const words = group === 'cancelled' ? 'cancelled'
    : group === 'done' ? (run.gate?.kind === 'ask-code' ? 'done at PR 1' : 'done')
    : run.question ? `waiting for you: ${run.question.text.split('\n')[0]}`
    : !run.gate && blocked ? `waiting for you: the chat asks a question in its window`
    : run.gate?.kind === 'ask-code' ? 'waiting for you: code PR now or stop (PR 1 open)'
    : run.gate?.kind === 'approve-pr' ? `waiting for you: try it, then approve to open ${area.then === 'ask-code' ? 'PR 1' : 'the PR'}`
    : run.gate ? `waiting for you: approve the ${run.gate.area}`
    : group === 'pr-open' ? `${!ask ? 'PR' : area.then === 'ask-code' ? 'PR 1' : 'PR 2'} open`
    : step ? `agent working on ${step}` : 'agent working';
  const ref = `${run.repo}#${run.number}`;
  const when = Number.isFinite(run.updatedAt) ? new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit', hourCycle: 'h23', ...(timeZone ? { timeZone } : {}) }).format(new Date(run.updatedAt)) : 'unknown time';
  const prs = (run.pr ?? []).map(pr => ({ number: pr.number, url: pr.url, state: pr.state ?? 'open' })), stories = storyCount(run);
  return { ref, repo: run.repo, number: run.number, workflow: run.workflow, area: area?.name ?? null, group, words, prs, stories,
    updatedAt: run.updatedAt ?? null, root: run.root, runDir: run.runDir,
    line: [ref, run.workflow, area?.name ?? '?', words, ...(stories ? [storyText(stories)] : []), ...(prs.length ? [`PR ${prs.map(pr => `#${pr.number}`).join(' ')}`] : []), when].join(' · ') };
}

async function listStatus(runs, { json, cancelled, scope }, p) {
  for (const run of runs) if (run.state === 'waiting' && run.pr?.length) { try { await refreshPr(run, p); } catch { /* A PR read failure keeps the saved state. */ } }
  const all = [];
  for (const run of runs) all.push(summary(run, p.timeZone, await chatBlocked(run, p)));
  const hidden = cancelled ? 0 : all.filter(item => item.group === 'cancelled').length;
  const shown = all.filter(item => cancelled || item.group !== 'cancelled')
    .sort((a, b) => GROUPS.indexOf(a.group) - GROUPS.indexOf(b.group) || (b.updatedAt ?? 0) - (a.updatedAt ?? 0));
  if (json) return done(JSON.stringify({ runs: shown.map(({ line, ...item }) => item) }, null, 2));
  if (!shown.length) return done([`No pdd runs ${scope}.${hidden ? ` ${hidden} cancelled run${hidden > 1 ? 's' : ''} hidden; add --cancelled to see ${hidden > 1 ? 'them' : 'it'}.` : ''}`, 'Start one with: pdd workflow run NAME ISSUE'].join('\n'));
  return done([...shown.map(item => item.line),
    ...(hidden ? [`${hidden} cancelled run${hidden > 1 ? 's' : ''} hidden; add --cancelled to see ${hidden > 1 ? 'them' : 'it'}.`] : []),
    `Open one: pdd workflow open ${shown[0].ref}`].join('\n'));
}

export async function runStatus({ ref, cwd, all = false, json = false, cancelled = false }, ports) {
  const p = deps(ports);
  if (ref === undefined && (all || !(await gitContext(cwd, p)))) return listStatus(allRuns({ cancelled }, p), { json, cancelled, scope: 'on this machine' }, p);
  if (ref === undefined && !(await runForWorktree(cwd, p))) return listStatus(await listRuns({ cwd, cancelled }, p), { json, cancelled, scope: 'in this repository' }, p);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  await refreshPr(found.run, p);
  const run = found.run, drafts = run.gate?.kind === 'ask-code' ? await pr1Drafts(run, p) : [];
  const blocked = await chatBlocked(run, p);
  if (json) { const { line, ...item } = summary(run, p.timeZone, blocked); return done(JSON.stringify({ runs: [item] }, null, 2)); }
  return done(detail(run, drafts, blocked));
}

export async function openRun({ ref, cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  const run = found.run;
  if (ended(run)) return fail(`The run for ${run.repo}#${run.number} is ${run.state}. Its worktree is ${run.root}.`);
  let chat = currentChat(run), started = false;
  try {
    if (!chat) { chat = await startNextChat(run, p, packageRoot); started = true; }
    const opened = await openChat({ run, chat }, p);
    writeRun(run, p);
    const where = `Herdr session pdd, tab "${chat.label}"`;
    return done([started ? `Started the ${chat.area} chat in ${where}.` : opened.resumed ? `Resumed the ${chat.area} chat in ${where}.` : `The ${chat.area} chat is in ${where}.`,
      ...(opened.attached ? [] : [p.env.HERDR_ENV === '1' ? 'pdd focused that tab. If you are in another Herdr session, run: herdr session attach pdd' : 'See it with: herdr session attach pdd'])].join('\n'));
  } catch (error) {
    return fail(`pdd could not open the ${run.areas[run.area].name} chat (${error.code ?? 'error'}: ${oneLine(error.message)}).`);
  }
}
