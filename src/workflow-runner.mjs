// Generated from prompts/cli/workflow-runner.prompt.md (sha256: 545bf5d613b0782b04ea7cf98b8710150fffa11a98c87cd280845f9f85615f25).
import { execFile as execFileCallback } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join } from 'node:path';
import { createInterface } from 'node:readline/promises';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { readWorkflowAreas } from './workflow-areas.mjs';
import { resolveWorkflowIssue, prepareWorkflowPr, publishWorkflowPr, readWorkflowPrStatus } from './workflow-github.mjs';
import { allocateIssueWorktree } from './workflow-worktree.mjs';
import { currentChat, gitContext, listRuns, readRun, resolveRun, runDirFor, runForWorktree, writeRun } from './workflow-runs.mjs';
import { startChat, sendToChat, chatSession, openChat, closeChats } from './workflow-chat.mjs';

const PACKAGE_ROOT = dirname(dirname(fileURLToPath(import.meta.url)));
const CHANGE_PREFIX = 'The person asks for changes';
const ordinary = promisify(execFileCallback);
const shell = value => /^[A-Za-z0-9_@%+=:,./-]+$/.test(value) ? value : `'${value.replace(/'/g, `'\\''`)}'`;
const oneLine = value => String(value ?? '').replace(/\s+/g, ' ').trim();
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
const pddFor = (p, packageRoot) => p.pdd ?? [process.execPath, join(packageRoot ?? PACKAGE_ROOT, 'bin', 'pdd.mjs')].map(shell).join(' ');
async function git(p, cwd, ...args) { return String((await p.execFile('git', args, { cwd })).stdout ?? '').trim(); }

async function confirm(p, question) {
  if (p.confirm) return p.confirm(question);
  const rl = createInterface({ input: p.stdin ?? process.stdin, output: p.stderr ?? process.stderr });
  try { return /^(?:y|yes)$/i.test((await rl.question(question)).trim()); } finally { rl.close(); }
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
  const summaries = earlier.filter(step => run.done[step]).map(step => `${step}: ${oneLine(run.done[step].summary) || 'done'}`);
  const files = index ? await changedFiles(run, p) : [];
  return [
    `Use the ${run.skill} skill. This is a pdd workflow run.${index ? ' The person approved the earlier areas.' : ''}`,
    `Issue: ${run.repo}#${run.number} "${oneLine(run.issue.title)}" ${run.issue.url}`,
    `Worktree: ${run.root} (branch ${run.branch}). Work and commit only here.`,
    `Run folder: ${run.runDir}. Put notes there. verify writes verify.md there with the exact test commands and their output.`,
    ...(index ? [`Approved so far: ${summaries.join('; ') || 'no step summaries'}.`, `Changed files: ${files.slice(0, 20).join(', ') || 'none yet'}${files.length > 20 ? ', …' : ''}.`] : []),
    `Area ${index + 1} of ${run.areas.length}: ${area.name}. Steps: ${area.steps.map(step => area.optional.includes(step) ? `${step} (optional: ask the person)` : step).join(', ')}.`,
    `After each step, run: ${pdd} workflow done STEP --summary "one line". It prints what to do next.`,
    area.gate === 'approve'
      ? `Gate: after the last step, show the person the result, ask them to approve or ask for changes, and stop. Never approve for them: they approve in their own words, or run pdd workflow approve ${run.number}.`
      : 'After the last step, pdd pushes the branch and opens the PR. Never push, open a PR or merge yourself.',
    `If the ${run.skill} skill is not available, read ${join(packageRoot ?? PACKAGE_ROOT, 'skills', run.skill, 'SKILL.md')}.`,
  ].join('\n') + '\n';
}

function describe(run) {
  const area = run.areas[run.area];
  if (run.state === 'cancelled') return 'cancelled';
  if (run.state === 'completed') return 'complete: the PR is merged';
  if (run.gate) return `waiting for you: approve the ${run.gate.area} area or ask for changes`;
  if (run.pr?.length) return 'waiting for you: review and merge the PR on GitHub';
  const step = area?.steps.find(item => !run.done[item]);
  return step ? `the agent works on ${step}` : 'the agent works';
}

export async function startRun({ name, issue, agent = 'codex', cwd, packageRoot = PACKAGE_ROOT }, ports) {
  const p = deps(ports); p.pdd = pddFor(p, packageRoot);
  let workflow;
  try { workflow = readWorkflowAreas({ packageRoot, name }); } catch (error) { return fail(error.message); }
  if (!['codex', 'claude'].includes(agent)) return fail('Choose --agent codex or --agent claude.');
  const context = await gitContext(cwd, p);
  if (!context) return fail('Run this inside a Git checkout of the repository that has the issue.');
  let binding;
  try { binding = await resolveWorkflowIssue({ cwd: context.toplevel, issue }, p.commandPorts); }
  catch (error) { return fail(`pdd could not read issue ${issue} with gh (${error.code ?? 'error'}). Check "gh auth status", the origin remote and the issue number.`); }
  const number = binding.issue.number, runDir = runDirFor(context.commonDir, number), existing = readRun(runDir);
  if (existing) return fail(existing.state === 'cancelled'
    ? `Issue #${number} has a cancelled run. Its worktree stays at ${existing.root}. pdd 0.2 cannot start the same issue again.`
    : `Issue #${number} already has a run (${existing.workflow}, ${describe(existing)}). Open it: pdd workflow open ${number}. Status: pdd workflow status ${number}.`);
  const warnings = [];
  try { await p.execFile('git', ['fetch', 'origin', binding.defaultBranch], { cwd: context.toplevel }); }
  catch { warnings.push(`warning: "git fetch origin ${binding.defaultBranch}" failed; the worktree starts from the last fetched ${binding.defaultBranch}.`); }
  const runId = randomUUID();
  const allocated = await allocateIssueWorktree({ cwd: context.toplevel, repository: binding.repository, issueNumber: number, runId,
    workflowName: name, baseRef: `refs/remotes/origin/${binding.defaultBranch}` }, p.commandPorts);
  if (allocated.state !== 'ready' || !allocated.assignment) return fail(`pdd could not make the worktree for #${number}: ${allocated.message}`);
  const a = allocated.assignment;
  const run = { v: 1, runId, workflow: name, skill: workflow.skill, repo: binding.repository,
    issue: { number, title: binding.issue.title, url: binding.issue.url }, number, root: a.worktreePath, branch: a.branch,
    baseBranch: binding.defaultBranch, baseSha: a.baseSha, sourceRoot: a.sourceRoot, commonDir: a.commonDir, runDir, agent,
    configDir: (agent === 'claude' ? p.env.CLAUDE_CONFIG_DIR : p.env.CODEX_HOME) || null,
    startedAt: p.now(), state: 'running', areas: workflow.areas, area: 0, done: {}, gate: null, chats: [], decisions: [], changes: [],
    approvalRecord: null, pr: [], prState: null, cancelled: null, warnings, journalSeq: 0 };
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

function prBody(run) {
  const steps = run.areas.flatMap(area => area.steps).filter(step => run.done[step]);
  let verify;
  try { verify = readFileSync(join(run.runDir, 'verify.md'), 'utf8').trim(); } catch { verify = '_verify.md was not written in the run folder._'; }
  return [`Closes #${run.number}`, '', `Made with \`pdd workflow run ${run.workflow}\`.`, '', '## Steps',
    ...steps.map(step => `- **${step}**: ${oneLine(run.done[step].summary) || 'done'}`), '', '## Verify', '', verify, ''].join('\n');
}

async function finishPr(run, step, p, lines) {
  lines.push(`pdd recorded ${step}. pdd opens the PR now.`);
  const status = await git(p, run.root, 'status', '--porcelain=v1', '--untracked-files=all');
  if (status) {
    const files = status.split('\n').map(row => row.slice(3)).filter(Boolean);
    await git(p, run.root, 'add', '-A');
    await git(p, run.root, 'commit', '-q', '-m', `${oneLine(run.issue.title)} (#${run.number})`);
    lines.push(`warning: pdd committed ${files.length} uncommitted file(s): ${files.slice(0, 10).join(', ')}${files.length > 10 ? ', …' : ''}.`);
  }
  if (run.pr.length) {
    try { await p.execFile('git', ['push', 'origin', `HEAD:refs/heads/${run.branch}`], { cwd: run.root }); }
    catch { return fail([...lines, `git push to ${run.branch} failed. Check the network and gh auth, then run done ${step} again.`].join('\n')); }
    lines.push(`Pushed the new commits to the PR.`);
  } else {
    const bodyFile = join(run.runDir, 'pr-body.md');
    writeFileSync(bodyFile, prBody(run));
    let intent;
    try {
      intent = await prepareWorkflowPr({ cwd: run.root, runId: run.runId, stageId: 'pr', repository: run.repo, baseBranch: run.baseBranch,
        bodyFile, title: oneLine(run.issue.title).slice(0, 256) || `Issue #${run.number}` }, p.commandPorts);
    } catch (error) {
      const why = error.code === 'workflow_github_topic_has_no_commits' ? `There are no commits on ${run.branch}. Commit the change, then run done ${step} again.`
        : `pdd could not prepare the PR (${error.code ?? 'error'}). Fix it, then run done ${step} again.`;
      return fail([...lines, why].join('\n'));
    }
    const outcome = await publishWorkflowPr({ cwd: run.root, intent }, p.commandPorts);
    if (!['open', 'merged'].includes(outcome.state) || !outcome.pr) return fail([...lines, `The PR did not open: ${outcome.message} Run done ${step} again to retry.`].join('\n'));
    run.pr = [{ stage: 'pr', number: outcome.pr.number, url: outcome.pr.url }];
  }
  run.state = 'waiting'; run.gate = null; writeRun(run, p);
  return done([...lines, `PR: ${run.pr[0].url}`, 'Tell the person the PR is open. pdd never merges. Stop here.'].join('\n'));
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
  run.done[step] = { at: p.now(), summary: oneLine(summary), area: area.name };
  const next = area.steps.find(item => !run.done[item]);
  if (next) {
    run.state = 'running'; run.gate = null; writeRun(run, p);
    lines.push(`pdd recorded ${step}.`, area.optional.includes(next)
      ? `Next step: ${next} (optional). Ask the person if they want it. If they do not, run: ${p.pdd} workflow done ${next} --summary "skipped"`
      : `Next step: ${next}.`, `When it is done, run: ${p.pdd} workflow done ${next} --summary "one line"`);
    return done(lines.join('\n'));
  }
  if (area.gate === 'pr') return finishPr(run, step, p, lines);
  run.gate = { area: area.name, at: p.now() }; run.state = 'waiting'; writeRun(run, p);
  lines.push(`pdd recorded ${step}. The ${area.name} area is done.`,
    'Gate: show the person the result, ask them to approve it or ask for changes, and stop. Do not approve for them.',
    `When the person approves in their own words, run: ${p.pdd} workflow approve ${run.number}`,
    'If they ask for changes, revise in this chat, run done again for the step you changed, and ask again.');
  return done(lines.join('\n'));
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
  if (ended(run)) return fail(`The run for ${run.repo}#${run.number} is ${run.state}. There is nothing to approve.`);
  if (area.gate === 'pr') return fail(`Nothing to approve for #${run.number}: the ${area.name} area ends with the PR, which pdd opens after its last step.${run.pr.length ? ` PR: ${run.pr[0].url}` : ''}`);
  const agent = isAgentSession(p.env), viaChat = agent || !p.isTTY;
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
      gateAskedAt: run.gate.at, decision: 'approve', ignorePrefixes: [CHANGE_PREFIX] },
    { env: p.env, now: p.now, ...(chat.configDir ? (run.agent === 'claude' ? { claudeConfigDir: chat.configDir } : { codexHome: chat.configDir }) : {}) });
    if (evidence?.ok !== true) return fail(`Only the person can approve. Ask them in this chat and wait for their answer, then run this again. Or the person runs "pdd workflow approve ${run.number}" in a terminal. (${oneLine(evidence?.message) || 'no chat evidence'})`);
    record = { via: 'chat', text: evidence.userMessage, sessionId: evidence.sessionId, at: evidence.userMessageAt };
  } else {
    if (!await confirm(p, `Approve the ${area.name} area for ${label}? (y/N) `)) return fail('Not approved. The run is unchanged.');
    record = { via: 'terminal' };
  }
  const now = p.now();
  run.decisions.push({ stage: area.name, decision: 'approve', via: record.via, at: now, ...(record.text !== undefined ? { text: record.text } : {}) });
  run.approvalRecord = { kind: record.via, area: area.name, at: now, ...(record.text !== undefined ? { userMessage: record.text, userMessageAt: record.at, sessionId: record.sessionId } : {}) };
  run.gate = null; run.area++; run.state = 'running'; writeRun(run, p);
  const next = run.areas[run.area];
  const said = record.text !== undefined ? ` The person wrote: "${oneLine(record.text).slice(0, 300)}".` : '';
  let chat;
  try { chat = await startNextChat(run, p, packageRoot); }
  catch (error) { return fail(`Approved the ${area.name} area of ${label}.${said} The ${next.name} chat did not start (${error.code ?? 'error'}). Start it: pdd workflow open ${run.number}`); }
  return done([`Approved the ${area.name} area of ${label}.${said}`,
    `Started area ${run.area + 1} of ${run.areas.length}: ${next.name} (${next.steps.join(', ')}) in a new chat: Herdr session pdd, tab "${chat.label}".`,
    `Watch it: pdd workflow open ${run.number}`, ...(agent ? ['This chat\'s work is done. Stop here.'] : [])].join('\n'));
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
  const sent = await sendToChat(chat, `${CHANGE_PREFIX}: ${request} Revise in this chat, run done again for the step you changed, then show the result and ask again.`, p);
  if (!sent.ok) return fail(sent.code === 'agent_not_found' ? `The ${area.name} chat is not running. Open it with "pdd workflow open ${run.number}", then type the change there.`
    : sent.code === 'agent_blocked' ? `The ${area.name} chat waits for an answer in its window. Open it: pdd workflow open ${run.number}`
    : `pdd could not send the change to the ${area.name} chat (${sent.code}). Open it: pdd workflow open ${run.number}`);
  const now = p.now();
  run.changes.push({ stage: area.name, round: run.changes.filter(change => change.stage === area.name).length + 1, text: request, at: now });
  if (run.gate) run.gate.at = now;
  writeRun(run, p);
  return done(`Sent your change request to the ${area.name} chat of #${run.number}. The gate stays open. Approve when you are happy: pdd workflow approve ${run.number}`);
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
  const cwd = existsSync(run.root) ? run.root : run.sourceRoot;
  const state = await (p.readPrStatus ?? readWorkflowPrStatus)({ cwd, url: run.pr[0].url }, p.commandPorts);
  run.prState = { ...state, checkedAt: p.now() };
  if (state.state === 'merged') run.state = 'completed';
  writeRun(run, p);
}

function detail(run) {
  const area = run.areas[run.area], chat = currentChat(run) ?? run.chats?.at(-1);
  const ci = { passing: 'CI passing', failing: 'CI failing', pending: 'CI running', none: 'no CI checks' }[run.prState?.ci] ?? 'CI unknown';
  const steps = (area?.steps ?? []).map(step => `${step} ${run.done[step] ? 'done' : 'to do'}${run.done[step]?.summary ? ` ("${run.done[step].summary.slice(0, 120)}")` : ''}`);
  const next = run.gate ? `pdd workflow approve ${run.number}   or   pdd workflow changes ${run.number} "what to change"`
    : ended(run) ? null : run.pr?.length ? 'Review and merge the PR on GitHub. pdd never merges.' : `pdd workflow open ${run.number}`;
  return [`${run.repo}#${run.number} "${oneLine(run.issue.title)}" · ${run.workflow} · ${run.agent}`,
    `State: ${describe(run)}`,
    ...(area ? [`Area ${run.area + 1} of ${run.areas.length}: ${area.name} — ${steps.join(', ')}`] : []),
    ...(chat && !ended(run) ? [`Chat: Herdr session pdd, tab "${chat.label}" — pdd workflow open ${run.number}`] : []),
    ...(run.pr?.length ? [`PR: ${run.pr[0].url} — ${run.prState?.state ?? 'open'}, ${ci}`] : []),
    `Worktree: ${run.root} (branch ${run.branch})`, `Run folder: ${run.runDir}`, ...(next ? [`Next: ${next}`] : [])].join('\n');
}

export async function runStatus({ ref, cwd }, ports) {
  const p = deps(ports);
  if (ref === undefined && !(await runForWorktree(cwd, p))) {
    const runs = await listRuns({ cwd }, p);
    if (!runs.length) return done('No pdd runs here. Start one with: pdd workflow run NAME ISSUE');
    for (const run of runs) await refreshPr(run, p);
    return done(runs.map(run => `${run.repo}#${run.number} "${oneLine(run.issue.title).slice(0, 60)}" · ${run.workflow} · ${describe(run)}${run.pr?.length ? ` · ${run.pr[0].url}` : ''}`).join('\n'));
  }
  const found = await resolveRun(ref, { cwd }, p);
  if (found.error) return fail(found.error);
  await refreshPr(found.run, p);
  return done(detail(found.run));
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
