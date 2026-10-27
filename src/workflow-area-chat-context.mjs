// Generated from prompts/cli/workflow-area-chat-context.prompt.md (sha256: e7b0c4f70eb9299cd69a29e6a2309f2b43787087dbf97750986cc11c59f85f21).
import { readFileSync } from 'node:fs';

const names = ['common', 'plan', 'build', 'scope', 'change', 'verify', 'open-pr', 'wait-merge'];
const stages = names.slice(3);
function required(value, field) {
  if (typeof value !== 'string' || !value.trim()) throw Error(`Missing or invalid ${field}.`);
  return value;
}
function templates(prompts) {
  for (const name of names) required(prompts?.[name], `prompts.${name}`);
  return prompts;
}
export function loadAreaChatPrompts() {
  return templates(Object.fromEntries(names.map(name => [name,
    readFileSync(new URL(`../.pdd/workflows/small-change/area-chats/${name}.md`, import.meta.url), 'utf8')])));
}
function commandPrefix(argv = ['pdd']) {
  if (!Array.isArray(argv) || !argv.length || argv.some(arg => typeof arg !== 'string' || !arg.trim() || /[\0\r\n]/.test(arg)))
    throw Error('Invalid pddCommand argv.');
  return argv.map(arg => /^[a-zA-Z0-9_./:-]+$/.test(arg) ? arg : `'${arg.replaceAll("'", "'\\''")}'`).join(' ');
}
function substitutions(prefix, issueNumber) {
  return { approveCommand: `${prefix} workflow approve ${issueNumber}`,
    scopeCommand: `${prefix} step done scope`, changeCommand: `${prefix} step done change`,
    verifyCommand: `${prefix} step done verify`, openPrCommand: `${prefix} step done open-pr`,
    waitMergeCommand: `${prefix} step done wait-merge` };
}
function render(template, values) {
  return template.replace(/\{\{(approveCommand|scopeCommand|changeCommand|verifyCommand|openPrCommand|waitMergeCommand)\}\}/g,
    (_, key) => values[key]);
}
export function buildAreaChatPrompt({ area, agent, issueNumber, runId, context, prompts, pddCommand } = {}) {
  if (!['plan', 'build'].includes(area)) throw Error('Invalid area.');
  if (!['codex', 'claude'].includes(agent)) throw Error('Invalid agent.');
  if (!Number.isSafeInteger(issueNumber) || issueNumber < 1) throw Error('Invalid issueNumber.');
  required(runId, 'runId'); required(context, 'context'); templates(prompts);
  const values = substitutions(commandPrefix(pddCommand), issueNumber);
  const delegation = agent === 'codex'
    ? 'Use Codex native multi_agent tools to delegate one current stage and wait for its result.'
    : 'Use Claude native subagents to delegate one current stage and wait for its result.';
  return `${context}\n\n# Assigned area chat\n${JSON.stringify({ runId, issueNumber, area, agent })}\n\n${delegation}\n\n${render(prompts.common, values)}\n\n${render(prompts[area], values)}`;
}
export function buildAreaStageTask({ stageId, instructions, prompts, pddCommand } = {}) {
  if (!stages.includes(stageId)) throw Error('Invalid stageId.');
  required(instructions, 'instructions'); templates(prompts);
  const values = substitutions(commandPrefix(pddCommand));
  return `${render(prompts[stageId], values)}\n\n# Exact current-stage request from PDD\n${instructions}`;
}

export function buildAreaChatInstructions({ area, stageInstructions, reportCommand, approvalCommand,
  changesText, prompts = loadAreaChatPrompts() } = {}) {
  const expected = { plan: ['Chat 1: plan', 'approve-plan'], build: ['Chat 2: build', 'merge'] }[area?.id];
  if (!expected || area.label !== expected[0] || area.gate !== expected[1]) throw Error('Invalid area identity.');
  required(stageInstructions, 'stageInstructions'); templates(prompts);
  for (const [field, value] of Object.entries({ reportCommand, approvalCommand })) {
    required(value, field);
    if (/[\0\r\n]/.test(value)) throw Error(`Invalid ${field}.`);
  }
  if (changesText != null) required(changesText, 'changesText');
  const values = { approveCommand: approvalCommand };
  for (const [key, stage] of Object.entries({ scopeCommand: 'scope', changeCommand: 'change',
    verifyCommand: 'verify', openPrCommand: 'open-pr', waitMergeCommand: 'wait-merge' })) {
    values[key] = area.id === 'plan' && stage === 'scope' ? reportCommand
      : `the exact current report command supplied by PDD for ${stage}`;
  }
  const stageIds = area.id === 'plan' ? ['scope'] : ['change', 'verify', 'open-pr', 'wait-merge'];
  return [prompts.common,
    'Use Codex native multi_agent tools for Codex, or Claude native subagents for Claude. The runner supplies the full saved guide and workflow context before these instructions.',
    render(prompts[area.id], values),
    '# Reporting the current attempt',
    'After the current subagent returns its handoff, invoke exactly the following command in the assigned worktree. It reports this attempt only; use the returned nextStageInstructions and its new report command for subsequent stages.',
    reportCommand,
    changesText ? `# Supported changes route\n${changesText}` : '',
    '# Stage task references — supply only the current one to its subagent',
    ...stageIds.map(id => render(prompts[id], values)),
    '# Exact current-stage request from PDD', stageInstructions].filter(Boolean).join('\n\n');
}
