// Generated from prompts/cli/session-intro.prompt.md (sha256: 28724ffcaf96d053a7185a793ba4de3ba25781219e0c65d080851f8967d3590e).
import { lstatSync, readFileSync, statSync } from 'node:fs';
import { join, resolve } from 'node:path';

const shellWord = value => /^[A-Za-z0-9_@%+=:,./-]+$/.test(value) ? value : `'${value.replace(/'/g, "'\\''")}'`;

function coreRules(packageRoot) {
  const text = readFileSync(join(packageRoot, 'skills/pdd-prompting/SKILL.md'), 'utf8');
  const section = text.split(/^## /m).find(part => part.startsWith('Core rules\n')) ?? '';
  const rules = section.split('\n').filter(line => line.startsWith('- '));
  if (!rules.length) throw Error('The pdd-prompting skill has no core rules');
  return rules;
}

export function renderSessionIntro({ packageRoot, cwd, request = '', workflowName }) {
  const rules = coreRules(packageRoot);
  if (workflowName !== undefined && !lstatSync(join(packageRoot, 'skills', `pdd-${workflowName}`, 'SKILL.md')).isFile()) {
    throw Error('The selected workflow skill is not a file');
  }
  const pdd = [process.execPath, resolve(packageRoot, 'bin/pdd.mjs')].map(shellWord).join(' ');
  const runbook = resolve(packageRoot, 'RUNBOOK.md');
  let hasRunbook = false;
  try { hasRunbook = statSync(runbook).isFile(); } catch { /* No runbook yet: the intro names none. */ }
  return [
    `This is a PDD session in ${cwd}.`,
    'In PDD, prompts are the source. Write the prompt, Story and test cases first, then the code.',
    '',
    'Prompting guide = the pdd-prompting skill. Read its guide.md in full before you write or change a prompt, Story or test cases.',
    'Core rules:',
    ...rules,
    '',
    'Workflows = the skills pdd-small-change, pdd-bug and pdd-feature.',
    '- To do the work in this chat, follow the matching skill here.',
    `- To turn a GitHub issue into a PR: ${pdd} workflow run <name> <issue> (you can start it for the person when they ask).`,
    'When a request fits a workflow, suggest it.',
    '',
    `Use this pdd: ${pdd}`,
    `If a skill is missing, read it in ${resolve(packageRoot, 'skills')}.`,
    ...(hasRunbook ? [`Runtime: read ${runbook} before you run a check.`] : []),
    request || 'Ask what the person wants to work on.',
    ...(workflowName !== undefined ? [`Use the pdd-${workflowName} skill for this request.`] : []),
  ].join('\n');
}
