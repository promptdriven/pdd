// Generated from prompts/cli/session-intro.prompt.md (sha256: 63e14534dfccfc174e4390617459a6f178e686ee3b6ef117c26e7cba2aa2f4ce).
import { lstatSync, readFileSync } from 'node:fs';
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
    request || 'Ask what the person wants to work on.',
    ...(workflowName !== undefined ? [`Use the pdd-${workflowName} skill for this request.`] : []),
  ].join('\n');
}
