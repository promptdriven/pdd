// Prompt: prompts/cli/completion.prompt.md
import { PUBLIC_COMMAND_ROUTES } from './command-catalog.mjs';

function add(map, key, value) {
  if (!map.has(key)) map.set(key, new Set());
  map.get(key).add(value);
}

function candidateMaps() {
  const first = new Set(['--help', '-h', '--version']);
  const second = new Map();
  const third = new Map();
  const fourth = new Map();
  for (const { options, ...rest } of PUBLIC_COMMAND_ROUTES) {
    const route = { ...rest, options: options.filter(option => !option.hidden) };
    if (!route.prefix.length) continue;
    if (route.prefix[0]) first.add(route.prefix[0]);
    if (route.prefix.length > 1) add(second, route.prefix[0], route.prefix[1]);
    else {
      for (const option of route.options) add(second, route.prefix[0], option.name);
      for (const item of route.operands) {
        if (item.type.startsWith('choice:')) for (const choice of item.type.slice(7).split(',')) add(second, route.prefix[0], choice);
      }
    }
    if (route.prefix.length > 2) add(third, `${route.prefix[0]}:${route.prefix[1]}`, route.prefix[2]);
    for (const option of route.options) if (option.choices) for (const choice of option.choices) {
      if (route.prefix.length === 1) add(third, `${route.prefix[0]}:${option.name}`, choice);
      else if (route.prefix.length === 2) add(fourth, `${route.prefix.join(':')}:${option.name}`, choice);
    }
    if (route.prefix.length > 1) {
      for (const option of route.options) add(third, `${route.prefix[0]}:${route.prefix[1]}`, option.name);
      for (const item of route.operands) {
        if (item.type.startsWith('choice:')) for (const choice of item.type.slice(7).split(',')) add(third, `${route.prefix[0]}:${route.prefix[1]}`, choice);
      }
    }
  }
  for (const route of PUBLIC_COMMAND_ROUTES) if (route.prefix[0] && !route.prefix[0].startsWith('-')) add(second, 'help', route.prefix[0]);
  return { first: [...first].sort(), second, third, fourth };
}

const quoteWords = (values) => [...values].sort().join(' ');


export function renderCompletion(shell) {
  if (shell !== 'bash' && shell !== 'zsh') throw new TypeError('Choose bash or zsh.');
  const maps = candidateMaps();
  const valueChoices = new Map();
  for (const route of PUBLIC_COMMAND_ROUTES) {
    for (const option of route.options) {
      if (!option.hidden && option.choices) {
        const key = route.prefix.length ? `${route.prefix[0]}:${option.name}` : `*:${option.name}`;
        valueChoices.set(key, option.choices);
      }
    }
  }
  const bashValues = [...valueChoices].map(([name,values])=>`    ${name}) COMPREPLY=( $(compgen -W '${quoteWords(values)}' -- "$current") ); return ;;`).join('\n');
  const zshValues = [...valueChoices].map(([name,values])=>`    ${name}) choices=(${quoteWords(values)}); _describe "PDD option" choices; return ;;`).join('\n');
  const secondCases = [...maps.second].map(([key, values]) => `      ${key}) choices='${quoteWords(values)}' ;;`).join('\n');
  const thirdCases = [...maps.third].map(([key, values]) => `      ${key}) choices='${quoteWords(values)}' ;;`).join('\n');
  const fourthCases = [...maps.fourth].map(([key, values]) => `      ${key}) choices='${quoteWords(values)}' ;;`).join('\n');
  if (shell === 'bash') {
    return [
      '# Bash completion for pdd',
      '_pdd_complete() {',
      '  local current="${COMP_WORDS[COMP_CWORD]}" choices',
      '  case "${COMP_WORDS[1]}:${COMP_WORDS[COMP_CWORD-1]}" in', bashValues, '  esac',
      '  case "$COMP_CWORD" in',
      `    1) choices='${quoteWords(maps.first)}' ;;`,
      '    2) case "${COMP_WORDS[1]}" in', secondCases, '      *) choices="" ;;', '    esac ;;',
      '    3) case "${COMP_WORDS[1]}:${COMP_WORDS[2]}" in', thirdCases, '      *) choices="" ;;', '    esac ;;',
      '    4) case "${COMP_WORDS[1]}:${COMP_WORDS[2]}:${COMP_WORDS[3]}" in', fourthCases, '      *) choices="" ;;', '    esac ;;',
      '    *) choices="" ;;',
      '  esac',
      '  COMPREPLY=( $(compgen -W "$choices" -- "$current") )',
      '}',
      'complete -F _pdd_complete pdd',
      '',
    ].join('\n');
  }
  const fourthZshCases = [...maps.fourth].map(([key, values]) => `      ${key}) choices=(${quoteWords(values)}) ;;`).join('\n');
  const thirdZshCases = [...maps.third].map(([key, values]) => `      ${key}) choices=(${quoteWords(values)}) ;;`).join('\n');
  const secondZshCases = [...maps.second].map(([key, values]) => `      ${key}) choices=(${quoteWords(values)}) ;;`).join('\n');
  return [
    '#compdef pdd',
    '_pdd() {',
    '  local -a choices',
    '  case "${words[2]}:${words[CURRENT-1]}" in', zshValues, '  esac',
    '  case $CURRENT in',
    `    2) choices=(${quoteWords(maps.first)}) ;;`,
    '    3) case $words[2] in', secondZshCases, '      *) choices=() ;;', '    esac ;;',
    '    4) case "$words[2]:$words[3]" in', thirdZshCases, '      *) choices=() ;;', '    esac ;;',
    '    5) case "$words[2]:$words[3]:$words[4]" in', fourthZshCases, '      *) choices=() ;;', '    esac ;;',
    '    *) choices=() ;;',
    '  esac',
    '  _describe "PDD command" choices',
    '}',
    'compdef _pdd pdd',
    '',
  ].join('\n');
}
