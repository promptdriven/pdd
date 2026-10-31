// Generated from prompts/cli/completion.prompt.md (sha256: 3c13cb80f733ce37e4f60daaa0a87db37c3688d65956bb79c9c4c1bd80ef8aa2).
import { NAMES, PUBLIC_COMMAND_ROUTES } from './command-catalog.mjs';

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
  for (const route of PUBLIC_COMMAND_ROUTES) if (!route.prefix[0].startsWith('-')) add(second, 'help', route.prefix[0]);
  return { first: [...first].sort(), second, third, fourth };
}

const quoteWords = (values) => [...values].sort().join(' ');

// Read only the authoritative local catalog; names remain data, never shell source.
const definitionNames = `pdd workflow list --json 2>/dev/null | node -e 'let s="";process.stdin.on("data",x=>s+=x);process.stdin.on("end",()=>{try{const d=JSON.parse(s);process.stdout.write(d.workflows.map(x=>x.name).filter(n=>typeof n==="string"&&n.length<=64&&/^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/.test(n)).join(" "));}catch{}})'`;


export function renderCompletion(shell) {
  if (shell !== 'bash' && shell !== 'zsh') throw new TypeError('Choose bash or zsh.');
  const maps = candidateMaps();
  const valueChoices = new Map();
  for(const route of PUBLIC_COMMAND_ROUTES) for(const option of route.options) if(option.choices) valueChoices.set(`${route.prefix[0]}:${option.name}`,option.choices);
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
      `  if [[ $COMP_CWORD == 3 && \${COMP_WORDS[1]} == workflow && \${COMP_WORDS[2]} == ${NAMES.start} ]]; then`,
      `    choices="$(${definitionNames})"`,
      '    COMPREPLY=( $(compgen -W "$choices" -- "$current") ); return',
      '  fi',
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
    `  if [[ $CURRENT == 4 && $words[2] == workflow && $words[3] == ${NAMES.start} ]]; then`,
    `    local names="$(${definitionNames})"`,
    '    choices=(${=names}); _describe "PDD workflow" choices; return',
    '  fi',
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
