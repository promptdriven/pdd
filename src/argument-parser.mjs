// Generated from prompts/cli/argument-parser.prompt.md (sha256: eb831df0588ac233776d18fb72d9e4b31f7693f0104dfebd3824e60f6e331c06).
import { PUBLIC_COMMAND_ROUTES } from './command-catalog.mjs';

export class CommandInputError extends Error {
  constructor(message) { super(message); this.name = 'CommandInputError'; this.exitCode = 2; }
}
const HELP_WORDS = ['--help', '-h', '-help'];
const fail = () => { throw new CommandInputError('Unsupported command or options in pdd. Run pdd --help for local authoring tools.'); };
const routes = [...PUBLIC_COMMAND_ROUTES].sort((a, b) => b.prefix.length - a.prefix.length);
const matches = (route, words) => route.prefix.every((token, index) => words[index] === token);
const findRoute = words => routes.find(route => matches(route, words));
const help = prefix => Object.freeze({ commandId: 'help', local: 'help', helpPrefix: Object.freeze([...prefix]) });
// Former words (`formerly`) parse with the route whose former words have no flag; `check --lint` names the lint route.
const isFlag = word => word.startsWith('-');
const FORMER = routes.filter(route => route.formerly).map(route => ({ route,
  words: route.formerly.filter(word => !isFlag(word)), flags: route.formerly.filter(isFlag) }));
const formerAt = words => FORMER.find(entry => !entry.flags.length && entry.words.every((word, index) => words[index] === word));
// A plan whose options hold every flag that another route of the same local always has works like that route (`test --lint` = `lint`).
const routeLike = (route, options) => routes.find(other => other !== route && other.local === route.local && other.implies
  ?.every(flag => options[flag] === true)) ?? route;
function withNotice(plan, base) {
  const route = plan.local === 'help' ? routes.find(item => item.prefix.join(' ') === plan.helpPrefix.join(' '))
    : routeLike(base.route, plan.options);
  const entry = FORMER.find(item => item.route === route && item.flags.length) ?? base;
  return Object.freeze({ ...plan, notice: `pdd ${entry.route.formerly.join(' ')} is now pdd ${entry.route.prefix.join(' ')}.` });
}
function helpFor(words) {
  if (!words.length) return help([]);
  const route = findRoute(words);
  if (route && route.prefix.length === words.length) return help(words);
  if (words.length === 1 && routes.some(route => route.prefix[0] === words[0])) return help(words);
  fail();
}
const optionValue = (option, value) => option.kind === 'integer'
  ? /^[1-9][0-9]{0,5}$/.test(value ?? '') && Number(value) >= option.min && Number(value) <= option.max
  : option.kind === 'uuid' ? /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(value ?? '')
  : option.kind === 'text' ? typeof value === 'string' && !!value.trim() : !!option.choices?.includes(value);
function parseRoute(route, words, allowHelp = false, typed = route.prefix) {
  const options = Object.create(null), operands = []; let literal = false, helpRequested = false;
  for (let index = 0; index < words.length; index++) {
    const word = words[index];
    if (allowHelp && !literal && index === words.length - 1 && HELP_WORDS.includes(word)) { helpRequested = true; continue; }
    if (word === '--' && route.operands.at(-1)?.type === 'text' && !literal) { literal = true; continue; }
    if (!literal && word.startsWith('-')) {
      const option = route.options.find(option => option.name === word);
      if (!option || Object.hasOwn(options, word)) fail();
      if (option.kind === 'flag') options[word] = true;
      else if (option.kind === 'optional-integer') {
        const next = words[index + 1];
        if (/^[0-9]+$/.test(next ?? '')) {
          if (Number(next) < option.min || Number(next) > option.max) fail();
          options[word] = words[++index];
        } else options[word] = String(option.default);
      }
      else {
        const value = words[++index];
        if (!optionValue(option, value)) fail();
        options[word] = value;
      }
    } else operands.push(word);
  }
  if (route.id === 'workflow.run' && /^[1-9][0-9]*$/.test(operands[0] ?? '')) {
    throw new CommandInputError(`Name the workflow: pdd ${typed.join(' ')} small-change ${operands[0]} (or bug, feature). See pdd workflow list.`);
  }
  const minimum = route.operands.filter(item => !item.optional).length;
  if (operands.length < minimum || !route.operands.at(-1)?.repeat && operands.length > route.operands.length) fail();
  for (let index = 0; index < operands.length; index++) {
    const type = route.operands[Math.min(index, route.operands.length - 1)].type;
    const word = operands[index];
    const valid = type === 'text' || type === 'workflow-name' && word.length<=64 && /^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/.test(word) || type === 'issue'
      && /^(?:[1-9][0-9]*|[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+#[1-9][0-9]*|https:\/\/github\.com\/[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+\/issues\/[1-9][0-9]*\/?)$/.test(word)
      || type === 'uuid' && /^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/i.test(word)
      || type.startsWith('choice:') && type.slice(7).split(',').includes(word);
    if (!valid) fail();
  }
  if (helpRequested) return help(routeLike(route, options).prefix);
  const implied = Object.fromEntries((route.implies ?? []).map(flag => [flag, true]));
  return Object.freeze({ commandId: route.id, local: route.local,
    operands: Object.freeze(operands), options: Object.freeze({ ...implied, ...options }) });
}
// A short form (`sim`) is the route's own words in fewer letters: rewrite it to the prefix, with no notice.
const SHORT = routes.filter(route => route.short);
const expandShort = (argv, at) => {
  const route = SHORT.find(item => item.short.every((word, index) => argv[at + index] === word));
  return route ? [...argv.slice(0, at), ...route.prefix, ...argv.slice(at + route.short.length)] : argv;
};
export function parseArgv(input) {
  if (!Array.isArray(input) || input.some(word => typeof word !== 'string' || word.includes('\0'))) fail();
  const direct = parseProgram(input);
  if (direct) return direct;
  const at = input[0] === 'help' ? 1 : 0, argv = expandShort(input, at), base = formerAt(argv.slice(at));
  if (!base) return parseWords(argv);
  // Rewrite the former words to the new words, then parse as usual; a refusal throws before any notice.
  const words = [...argv.slice(0, at), ...base.route.prefix, ...argv.slice(at + base.words.length)];
  return withNotice(parseWords(words, base.words), base);
}
function parseWords(argv, typed) {
  if (!argv.length || argv.length === 1 && HELP_WORDS.includes(argv[0])) return help([]);
  if (argv[0] === 'help') return helpFor(argv.slice(1));
  if (HELP_WORDS.includes(argv.at(-1)) && !(findRoute(argv)?.operands.at(-1)?.type === 'text' && argv.includes('--'))) {
    const words = argv.slice(0, -1), route = findRoute(words);
    if (!route || route.prefix.length === words.length) return helpFor(words);
    return parseRoute(route, argv.slice(route.prefix.length), true, typed);
  }
  const route = findRoute(argv);
  if (!route && !argv[0].startsWith('-') && !routes.some(candidate => candidate.prefix[0] === argv[0])) {
    const word = argv[0].replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').slice(0, 64);
    throw new CommandInputError(`Unknown command "${word}". Run pdd --help to see the commands.`);
  }
  if (!route) fail();
  return parseRoute(route, argv.slice(route.prefix.length), false, typed);
}

function parseProgram(words) {
  const options = {}, valueOptions = new Set(['--data', '--max-calls', '--read', '--port']);
  let i = 0;
  while (i < words.length && words[i].startsWith('-')) {
    const key = words[i];
    if (!['--reset','--no-cache','--json','--show-data','-q','--quiet', ...valueOptions].includes(key)) return null;
    if (Object.hasOwn(options,key)) fail();
    if (valueOptions.has(key)) { if (!words[i+1]) fail(); options[key] = words[++i]; }
    else options[key] = true;
    i++;
  }
  if (!words[i]?.endsWith('.prompt.md')) return null;
  if (options['--max-calls'] !== undefined && !/^(?:[1-9][0-9]{0,2}|1000)$/.test(options['--max-calls'])) fail();
  if (options['--port'] !== undefined && (!/^[0-9]+$/.test(options['--port']) || Number(options['--port']) < 1 || Number(options['--port']) > 65535)) fail();
  if (options['--read'] && !/^[a-f0-9-]{36}$/i.test(options['--read'])) fail();
  return Object.freeze({commandId:'prompt-run',local:'prompt-run',operands:Object.freeze(words.slice(i)),options:Object.freeze(options)});
}
