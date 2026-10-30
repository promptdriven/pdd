// Generated from prompts/cli/argument-parser.prompt.md (sha256: a9b2831a90851a8808cd82ba81d2a834bad3fc46368ac8fb888a04d26675fd22).
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
// A plan whose options hold every flag that another route of the same local always has works like that route (`test --lint` = `lint`).
const routeLike = (route, options) => routes.find(other => other !== route && other.local === route.local && other.implies
  ?.every(flag => options[flag] === true)) ?? route;
// A removed word (`check`, `try`) runs nothing: one line names the new command. A removed entry with a flag
// (`check --lint`) wins when that flag is one of the words after the command word.
const REMOVED = routes.filter(route => route.removed).map(route => ({ route,
  word: route.removed[0], flags: route.removed.slice(1) })).sort((a, b) => b.flags.length - a.flags.length);
function refuseRemoved(input) {
  const at = input[0] === 'help' ? 1 : 0, rest = input.slice(at + 1);
  const entry = REMOVED.find(item => item.word === input[at] && item.flags.every(flag => rest.includes(flag)));
  if (entry) throw new CommandInputError(`pdd ${entry.route.removed.join(' ')} was removed. Use pdd ${entry.route.prefix.join(' ')}.`);
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
function parseRoute(route, words, allowHelp = false) {
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
    throw new CommandInputError(`Name the workflow: pdd ${route.prefix.join(' ')} small-change ${operands[0]} (or bug, feature). See pdd workflow list.`);
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
// A quiet word (`sim`, `workflow start`) is rewritten to the prefix of its route, with nothing added.
const QUIET = routes.filter(route => route.quiet);
const expandQuiet = (argv, at) => {
  const route = QUIET.find(item => item.quiet.every((word, index) => argv[at + index] === word));
  return route ? [...argv.slice(0, at), ...route.prefix, ...argv.slice(at + route.quiet.length)] : argv;
};
export function parseArgv(input) {
  if (!Array.isArray(input)) fail();
  refuseRemoved(input);
  if (input.some(word => typeof word !== 'string' || word.includes('\0'))) fail();
  return parseWords(expandQuiet(input, input[0] === 'help' ? 1 : 0));
}
function parseWords(argv) {
  if (!argv.length || argv.length === 1 && HELP_WORDS.includes(argv[0])) return help([]);
  if (argv[0] === 'help') return helpFor(argv.slice(1));
  if (HELP_WORDS.includes(argv.at(-1)) && !(findRoute(argv)?.operands.at(-1)?.type === 'text' && argv.includes('--'))) {
    const words = argv.slice(0, -1), route = findRoute(words);
    if (!route || route.prefix.length === words.length) return helpFor(words);
    return parseRoute(route, argv.slice(route.prefix.length), true);
  }
  const route = findRoute(argv);
  if (!route && !argv[0].startsWith('-') && !routes.some(candidate => candidate.prefix[0] === argv[0])) {
    const word = argv[0].replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').slice(0, 64);
    throw new CommandInputError(`Unknown command "${word}". Run pdd --help to see the commands.`);
  }
  if (!route) fail();
  return parseRoute(route, argv.slice(route.prefix.length), false);
}
