// Prompt: prompts/cli/argument-parser.prompt.md

import { PUBLIC_COMMAND_ROUTES, REMOVED_COMMANDS } from './command-catalog.mjs';

export class CommandInputError extends Error {
  constructor(message) { super(message); this.name = 'CommandInputError'; this.exitCode = 2; }
}
const HELP_WORDS = ['--help', '-h', '-help'];
const fail = () => { throw new CommandInputError('Unsupported command or options in pdd. Run pdd --help for local authoring tools.'); };
const sanitizeToken = word => String(word ?? '').replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').slice(0, 64);
const failUnknownOption = (route, word) => {
  if (!route?.prefix?.length || route.prefix[0].startsWith('-')) fail();
  const cmd = `pdd ${route.prefix.join(' ')}`;
  throw new CommandInputError(`Unsupported command or options in pdd: unknown option "${sanitizeToken(word)}" for ${cmd}. Run ${cmd} --help.`);
};
const explicitRoutes = [...PUBLIC_COMMAND_ROUTES]
  .filter(route => route.prefix.length > 0)
  .sort((a, b) => b.prefix.length - a.prefix.length);
const directRoute = PUBLIC_COMMAND_ROUTES.find(route => route.id === 'try');
const DIRECT_TRAILING_OPTIONS = new Set([
  '--agent', '--tab', '--new', '--fresh',
  '--page', '--cli', '--shell', '--serve',
  '--allow-origins', '--trust-proxy', '--serve-token', '--serve-header',
  '--max-calls', '--no-open', '--stop', '--app-map', '--no-wait',
]);
const DIRECT_SESSION_CONTROL_OPTIONS = ['--stop', '--save-last', '--product'];
const matches = (route, words) => route.prefix.every((token, index) => words[index] === token);
const findRoute = words => explicitRoutes.find(route => matches(route, words));
const help = prefix => Object.freeze({ commandId: 'help', local: 'help', helpPrefix: Object.freeze([...prefix]) });
// A help topic (`help prompting`) is exactly two words; any word after the topic, also a help flag, refuses.
const TOPICS = PUBLIC_COMMAND_ROUTES.find(route => route.id === 'help')?.topics ?? [];
const topicHelp = words => words.length === 1 ? Object.freeze({ ...help([]), topic: words[0] }) : fail();
// A plan whose options hold every flag that another route always implies works like that route (`test --lint` = `lint`).
const routeLike = (route, options) => explicitRoutes.find(other => other !== route && other.implies?.length
  && other.implies.every(flag => options[flag] === true)) ?? route;
// A removed word runs nothing: one line names the replacement. A removed entry with a flag
// (`check --lint`) wins when that flag is one of the words after the command word.
const REMOVED = explicitRoutes.filter(route => route.removed).map(route => ({ route,
  word: route.removed[0], flags: route.removed.slice(1) })).sort((a, b) => b.flags.length - a.flags.length);
function refuseRemoved(input) {
  const at = input[0] === 'help' ? 1 : 0, rest = input.slice(at + 1);
  const entry = REMOVED.find(item => item.word === input[at] && item.flags.every(flag => rest.includes(flag)));
  if (entry) throw new CommandInputError(`pdd ${entry.route.removed.join(' ')} was removed. Use pdd ${entry.route.prefix.join(' ')}.`);
  const retired = REMOVED_COMMANDS.find(item => item.words.every((word, index) => input[at + index] === word));
  if (retired) throw new CommandInputError(retired.message);
}
function helpFor(words) {
  if (!words.length) return help([]);
  if (words.length === 1 && words[0] === '.') return help(['.']);
  const route = findRoute(words);
  if (route && route.prefix.length === words.length) return help(words);
  if (words.length === 1 && explicitRoutes.some(route => route.prefix[0] === words[0])) return help(words);
  fail();
}
const UUID_OPTION_RE = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
const BATCH_OPTION_RE = /^\d{8}-\d{6}-[a-z0-9]{4}$/;
const optionValue = (option, value) => option.kind === 'integer'
  ? /^(?:0|[1-9][0-9]{0,5})$/.test(value ?? '') && Number(value) >= option.min && Number(value) <= option.max
  : option.kind === 'uuid' ? UUID_OPTION_RE.test(value ?? '')
  : option.kind === 'uuid-or-batch' ? (UUID_OPTION_RE.test(value ?? '') || BATCH_OPTION_RE.test(value ?? ''))
  : option.kind === 'text' ? typeof value === 'string' && !!value.trim() : !!option.choices?.includes(value);

function consumeOption(route, options, words, index, { speculative = false } = {}) {
  const word = words[index];
  const bad = () => {
    if (speculative) return -1;
    fail();
  };
  const option = route.options.find(item => item.name === word);
  if (!option) return speculative ? -1 : failUnknownOption(route, word);
  if (Object.hasOwn(options, word)) return bad();
  if (option.kind === 'flag') {
    options[word] = true;
    return index;
  }
  if (option.kind === 'optional-integer') {
    const next = words[index + 1];
    if (/^[0-9]+$/.test(next ?? '')) {
      if (Number(next) < option.min || Number(next) > option.max) return bad();
      options[word] = words[++index];
    } else options[word] = String(option.default);
    return index;
  }
  if (option.kind === 'optional-text') {
    if (index + 1 < words.length && !words[index + 1].startsWith('-')) {
      const value = words[++index];
      if (!value.trim()) return bad();
      options[word] = value;
    } else options[word] = true;
    return index;
  }
  if (option.kind === 'text-list') {
    const values = [];
    while (index + 1 < words.length && !words[index + 1].startsWith('-')) {
      const value = words[++index];
      if (!value.trim()) return bad();
      values.push(value);
    }
    if (!values.length) return bad();
    options[word] = Object.freeze(values);
    return index;
  }
  const value = words[++index];
  if (!optionValue(option, value)) return bad();
  options[word] = value;
  return index;
}

function isDirectPromptTarget(word) {
  if (typeof word !== 'string' || !word || word.startsWith('-')) return false;
  const base = word.split(/[\\/]/).at(-1);
  return base.endsWith('.prompt.md') && base.slice(0, -'.prompt.md'.length).trim().length > 0;
}

function isDirectAppMapTarget(word) {
  if (typeof word !== 'string' || !word || word.startsWith('-')) return false;
  return word.split(/[\\/]/).at(-1) === 'app-map.json';
}

function parseDirectFile(file, tail, prefixOptions) {
  if (!tail.length) {
    return Object.freeze({
      commandId: directRoute.id,
      local: directRoute.local,
      operands: Object.freeze([file]),
      options: Object.freeze({ ...prefixOptions }),
    });
  }
  if (tail[0] === '--') {
    return Object.freeze({
      commandId: directRoute.id,
      local: directRoute.local,
      operands: Object.freeze([file, ...tail.slice(1)]),
      options: Object.freeze({ ...prefixOptions }),
    });
  }
  const trailing = Object.create(null);
  let allTrailing = true;
  for (let i = 0; i < tail.length; i++) {
    const word = tail[i];
    if (!word.startsWith('-') || !DIRECT_TRAILING_OPTIONS.has(word) || Object.hasOwn(prefixOptions, word) || Object.hasOwn(trailing, word)) {
      allTrailing = false;
      break;
    }
    const nextIdx = consumeOption(directRoute, trailing, tail, i, { speculative: true });
    if (nextIdx < 0) { allTrailing = false; break; }
    i = nextIdx;
  }
  if (allTrailing) {
    return Object.freeze({
      commandId: directRoute.id,
      local: directRoute.local,
      operands: Object.freeze([file]),
      options: Object.freeze({ ...prefixOptions, ...trailing }),
    });
  }
  return Object.freeze({
    commandId: directRoute.id,
    local: directRoute.local,
    operands: Object.freeze([file, ...tail]),
    options: Object.freeze({ ...prefixOptions }),
  });
}

function parseDirectTail(words, initialOptions, { maxOperands = 1 } = {}) {
  const options = Object.assign(Object.create(null), initialOptions);
  const operands = [];
  let literal = false;
  let helpRequested = false;
  for (let index = 0; index < words.length; index++) {
    const word = words[index];
    if (!literal && index === words.length - 1 && HELP_WORDS.includes(word)) {
      helpRequested = true;
      continue;
    }
    if (word === '--' && maxOperands > 0 && !literal) {
      literal = true;
      continue;
    }
    if (!literal && word.startsWith('-')) {
      index = consumeOption(directRoute, options, words, index);
    } else {
      operands.push(word);
    }
  }
  if (operands.length > maxOperands) fail();
  if (helpRequested) return help(['.']);
  return Object.freeze({
    commandId: directRoute.id,
    local: directRoute.local,
    operands: Object.freeze(operands),
    options: Object.freeze({ ...options }),
  });
}

function parseDirectLeadingOptions(argv, { resolveTarget } = {}) {
  if (!directRoute.options.some(option => option.name === argv[0])) fail();
  const prefixOptions = Object.create(null);
  let index = 0;
  while (index < argv.length && argv[index].startsWith('-')) {
    const word = argv[index];
    if (index === argv.length - 1 && HELP_WORDS.includes(word)) return help(['.']);
    if (word === '--') break;
    index = consumeOption(directRoute, prefixOptions, argv, index);
    index++;
  }
  if (index === argv.length) {
    return Object.freeze({
      commandId: directRoute.id,
      local: directRoute.local,
      operands: Object.freeze([]),
      options: Object.freeze({ ...prefixOptions }),
    });
  }
  const next = argv[index];
  const sessionControl = DIRECT_SESSION_CONTROL_OPTIONS.some(flag => Object.hasOwn(prefixOptions, flag));
  if (sessionControl) {
    return parseDirectTail(argv.slice(index), prefixOptions, { maxOperands: 1 });
  }
  if (next !== '--' && isDirectPromptTarget(next)) {
    return parseDirectFile(next, argv.slice(index + 1), prefixOptions);
  }
  if (next !== '--' && isDirectAppMapTarget(next)) {
    return parseDirectTail([next, ...argv.slice(index + 1)], prefixOptions, { maxOperands: 1 });
  }
  if (next !== '--' && next === '.') {
    return parseDirectTail(argv.slice(index + 1), prefixOptions, { maxOperands: 0 });
  }
  if (next !== '--' && typeof resolveTarget === 'function') {
    const resolved = resolveTarget(next);
    if (resolved?.kind === 'prompt' && typeof resolved.operand === 'string') {
      return parseDirectFile(resolved.operand, argv.slice(index + 1), prefixOptions);
    }
    if (resolved?.kind === 'story') {
      return parseDirectTail([resolved.operand ?? next, ...argv.slice(index + 1)], prefixOptions, { maxOperands: 1 });
    }
  }
  return parseDirectTail(argv.slice(index), prefixOptions, { maxOperands: 1 });
}

function parseRoute(route, words, allowHelp = false) {
  if (route.passthrough) {
    const forwarded = words[0] === '--' ? words.slice(1) : words;
    return Object.freeze({ commandId: route.id, local: route.local,
      operands: Object.freeze([...forwarded]), options: Object.freeze({}) });
  }
  const options = Object.create(null), operands = []; let literal = false, helpRequested = false;
  for (let index = 0; index < words.length; index++) {
    const word = words[index];
    if (allowHelp && !literal && index === words.length - 1 && HELP_WORDS.includes(word)) { helpRequested = true; continue; }
    if (word === '--' && route.operands.at(-1)?.type === 'text' && !literal) { literal = true; continue; }
    if (!literal && word.startsWith('-')) {
      index = consumeOption(route, options, words, index);
    } else operands.push(word);
  }
  const minimum = route.operands.filter(item => !item.optional).length;
  if (operands.length < minimum || !route.operands.at(-1)?.repeat && operands.length > route.operands.length) fail();
  for (let index = 0; index < operands.length; index++) {
    const type = route.operands[Math.min(index, route.operands.length - 1)].type;
    const word = operands[index];
    const valid = type === 'text' || type === 'issue'
      && /^(?:[1-9][0-9]*|[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+#[1-9][0-9]*|https:\/\/github\.com\/[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+\/issues\/[1-9][0-9]*\/?)$/.test(word)
      || type === 'uuid' && /^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/i.test(word)
      || type.startsWith('choice:') && type.slice(7).split(',').includes(word);
    if (!valid) fail();
  }
  const effective = routeLike(route, options);
  if (helpRequested) return help(effective.prefix);
  const implied = Object.fromEntries((route.implies ?? []).map(flag => [flag, true]));
  return Object.freeze({ commandId: route.id, local: effective.local,
    operands: Object.freeze(operands), options: Object.freeze({ ...implied, ...options }) });
}
// A quiet word (`-V`) is rewritten to the prefix of its route, with nothing added.
const QUIET = explicitRoutes.filter(route => route.quiet);
const expandQuiet = (argv, at) => {
  const route = QUIET.find(item => item.quiet.every((word, index) => argv[at + index] === word));
  return route ? [...argv.slice(0, at), ...route.prefix, ...argv.slice(at + route.quiet.length)] : argv;
};
export function parseArgv(input, { resolveTarget } = {}) {
  if (!Array.isArray(input)) fail();
  refuseRemoved(input);
  if (input.some(word => typeof word !== 'string' || word.includes('\0'))) fail();
  return parseWords(expandQuiet(input, input[0] === 'help' ? 1 : 0), { resolveTarget });
}
function parseWords(argv, { resolveTarget } = {}) {
  if (!argv.length || argv.length === 1 && HELP_WORDS.includes(argv[0])) return help([]);
  if (argv[0] === 'help') return TOPICS.includes(argv[1]) ? topicHelp(argv.slice(1)) : helpFor(argv.slice(1));
  const matchedRoute = findRoute(argv);
  if (matchedRoute?.passthrough) {
    if (argv.length === matchedRoute.prefix.length + 1 && HELP_WORDS.includes(argv.at(-1))) return help(matchedRoute.prefix);
    return parseRoute(matchedRoute, argv.slice(matchedRoute.prefix.length), false);
  }
  if (matchedRoute || explicitRoutes.some(candidate => candidate.prefix[0] === argv[0])) {
    if (HELP_WORDS.includes(argv.at(-1)) && !(matchedRoute?.operands.at(-1)?.type === 'text' && argv.includes('--'))) {
      const words = argv.slice(0, -1), route = findRoute(words);
      if (!route || route.prefix.length === words.length) return helpFor(words);
      return parseRoute(route, argv.slice(route.prefix.length), true);
    }
    if (!matchedRoute) fail();
    return parseRoute(matchedRoute, argv.slice(matchedRoute.prefix.length), false);
  }
  if (directRoute) {
    if (isDirectPromptTarget(argv[0])) {
      return parseDirectFile(argv[0], argv.slice(1), {});
    }
    if (isDirectAppMapTarget(argv[0])) {
      return parseDirectTail(argv, {}, { maxOperands: 1 });
    }
    if (argv[0] === '.') {
      return parseDirectTail(argv.slice(1), {}, { maxOperands: 0 });
    }
    if (argv[0].startsWith('-')) {
      return parseDirectLeadingOptions(argv, { resolveTarget });
    }
    if (typeof resolveTarget === 'function') {
      const resolved = resolveTarget(argv[0]);
      if (resolved?.kind === 'prompt' && typeof resolved.operand === 'string') {
        return parseDirectFile(resolved.operand, argv.slice(1), {});
      }
      if (resolved?.kind === 'story') {
        return parseDirectTail([resolved.operand ?? argv[0], ...argv.slice(1)], {}, { maxOperands: 1 });
      }
    }
  }
  if (HELP_WORDS.includes(argv.at(-1))) fail();
  if (!argv[0].startsWith('-')) {
    const word = sanitizeToken(argv[0]);
    throw new CommandInputError(`Unknown command "${word}". Run pdd --help to see the commands.`);
  }
  fail();
}
