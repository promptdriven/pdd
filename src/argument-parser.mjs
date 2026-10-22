import { PUBLIC_COMMAND_IDS, PUBLIC_COMMAND_ROUTES } from './command-catalog.mjs';

const idSet = new Set(PUBLIC_COMMAND_IDS);
const routesBySpecificity = [...PUBLIC_COMMAND_ROUTES].sort((left, right) => right.prefix.length - left.prefix.length);

export class CommandInputError extends Error {
  constructor(message) {
    super(message);
    this.name = 'CommandInputError';
    this.exitCode = 2;
  }
}

function fail(message = 'Check the command and options with pdd --help.') {
  throw new CommandInputError(message);
}

function noNul(value) {
  return typeof value === 'string' && !value.includes('\u0000');
}

function plainText(value) {
  return noNul(value) && value.length > 0;
}

function validType(value, type) {
  if (!plainText(value)) return false;
  if (type.startsWith('choice:')) return type.slice(7).split(',').includes(value);
  switch (type) {
    case 'text': return true;
    case 'id': return /^[A-Za-z0-9][A-Za-z0-9_.:@/-]{0,159}$/.test(value);
    case 'slug': return /^[a-z0-9][a-z0-9._-]{0,63}$/.test(value);
    case 'label': return /^[A-Za-z0-9][A-Za-z0-9_. -]*$/.test(value);
    case 'branch': return /^[A-Za-z0-9][A-Za-z0-9._/-]*$/.test(value);
    case 'positive-int': return /^[1-9]\d{0,8}$/.test(value);
    case 'repository': return /^[A-Za-z0-9][A-Za-z0-9_.-]{0,99}(?:\/[A-Za-z0-9][A-Za-z0-9_.-]{0,99})?$/.test(value);
    case 'project': return value === '.' || validType(value, 'repository') || validType(value, 'path');
    case 'issue-ref': return /^[A-Za-z0-9][A-Za-z0-9_.:/#-]*$/.test(value);
    case 'path': return !value.startsWith('--');
    case 'absolute-path': return (value.startsWith('/') || /^[A-Za-z]:[\\/]/.test(value)) && !value.startsWith('--');
    case 'json':
      try { JSON.parse(value); return true; } catch { return false; }
    case 'json-or-path':
      if (value.startsWith('{') || value.startsWith('[')) {
        try { JSON.parse(value); return true; } catch { return false; }
      }
      return validType(value, 'path');
    case 'stage': return /^[A-Za-z0-9][A-Za-z0-9_-]{0,63}(?::[A-Za-z0-9][A-Za-z0-9_-]{0,63})?$/.test(value);
    case 'stages': return value.split(',').every((item) => validType(item, 'stage'));
    case 'wait-state': return ['needs-you', 'question', 'solution', 'story', 'merge', 'ended'].includes(value)
      || /^stage:[A-Za-z0-9][A-Za-z0-9_-]{0,63}$/.test(value);
    default: return false;
  }
}

function routeMatches(route, tokens) {
  return route.prefix.length <= tokens.length && route.prefix.every((token, index) => tokens[index] === token);
}

function findRoute(tokens) {
  return routesBySpecificity.find((route) => routeMatches(route, tokens));
}

function appendOption(argv, option, parsedValue) {
  argv.push(option.name);
  if (option.kind === 'value') argv.push(parsedValue);
}

function validateCombinations(route, operands, options) {
  switch (route.validate) {
    case 'session-make-it':
      if ((options['--request'] === undefined) === (options['--resume'] === undefined)) fail('Choose exactly one of --request or --resume.');
      break;
    case 'agent-interrupt':
      if (options['--generation'] === undefined || options['--turn'] === undefined) fail('Use --generation and --turn from the current session.');
      break;
    case 'agent-list-models':
      if (options['--list-models'] && (operands.length || ['--project', '--model', '--effort'].some((name) => options[name] !== undefined)))
        fail('--list-models takes no text, project, model or effort.');
      break;
    case 'agent-request-action':
      if (options['--generation'] === undefined || options['--request'] === undefined) fail('Use --request and --generation from the current session.');
      break;
    case 'workflow-new':
      if (options['--from'] !== undefined && options['--describe'] !== undefined) fail('Choose --from or --describe, not both.');
      break;
    case 'runtime-request':
      if (options['--request'] !== undefined && (operands.length > 0 || Object.keys(options).some((key) => !['--request', '--json'].includes(key))))
        fail('A saved request can be read with --request and optional --json only.');
      if (route.id === 'replay' && options['--request'] === undefined && operands.length !== 1)
        fail('Give one saved check or use --request to read an existing replay.');
      break;
    case 'runtime':
      if (options['--request'] !== undefined) {
        if (operands.length) fail('Use --request by itself to read an existing Runtime operation.');
      } else if (operands.length !== 1) {
        fail('Choose one supported Runtime operation or use --request to read an existing operation.');
      }
      break;
    case 'call':
      if (options['--request'] !== undefined) {
        if (operands.length || options['--input'] !== undefined || options['--session'] !== undefined) fail('Use --request by itself to read a saved call.');
      } else if (operands.length !== 2 || options['--input'] === undefined) fail('Give a prompt, operation, and valid JSON with --input.');
      break;
    case 'tests':
      if (options['--request'] !== undefined) {
        if (operands.length || options['--story'] !== undefined) fail('Use --request by itself to read a saved test draft.');
      } else if (operands.length !== 1 || operands[0] !== 'draft' || options['--story'] === undefined) fail('Use tests draft --story text.');
      break;
    case 'try': {
      const has = (name) => options[name] !== undefined;
      if (operands.length) {
        if (operands.length !== 1 || !has('--input') || has('--run') || has('--terminal') || has('--session') || has('--command') || has('--request'))
          fail('Use a prompt path with --input and optional --repeat.');
      } else if (has('--run')) {
        if (has('--session') || has('--command') || has('--request') || has('--input') || has('--repeat')) fail('Use --run by itself, with optional --terminal.');
      } else if (has('--session')) {
        if (has('--input') || has('--repeat') || has('--run') || has('--command') && has('--request')) fail('Use --session with either --command or --request.');
      } else if (has('--terminal')) {
        if (has('--input') || has('--repeat') || has('--request') || has('--command')) fail('Use --terminal with an optional session and command.');
      } else if (has('--command')) fail('--command needs --session or --terminal.');
      else if (has('--request')) break;
      else if (has('--input') || has('--repeat')) fail('--input and --repeat need a prompt path.');
      break;
    }
    default:
      break;
  }
}

function parseRoute(route, args) {
  const optionSpecs = new Map(route.options.map((option) => [option.name, option]));
  const operands = [];
  const options = Object.create(null);
  const optionOrder = [];

  for (let index = 0; index < args.length; index += 1) {
    const token = args[index];
    if (token.startsWith('-')) {
      const option = optionSpecs.get(token);
      if (!option) fail('Unknown option. Run pdd --help.');
      if (options[token] !== undefined && !option.repeat) fail(`${token} may be used only once.`);
      if (option.kind === 'flag') {
        options[token] = true;
        optionOrder.push({ option, value: true });
        continue;
      }
      const value = args[index + 1];
      if (value === undefined || value.startsWith('--') || !validType(value, option.type)) fail(`${token} needs a valid ${option.type.replace(/^choice:/, 'choice ')} value.`);
      index += 1;
      if (option.repeat) (options[token] ??= []).push(value);
      else options[token] = value;
      optionOrder.push({ option, value });
      continue;
    }
    operands.push(token);
  }

  let minimum = 0;
  for (const item of route.operands) {
    if (item.optional) break;
    minimum += 1;
    if (item.repeat) break;
  }
  const repeated = route.operands.at(-1)?.repeat === true;
  const maximum = repeated ? Number.POSITIVE_INFINITY : route.operands.length;
  if (operands.length < minimum || operands.length > maximum) fail(`Use: ${route.forms[0]?.form ?? `pdd ${route.prefix.join(' ')}`}`);

  for (let index = 0; index < operands.length; index += 1) {
    const item = route.operands[Math.min(index, route.operands.length - 1)];
    if (!item || !validType(operands[index], item.type)) fail(`Give a valid ${item?.name ?? 'command argument'}.`);
  }

  validateCombinations(route, operands, options);
  if (!idSet.has(route.id)) fail('This command is not available in this PDD build.');

  const hostArgv = [...route.prefix, ...operands];
  for (const { option, value } of optionOrder) appendOption(hostArgv, option, value);
  return Object.freeze({
    commandId: route.id,
    local: route.local,
    host: route.host === true,
    operands: Object.freeze([...operands]),
    options: Object.freeze({ ...options }),
    hostArgv: Object.freeze(hostArgv),
  });
}

function localHelp(tokens) {
  if (!tokens.length) return Object.freeze({ commandId: 'help', local: 'help', hostArgv: Object.freeze([]) });
  const exactRoute = findRoute(tokens);
  if (exactRoute && exactRoute.prefix.length === tokens.length) return Object.freeze({
    commandId: 'help', local: 'help', helpPrefix: Object.freeze([...tokens]), hostArgv: Object.freeze([]),
  });
  const knownGroup = PUBLIC_COMMAND_ROUTES.some((route) => route.prefix[0] === tokens[0]);
  if (knownGroup && tokens.length === 1) return Object.freeze({
    commandId: 'help', local: 'help', helpPrefix: Object.freeze([...tokens]), hostArgv: Object.freeze([]),
  });
  fail('Unknown or unsupported PDD command. Run pdd --help.');
}

export function parseArgv(argv) {
  if (!Array.isArray(argv) || argv.some((token) => typeof token !== 'string' || !noNul(token)))
    fail('Arguments may not contain NUL characters.');
  if (argv.length === 1 && (argv[0] === '--help' || argv[0] === '-h')) return localHelp([]);
  if (argv.length === 1 && argv[0] === '--version') return Object.freeze({ commandId: 'version', local: 'version', hostArgv: Object.freeze([]) });
  if (!argv.length) return localHelp([]);
  if (argv.at(-1) === '--help' || argv.at(-1) === '-h') {
    const beforeHelp = argv.slice(0, -1);
    const beforeRoute = findRoute(beforeHelp);
    const preceding = beforeHelp.at(-1);
    const consumesHelpAsValue = beforeRoute?.options.some((option) => option.name === preceding && option.kind === 'value');
    if (!consumesHelpAsValue) return localHelp(beforeHelp);
  }

  const route = findRoute(argv);
  if (!route) fail('Unknown or unsupported PDD command. Run pdd --help.');
  return parseRoute(route, argv.slice(route.prefix.length));
}
