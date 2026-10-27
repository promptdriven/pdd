// Generated from prompts/cli/argument-parser.prompt.md (sha256: d85f17d23e6be9927dffbcb9660581910b8bccffd206f0e2ea3c023da0705fef).
import { validDecisionInput } from './workflow-decide.mjs';
import { PUBLIC_COMMAND_ROUTES } from './command-catalog.mjs';

export class CommandInputError extends Error {
  constructor(message) { super(message); this.name = 'CommandInputError'; this.exitCode = 2; }
}
const HELP_WORDS = ['--help', '-h', '-help'];
const fail = () => { throw new CommandInputError('Unsupported command or options in PDD Alpha. Run pdd --help for local authoring tools.'); };
const routes = [...PUBLIC_COMMAND_ROUTES].sort((a, b) => b.prefix.length - a.prefix.length);
const matches = (route, words) => route.prefix.every((token, index) => words[index] === token);
const findRoute = words => routes.find(route => matches(route, words));
const help = prefix => Object.freeze({ commandId: 'help', local: 'help', helpPrefix: Object.freeze([...prefix]) });
function helpFor(words) {
  if (!words.length) return help([]);
  const route = findRoute(words);
  if (route && route.prefix.length === words.length) return help(words);
  if (words.length === 1 && routes.some(route => route.prefix[0] === words[0])) return help(words);
  fail();
}
function parseRoute(route, words) {
  const options = Object.create(null), operands = []; let literal = false;
  for (let index = 0; index < words.length; index++) {
    const word = words[index];
    if (word === '--' && route.local === 'session' && !literal) { literal = true; continue; }
    if (!literal && word.startsWith('-')) {
      const option = route.options.find(option => option.name === word);
      if (!option || Object.hasOwn(options, word)) fail();
      if (option.kind === 'flag') options[word] = true;
      else {
        const value = words[++index];
        if (typeof value !== 'string' || value.startsWith('--') || option.choices && !option.choices.includes(value)) fail();
        options[word] = value;
      }
    } else operands.push(word);
  }
  const minimum = route.operands.filter(item => !item.optional).length;
  if (operands.length < minimum || !route.operands.at(-1)?.repeat && operands.length > route.operands.length) fail();
  for (let index = 0; index < operands.length; index++) {
    const type = route.operands[Math.min(index, route.operands.length - 1)].type;
    const word = operands[index];
    const valid = type === 'text' || type === 'workflow-name' && word.length<=64 && /^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/.test(word) || type === 'issue'
      && /^(?:#?[1-9][0-9]*|[A-Za-z0-9_.-]+#[1-9][0-9]*|[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+#[1-9][0-9]*|https:\/\/github\.com\/[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+\/issues\/[1-9][0-9]*\/?)$/.test(word)
      || type === 'run-ref' && (/^(?:#?[1-9][0-9]*|[A-Za-z0-9_.-]+#[1-9][0-9]*|[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+#[1-9][0-9]*|https:\/\/github\.com\/[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+\/issues\/[1-9][0-9]*\/?)$/.test(word) || /^[a-f0-9]{8,}$/i.test(word) || /^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/i.test(word))
      || type === 'uuid' && /^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/i.test(word)
      || type.startsWith('choice:') && type.slice(7).split(',').includes(word);
    if (!valid) fail();
  }
  if (route.local === 'workflow-decide' && (!/^[1-9][0-9]*$/.test(options['--expect-seq']??'')
    || !validDecisionInput({runId:operands[0],decisionId:options['--id'],decision:options['--decision'],
      expectStage:options['--expect-stage'],expectSeq:Number(options['--expect-seq']),text:options['--text'],via:options['--via'],phoneId:options['--phone'],approval:options['--approval']}))) fail();
  return Object.freeze({ commandId: route.id, local: route.local, ...(route.workflowName ? { workflowName: route.workflowName } : {}),
    operands: Object.freeze(operands), options: Object.freeze({ ...options }) });
}
export function parseArgv(argv) {
  if (!Array.isArray(argv) || argv.some(word => typeof word !== 'string' || word.includes('\0'))) fail();
  if (!argv.length || argv.length === 1 && HELP_WORDS.includes(argv[0])) return help([]);
  if (argv[0] === 'help') return helpFor(argv.slice(1));
  if (HELP_WORDS.includes(argv.at(-1)) && !(findRoute(argv)?.local === 'session' && argv.includes('--'))) {
    const words = argv.slice(0, -1), route = findRoute(words);
    if (!route || route.prefix.length === words.length) return helpFor(words);
    parseRoute(route, words.slice(route.prefix.length));
    return help(route.prefix);
  }
  const route = findRoute(argv);
  if (!route && !argv[0].startsWith('-') && !routes.some(candidate => candidate.prefix[0] === argv[0])) {
    const word = argv[0].replace(/[\x00-\x1f\x7f-\x9f]/g, ' ').slice(0, 64);
    throw new CommandInputError(`Unknown command "${word}". Run pdd --help to see the commands.`);
  }
  if (!route) fail();
  return parseRoute(route, argv.slice(route.prefix.length));
}
