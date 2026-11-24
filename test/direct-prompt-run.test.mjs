import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { CommandInputError, parseArgv } from '../src/argument-parser.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { runJobs, runTry } from '../src/runtime-seam.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const BIN = join(ROOT, 'bin/pdd.mjs');

function makeTempRepo(t, files = {}) {
  const base = mkdtempSync(join(tmpdir(), 'pdd-direct-run-'));
  const repo = join(base, 'repo');
  const home = join(base, 'home');
  const state = join(base, 'state');
  mkdirSync(repo, { recursive: true });
  mkdirSync(home, { recursive: true });
  mkdirSync(state, { recursive: true });
  t.after(() => rmSync(base, { recursive: true, force: true }));
  for (const [rel, content] of Object.entries(files)) {
    const full = join(repo, rel);
    mkdirSync(dirname(full), { recursive: true });
    writeFileSync(full, typeof content === 'string' ? content : `${JSON.stringify(content, null, 2)}\n`);
  }
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '--allow-empty', '-m', 'init'], { cwd: repo });
  return { base, repo, home, state };
}

function runBin(args, { cwd, home, state, extraEnv = {}, preload } = {}) {
  const nodeArgs = preload ? ['--import', preload, BIN, ...args] : [BIN, ...args];
  return spawnSync(process.execPath, nodeArgs, {
    cwd,
    env: {
      PATH: '/usr/bin:/bin',
      HOME: home,
      PDD_STATE_DIR: state,
      PDD_RUNTIME_URL: 'http://127.0.0.1:1',
      PDD_NO_OPEN: '1',
      ...extraEnv,
    },
    encoding: 'utf8',
    timeout: 15000,
  });
}

test('direct file execution: Python-style arg boundary, prefix options, trailing interactive flags, and -- passthrough', () => {
  // Bare .prompt.md and app-map.json targets
  assert.deepEqual(parseArgv(['prompts/app.prompt.md']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md'], options: {},
  });
  assert.deepEqual(parseArgv(['app-map.json']), {
    commandId: 'try', local: 'runtime-try', operands: ['app-map.json'], options: {},
  });
  assert.deepEqual(parseArgv(['app/app-map.json']), {
    commandId: 'try', local: 'runtime-try', operands: ['app/app-map.json'], options: {},
  });

  // Verbatim passthrough for program args after .prompt.md (including --help, unknown flags, empty strings)
  assert.deepEqual(parseArgv(['prompts/todo.prompt.md', 'add', 'Buy milk']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/todo.prompt.md', 'add', 'Buy milk'], options: {},
  });
  assert.deepEqual(parseArgv(['prompts/calc.prompt.md', 'add', '--a', '1', '--b', '2']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/calc.prompt.md', 'add', '--a', '1', '--b', '2'], options: {},
  });
  assert.deepEqual(parseArgv(['prompts/calc.prompt.md', '--help']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/calc.prompt.md', '--help'], options: {},
  });
  assert.deepEqual(parseArgv(['prompts/calc.prompt.md', '-h']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/calc.prompt.md', '-h'], options: {},
  });
  assert.deepEqual(parseArgv(['prompts/echo.prompt.md', '']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/echo.prompt.md', ''], options: {},
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--', '--page', '--fresh']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md', '--page', '--fresh'], options: {},
  });

  // Prefix options before the prompt file belong to pdd; trailing args still pass verbatim
  assert.deepEqual(parseArgv(['--fresh', 'prompts/todo.prompt.md', 'add', 'Buy milk']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/todo.prompt.md', 'add', 'Buy milk'], options: { '--fresh': true },
  });
  assert.deepEqual(parseArgv(['--data', 'seed.json', '-q', 'prompts/todo.prompt.md', 'list']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/todo.prompt.md', 'list'], options: { '--data': 'seed.json', '-q': true },
  });
  assert.deepEqual(parseArgv(['--show-data', '--quiet', 'prompts/todo.prompt.md']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/todo.prompt.md'], options: { '--show-data': true, '--quiet': true },
  });
  assert.deepEqual(parseArgv(['--fresh', 'prompts/calc.prompt.md', '--help']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/calc.prompt.md', '--help'], options: { '--fresh': true },
  });

  // Trailing PDD interactive flags work when EVERY trailing token is a valid interactive flag
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--page', '--new', '--fresh']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md'], options: { '--page': true, '--new': true, '--fresh': true },
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--serve', '8080']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md'], options: { '--serve': '8080' },
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--serve']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md'], options: { '--serve': '8080' },
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--cli', '--shell']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md'], options: { '--cli': true, '--shell': true },
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--tab', 'screen', '--max-calls', '50', '--no-open', '--no-wait', '--app-map', 'app/custom.json', '--agent', 'Codex (a)']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md'],
    options: { '--tab': 'screen', '--max-calls': '50', '--no-open': true, '--no-wait': true, '--app-map': 'app/custom.json', '--agent': 'Codex (a)' },
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--stop']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md'], options: { '--stop': true },
  });

  // Ambiguous or non-interactive trailing flags fall back cleanly to verbatim program args
  assert.deepEqual(parseArgv(['prompts/fmt.prompt.md', '--tab', '4']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/fmt.prompt.md', '--tab', '4'], options: {},
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--page', 'extra']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md', '--page', 'extra'], options: {},
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '--data', 'seed.json']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md', '--data', 'seed.json'], options: {},
  });
  assert.deepEqual(parseArgv(['prompts/app.prompt.md', '-q']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md', '-q'], options: {},
  });
  assert.deepEqual(parseArgv(['--page', 'prompts/app.prompt.md', '--page']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/app.prompt.md', '--page'], options: { '--page': true },
  });
  // Flag-like tokens and blank stems are never direct file targets (Finding #3)
  for (const badFile of ['--foo.prompt.md', '-x.prompt.md', '-/app-map.json', '   .prompt.md', '.prompt.md']) {
    assert.throws(() => parseArgv([badFile]), CommandInputError, `must reject ${badFile}`);
  }

  // app-map.json parses strictly (no verbatim passthrough args; --help yields focused help) (Finding #5)
  assert.deepEqual(parseArgv(['app-map.json', '--help']), { commandId: 'help', local: 'help', helpPrefix: ['.'] });
  assert.deepEqual(parseArgv(['app/app-map.json', '--serve', '8080', '--fresh']), {
    commandId: 'try', local: 'runtime-try', operands: ['app/app-map.json'], options: { '--serve': '8080', '--fresh': true },
  });
  assert.throws(() => parseArgv(['app-map.json', 'foo', 'bar']), CommandInputError);

  // Session-control flags (--stop, --save-last, --product) never rewrite stems to .prompt.md or swallow --help (Finding #1)
  const resolveTarget = word => word === 'todo'
    ? { kind: 'prompt', operand: 'prompts/todo.prompt.md' }
    : word === 'my-story' ? { kind: 'story', operand: 'my-story' } : null;
  assert.deepEqual(parseArgv(['--stop', 'todo'], { resolveTarget }), {
    commandId: 'try', local: 'runtime-try', operands: ['todo'], options: { '--stop': true },
  });
  assert.deepEqual(parseArgv(['--stop', 'todo', '--help'], { resolveTarget }), {
    commandId: 'help', local: 'help', helpPrefix: ['.'],
  });
  assert.deepEqual(parseArgv(['--stop', 'prompts/todo.prompt.md', '--help'], { resolveTarget }), {
    commandId: 'help', local: 'help', helpPrefix: ['.'],
  });
  assert.deepEqual(parseArgv(['--save-last', 'todo'], { resolveTarget }), {
    commandId: 'try', local: 'runtime-try', operands: ['todo'], options: { '--save-last': true },
  });

  // Trailing session-control flags (--parts, --product, --save-last) pass verbatim to .prompt.md programs
  assert.deepEqual(parseArgv(['prompts/todo.prompt.md', '--parts', 'a']), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/todo.prompt.md', '--parts', 'a'], options: {},
  });
});

test('whole-project ., leading interpreter options, explicit subcommand priority, and error refusals', () => {
  // Whole-project `.` normalizes to operands: []
  assert.deepEqual(parseArgv(['.']), {
    commandId: 'try', local: 'runtime-try', operands: [], options: {},
  });
  assert.deepEqual(parseArgv(['.', '--serve', '8080']), {
    commandId: 'try', local: 'runtime-try', operands: [], options: { '--serve': '8080' },
  });
  assert.deepEqual(parseArgv(['--fresh', '.']), {
    commandId: 'try', local: 'runtime-try', operands: [], options: { '--fresh': true },
  });

  // Focused direct interpreter help
  for (const argv of [['.', '--help'], ['.', '-h'], ['help', '.'], ['--product', '--help'], ['--stop', '--help'], ['--serve', '8080', '--help']]) {
    assert.deepEqual(parseArgv(argv), { commandId: 'help', local: 'help', helpPrefix: ['.'] }, argv.join(' '));
  }

  // Leading direct interpreter flags without a file
  assert.deepEqual(parseArgv(['--product', '--parts', 'phone,server', '--journey', 'J1', '--max-calls', '30']), {
    commandId: 'try', local: 'runtime-try', operands: [],
    options: { '--product': true, '--parts': 'phone,server', '--journey': 'J1', '--max-calls': '30' },
  });
  assert.deepEqual(parseArgv(['--stop']), {
    commandId: 'try', local: 'runtime-try', operands: [], options: { '--stop': true },
  });
  assert.deepEqual(parseArgv(['--stop', 'my-story']), {
    commandId: 'try', local: 'runtime-try', operands: ['my-story'], options: { '--stop': true },
  });
  assert.deepEqual(parseArgv(['--save-last']), {
    commandId: 'try', local: 'runtime-try', operands: [], options: { '--save-last': true },
  });
  assert.deepEqual(parseArgv(['--save-last', 'my-story']), {
    commandId: 'try', local: 'runtime-try', operands: ['my-story'], options: { '--save-last': true },
  });

  // Pure injected resolveTarget handles both Story slugs and prompt stems (including after prefix options)
  const resolveTarget = word => word === 'todo'
    ? { kind: 'prompt', operand: 'prompts/todo.prompt.md' }
    : word === 'my-story' ? { kind: 'story', operand: 'my-story' } : null;
  assert.deepEqual(parseArgv(['todo', 'add', 'Buy milk'], { resolveTarget }), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/todo.prompt.md', 'add', 'Buy milk'], options: {},
  });
  assert.deepEqual(parseArgv(['--fresh', 'todo', 'add', 'Buy milk'], { resolveTarget }), {
    commandId: 'try', local: 'runtime-try', operands: ['prompts/todo.prompt.md', 'add', 'Buy milk'], options: { '--fresh': true },
  });
  assert.deepEqual(parseArgv(['my-story', '--serve', '8080'], { resolveTarget }), {
    commandId: 'try', local: 'runtime-try', operands: ['my-story'], options: { '--serve': '8080' },
  });

  // Explicit subcommands always route FIRST
  assert.equal(parseArgv(['test', 'prompts/app.prompt.md']).commandId, 'check');
  assert.equal(parseArgv(['approve', 'prompts/app.prompt.md']).commandId, 'approve');
  assert.equal(parseArgv(['owner', 'prompts/app.prompt.md']).commandId, 'owner');
  assert.equal(parseArgv(['lint', 'prompts/app.prompt.md']).commandId, 'lint');
  assert.equal(parseArgv(['--version']).commandId, 'version');
  assert.equal(parseArgv(['-V']).commandId, 'version');
  assert.equal(parseArgv(['-VV']).commandId, 'version.detailed');

  // Removed commands & typos refuse cleanly with exit 2
  for (const [argv, expected] of [
    [['simulate'], 'pdd simulate was removed. Run pdd <PROMPT.md|STORY> instead.'],
    [['simulate', 'prompts/app.prompt.md'], 'pdd simulate was removed. Run pdd <PROMPT.md|STORY> instead.'],
    [['sim'], 'pdd sim was removed. Run pdd <PROMPT.md|STORY> instead.'],
    [['sim', 'my-story'], 'pdd sim was removed. Run pdd <PROMPT.md|STORY> instead.'],
    [['try'], 'pdd try was removed. Run pdd <PROMPT.md|STORY> instead.'],
    [['help', 'sim'], 'pdd sim was removed. Run pdd <PROMPT.md|STORY> instead.'],
    [['help', 'simulate'], 'pdd simulate was removed. Run pdd <PROMPT.md|STORY> instead.'],
    [['statis'], 'Unknown command "statis". Run pdd --help to see the commands.'],
    [['.prompt.md'], 'Unknown command ".prompt.md". Run pdd --help to see the commands.'],
  ]) {
    assert.throws(() => parseArgv(argv, { resolveTarget }), err => err instanceof CommandInputError && err.exitCode === 2 && err.message === expected, argv.join(' '));
  }
  for (const invalid of [['--no-such-flag'], ['--serve', '70000'], ['--tab', 'phone'], ['--fresh=1'], ['.', 'extra'], ['statis', '--help']]) {
    assert.throws(() => parseArgv(invalid, { resolveTarget }), CommandInputError, invalid.join(' '));
  }
});

test('E2E subprocess: bare pdd never imports runtime-seam, local Stories/prompt stems resolve without breaking typos, and typed prompt --help executes directly', t => {
  const calcPrompt = [
    '# Calc',
    '',
    'Simple calculator.',
    '',
    '<details><summary>Runtime interface</summary>',
    '',
    '```json',
    JSON.stringify({
      status: 'draft',
      prose_sha256: '',
      entries: [{
        operation: 'add',
        input_schema: {
          type: 'object',
          properties: {
            a: { type: 'number', description: 'First number' },
            b: { type: 'number', description: 'Second number' },
          },
          required: ['a', 'b'],
          additionalProperties: false,
        },
        result_schema: { type: 'object', properties: { sum: { type: 'number' } }, required: ['sum'], additionalProperties: false },
        errors: [],
      }],
      calls: [],
      resources: [],
      limits: { max_steps: 4, max_model_calls: 2 },
      conventions: [],
    }, null, 2),
    '```',
    '</details>',
    '',
    '## Dependencies',
    '',
    'None.',
    '',
  ].join('\n');

  const todoPrompt = [
    '# Todo CLI',
    '',
    'Command-line todo list program.',
    '',
    '<details><summary>Runtime interface</summary>',
    '',
    '```json',
    JSON.stringify({
      status: 'draft',
      prose_sha256: '',
      entries: [{
        operation: 'main',
        input_schema: {
          type: 'object',
          title: 'CLI todo',
          properties: {
            argv: { type: 'array', items: { type: 'string' } },
          },
          required: ['argv'],
          additionalProperties: false,
        },
        result_schema: {
          type: 'object',
          properties: {
            stdout: { type: 'string' },
            stderr: { type: 'string' },
            exit_code: { type: 'integer' },
          },
          required: ['stdout', 'stderr', 'exit_code'],
          additionalProperties: false,
        },
        errors: [],
      }],
      calls: [],
      resources: [],
      limits: { max_steps: 4, max_model_calls: 2 },
      conventions: [
        { path: '/entries/0/input_schema', convention: 'cli' },
        { path: '/entries/0/result_schema', convention: 'cli' },
      ],
    }, null, 2),
    '```',
    '</details>',
    '',
    '## Dependencies',
    '',
    'None.',
    '',
  ].join('\n');

  const fx = makeTempRepo(t, {
    'prompts/calc.prompt.md': calcPrompt,
    'prompts/todo.prompt.md': todoPrompt,
    'prompts/a/dup.prompt.md': '# Dup A\n\n## Dependencies\n\nNone.\n',
    'prompts/b/dup.prompt.md': '# Dup B\n\n## Dependencies\n\nNone.\n',
    'user_stories/my-story.md': '# My Story\n\nAs a user, I want to add numbers.\n\n## Acceptance criteria\n\n1. Adds numbers.\n',
    'tests/my-story.json': {
      entry_path: 'prompts/calc.prompt.md',
      steps: [{ id: 's1', op: 'add', input: { a: 1, b: 2 }, checks: { '1': [['result', '/sum', '=', 3]] } }],
    },
    'sub/README.md': 'subdir\n',
  });

  // 1. Bare `pdd` never imports runtime-seam.mjs and matches `pdd --help` byte-for-byte
  const guardHook = `import { registerHooks } from 'node:module'; registerHooks({ resolve(s, c, n) { const r = n(s, c); if (r.url && r.url.includes('runtime-seam')) throw new Error('FORBIDDEN_RUNTIME_SEAM_IMPORT'); return r; } });`;
  const preload = `data:text/javascript,${encodeURIComponent(guardHook)}`;
  const bare = runBin([], { cwd: fx.repo, home: fx.home, state: fx.state, preload });
  const helpFlag = runBin(['--help'], { cwd: fx.repo, home: fx.home, state: fx.state, preload });
  assert.equal(bare.status, 0, bare.stderr);
  assert.equal(bare.stderr, '');
  assert.equal(bare.stdout, helpFlag.stdout);
  assert.doesNotMatch(bare.stdout, /\b(?:sim|simulate|simulator)\b/i);

  // 2. Typo & ambiguous prompt stem both return Unknown command (exit 2)
  const typo = runBin(['statis'], { cwd: fx.repo, home: fx.home, state: fx.state });
  assert.equal(typo.status, 2);
  assert.equal(typo.stdout, '');
  assert.equal(typo.stderr, 'Unknown command "statis". Run pdd --help to see the commands.\n');

  const ambiguous = runBin(['dup'], { cwd: fx.repo, home: fx.home, state: fx.state });
  assert.equal(ambiguous.status, 2);
  assert.equal(ambiguous.stderr, 'Unknown command "dup". Run pdd --help to see the commands.\n');

  // 3. Direct Story slug, Story path, and test path route to Prompt Interpreter (including repo-relative paths from subdir!)
  for (const [cwd, args] of [
    [fx.repo, ['my-story', '--stop']],
    [fx.repo, ['user_stories/my-story.md', '--stop']],
    [fx.repo, ['tests/my-story.json', '--stop']],
    [join(fx.repo, 'sub'), ['user_stories/my-story.md', '--stop']],
    [join(fx.repo, 'sub'), ['tests/my-story.json', '--stop']],
  ]) {
    const res = runBin(args, { cwd, home: fx.home, state: fx.state });
    assert.equal(res.status, 2, `${args.join(' ')}: ${res.stderr}`);
    assert.doesNotMatch(res.stderr, /Unknown command/);
    assert.match(res.stderr, /No open Try/);
  }

  // 3b. Repo-relative Story path --help works from subdirectory, while tests/fixtures/*.json is NOT treated as a Story (Finding #6)
  mkdirSync(join(fx.repo, 'tests/fixtures'), { recursive: true });
  writeFileSync(join(fx.repo, 'tests/fixtures/sample.json'), '{"ok":true}\n');
  const subStoryHelp = runBin(['user_stories/my-story.md', '--help'], { cwd: join(fx.repo, 'sub'), home: fx.home, state: fx.state });
  assert.equal(subStoryHelp.status, 0, subStoryHelp.stderr);
  assert.match(subStoryHelp.stdout, /pdd \[OPTIONS\] <PROMPT\.md\|app-map\.json> \[ARGS\.\.\.\]/);
  const fixtureRefused = runBin(['tests/fixtures/sample.json'], { cwd: fx.repo, home: fx.home, state: fx.state });
  assert.equal(fixtureRefused.status, 2);
  assert.match(fixtureRefused.stderr, /Unknown command "tests\/fixtures\/sample\.json"/);

  // 3c. Standalone `.prompt.md` under `--stop`, `--save-last`, `--product`, and `--cli` NEVER launches a new session (Finding #1)
  for (const [args, match] of [
    [['--stop', 'prompts/todo.prompt.md'], /No open Try for "prompts\/todo\.prompt\.md"/],
    [['prompts/todo.prompt.md', '--stop'], /No open Try for "prompts\/todo\.prompt\.md"/],
    [['--stop', 'todo'], /No open Try for "todo"/],
    [['--save-last', 'prompts/todo.prompt.md'], /--save-last takes an optional STORY/],
    [['--product', 'prompts/todo.prompt.md'], /--product composes the repository product maps/],
    [['prompts/todo.prompt.md', '--cli'], /Run pdd prompts\/todo\.prompt\.md \[args\.\.\.\] directly/],
  ]) {
    const res = runBin(args, { cwd: fx.repo, home: fx.home, state: fx.state });
    assert.equal(res.status, 2, `${args.join(' ')} expected exit 2, got ${res.status}: stdout=${res.stdout}\nstderr=${res.stderr}`);
    assert.match(res.stderr, match, `${args.join(' ')}: ${res.stderr}`);
  }

  // 4. Direct typed `.prompt.md` AND unique prompt stem (`calc`) pass `--help` directly to the prompt program (zero network!)
  for (const [cwd, args] of [
    [fx.repo, ['prompts/calc.prompt.md', '--help']],
    [fx.repo, ['calc', '--help']],
    [join(fx.repo, 'sub'), ['calc', '--help']],
  ]) {
    const res = runBin(args, { cwd, home: fx.home, state: fx.state });
    const combined = `${res.stdout}${res.stderr}`;
    assert.match(combined, /Operations:\s+add\b/, `${args.join(' ')} prints prompt operation help: ${combined}`);
    assert.match(combined, /--a <number> \(required\)/, `${args.join(' ')} prints prompt input fields: ${combined}`);
    assert.doesNotMatch(combined, /Quick start:/, `${args.join(' ')} must show prompt help, not PDD root help`);
    assert.doesNotMatch(combined, /\b(?:sim|simulate|simulator)\b/i, `${args.join(' ')} must not mention sim/simulate/Simulator`);
  }

  // 4b. Multi-arg direct prompt invocation passes all args past parser & schema validation to runtime auth (not exit 2!)
  const multiArg = runBin(['prompts/calc.prompt.md', 'add', '--a', '1', '--b', '2'], { cwd: fx.repo, home: fx.home, state: fx.state });
  assert.notEqual(multiArg.status, 2, `expected runtime auth failure (not parser exit 2): stdout=${multiArg.stdout}\nstderr=${multiArg.stderr}`);
  assert.doesNotMatch(multiArg.stderr, /Unsupported command|Unknown command|operands/i);

  const badType = runBin(['prompts/calc.prompt.md', 'add', '--a', 'not-a-number', '--b', '2'], { cwd: fx.repo, home: fx.home, state: fx.state });
  assert.equal(badType.status, 2);
  assert.match(badType.stderr, /Invalid scalar value/);

  // 4c. Direct CLI `.prompt.md` with Python-style prefix options (`--fresh`, `-q`) passes trailing program args cleanly
  const cliDirect = runBin(['--fresh', '-q', 'prompts/todo.prompt.md', 'add', 'Buy milk'], { cwd: fx.repo, home: fx.home, state: fx.state });
  assert.notEqual(cliDirect.status, 2, `expected direct CLI prompt to pass parser cleanly: ${cliDirect.stderr}`);
  assert.doesNotMatch(cliDirect.stderr, /Unsupported command|Unknown command|must declare exactly one command-line program/i);

  // 5. Removed commands refuse with exit 2 and clean 1-line guidance
  for (const [args, expected] of [
    [['simulate', 'prompts/calc.prompt.md'], 'pdd simulate was removed. Run pdd <PROMPT.md|STORY> instead.\n'],
    [['sim', 'my-story'], 'pdd sim was removed. Run pdd <PROMPT.md|STORY> instead.\n'],
    [['try', 'my-story'], 'pdd try was removed. Run pdd <PROMPT.md|STORY> instead.\n'],
  ]) {
    const res = runBin(args, { cwd: fx.repo, home: fx.home, state: fx.state });
    assert.equal(res.status, 2);
    assert.equal(res.stdout, '');
    assert.equal(res.stderr, expected);
  }
});

test('runtime-seam: pdd jobs prints active run (not simulate) from a real slot record and hint normalizer preserves user stdout/URLs/JSON while rewriting legacy diagnostics', async t => {
  const fx = makeTempRepo(t);
  // Seed a real valid active `try` slot record under encodeURIComponent(host) and invoke real `bin/pdd.mjs jobs` (Finding #4)
  const slotDir = join(fx.state, 'slots', encodeURIComponent('127.0.0.1:1'));
  mkdirSync(slotDir, { recursive: true });
  writeFileSync(
    join(slotDir, 'job-try-1.json'),
    JSON.stringify({
      id: 'job-try-1',
      state: 'active',
      pid: process.pid,
      kind: 'try',
      started_at: Date.now(),
      request_ids: [],
    }),
  );
  const jobsRes = runBin(['jobs'], { cwd: fx.repo, home: fx.home, state: fx.state });
  assert.equal(jobsRes.status, 0, jobsRes.stderr);
  assert.match(jobsRes.stdout, /\bactive run\b/, `expected pdd jobs to read seeded slot and print "active run": ${jobsRes.stdout}`);
  assert.doesNotMatch(jobsRes.stdout, /\bsimulate\b/i);

  // Also verify seam runJobs directly with env in input
  let jobsOut = '';
  let jobsErr = '';
  const jobsCode = await runJobs(
    { cwd: fx.repo, env: { HOME: fx.home, PDD_STATE_DIR: fx.state, PDD_RUNTIME_URL: 'http://127.0.0.1:1' } },
    {
      stdout: { write(chunk) { jobsOut += String(chunk); } },
      stderr: { write(chunk) { jobsErr += String(chunk); } },
    },
  );
  assert.equal(jobsCode, 0, jobsErr);
  assert.match(jobsOut, /\bactive run\b/);
  assert.doesNotMatch(jobsOut, /\bsimulate\b/i);

  // Verify hint normalization rewrites legacy stderr diagnostics cleanly while NEVER corrupting user stdout, URLs, iOS Simulator, JSON, or removal lines (Finding #2)
  let out = '';
  let err = '';
  const code = await runTry(
    { cwd: fx.repo, words: ['prompts/calc.prompt.md'], options: {} },
    {
      stdout: { write(chunk) { out += String(chunk); } },
      stderr: { write(chunk) { err += String(chunk); } },
      runTry: async (_input, ports) => {
        ports.stdout.write('Flight Simulator v2.0 on iOS Simulator: https://example.com/Simulator/docs\n');
        ports.stdout.write('{"msg":"pdd sim was removed. Run pdd <PROMPT.md|STORY> instead."}\n');
        ports.stdout.write('It ends in 24 hours, or with: pdd simulate --stop demo\n');
        ports.stderr.write('Product Simulator needs one explicit Story (needs ios-simulator, not iOS Simulator).\n');
        ports.stderr.write('Run pdd simulate place-order --new or pdd simulate --help.\n');
        ports.stderr.write('Run pdd simulate again later. pdd simulate takes one STORY.\n');
        ports.stderr.write('pdd simulate needs one story. Choose one: a, b.\n');
        ports.stderr.write('pdd test and pdd simulate work in a Git repository.\n');
        ports.stderr.write('pdd sim was removed. Run pdd <PROMPT.md|STORY> instead.\n');
        return 0;
      },
    },
  );
  assert.equal(code, 0);
  assert.equal(
    out,
    [
      'Flight Simulator v2.0 on iOS Simulator: https://example.com/Simulator/docs',
      '{"msg":"pdd sim was removed. Run pdd <PROMPT.md|STORY> instead."}',
      'It ends in 24 hours, or with: pdd --stop demo',
      '',
    ].join('\n'),
  );
  assert.equal(
    err,
    [
      'Product Prompt Interpreter needs one explicit Story (needs ios-simulator, not iOS Simulator).',
      'Run pdd place-order --new or pdd . --help.',
      'Run the command again later. pdd takes one STORY or prompt file.',
      'pdd needs one Story or prompt file. Choose one: a, b.',
      'pdd test and direct pdd runs work in a Git repository.',
      'pdd sim was removed. Run pdd <PROMPT.md|STORY> instead.',
      '',
    ].join('\n'),
  );

  // Verify --stop <PROMPT.md> handles symlinked cwd (e.g. macOS /var -> /private/var) and ambiguous multi-Story Try disambiguation
  const realRepo = realpathSync(fx.repo);
  const repoKey = createHash('sha256').update(realRepo).digest('hex').slice(0, 16);
  const reposDir = join(fx.state, 'repos');
  mkdirSync(reposDir, { recursive: true });
  writeFileSync(
    join(reposDir, `${repoKey}.json`),
    JSON.stringify({
      root: realRepo,
      tries: {
        'tests/a.json': { id: 'try-a', story: 'story-a', prompt: 'prompts/calc.prompt.md' },
        'tests/b.json': { id: 'try-b', story: 'story-b', prompt: 'prompts/calc.prompt.md' },
      },
    }),
  );
  const ambigStop = runBin(['--stop', 'prompts/calc.prompt.md'], { cwd: fx.repo, home: fx.home, state: fx.state });
  assert.equal(ambigStop.status, 2);
  assert.match(ambigStop.stderr, /Multiple open Try sessions use "prompts\/calc\.prompt\.md" \(story-a, story-b\)/);

  // Verify runPdd rejects removed commands without touching filesystem
  let pddOut = '';
  let pddErr = '';
  assert.equal(await runPdd(['sim'], { stdout: { write(c) { pddOut += c; } }, stderr: { write(c) { pddErr += c; } } }), 2);
  assert.equal(pddOut, '');
  assert.equal(pddErr, 'pdd sim was removed. Run pdd <PROMPT.md|STORY> instead.\n');
});
