// Generated from prompts/cli/test-suite-queue.prompt.md (sha256: 9a6fbeb4f0e51d65db80cee642a73f0977c1943b8a6548f9c24281b66b319d3c).
// Direct and compatibility entrypoint owned by prompts/cli/test-suite-queue.prompt.md.
import { appendFileSync, mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { runTestSuite, suiteQueueRoot } from './test-suite-queue.mjs';

function parseDirectSuiteArgs(argv) {
  const tokens = argv[0] === 'suite' ? argv.slice(1) : argv;
  let command = null, timeout = 30;
  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i];
    if (token === '--command') {
      command = tokens[++i] ?? '';
    } else if (token.startsWith('--command=')) {
      command = token.slice('--command='.length);
    } else if (token === '--timeout') {
      timeout = Number(tokens[++i]);
    } else if (token.startsWith('--timeout=')) {
      timeout = Number(token.slice('--timeout='.length));
    } else {
      return {
        error: `test-suite-entry.mjs: unexpected argument "${token}".\nInvariant: direct suite mode accepts only --command COMMAND and optional --timeout MIN (0..120).\nFix: pass --command "<cmd>" [--timeout 0..120].\nRerun: node src/test-suite-entry.mjs suite --command "npm test" --timeout 0`,
      };
    }
  }
  if (typeof command !== 'string' || !command.trim()) {
    return {
      error: 'test-suite-entry.mjs: missing required --command value.\nInvariant: direct suite mode requires a non-blank test command string.\nFix: supply --command "<cmd>" (for example --command "npm test").\nRerun: node src/test-suite-entry.mjs suite --command "npm test" --timeout 0',
    };
  }
  if (!Number.isInteger(timeout) || timeout < 0 || timeout > 120) {
    return {
      error: `test-suite-entry.mjs: invalid --timeout value "${timeout}".\nInvariant: --timeout must be an integer from 1 to 120 minutes, or 0 for no time limit.\nFix: pass --timeout 0 (or 1..120).\nRerun: node src/test-suite-entry.mjs suite --command "${command}" --timeout 0`,
    };
  }
  return { command, timeout };
}

const env = process.env;
const rawArgs = process.argv.slice(2);
const directMode = rawArgs[0] === 'suite' || rawArgs.some(arg => arg === '--command' || arg.startsWith('--command='));

try {
  if (directMode) {
    const parsed = parseDirectSuiteArgs(rawArgs);
    if (parsed.error) {
      process.stderr.write(`${parsed.error}\n`);
      process.exitCode = 2;
    } else {
      const result = await runTestSuite({ cwd: process.cwd(), env, command: parsed.command, timeout: parsed.timeout });
      if (result.exitCode) process.stderr.write(`${result.message}\n`);
      process.exitCode = result.exitCode;
    }
  } else {
    const root = suiteQueueRoot(env);
    mkdirSync(root, { recursive: true, mode: 0o700 });
    if (rawArgs[0] !== '--check') {
      const history = `${env.PDD_VM_SUITE_LOCK || `${env.HOME}/.local/state/pdd/vm-suite/fullsuite.lock`}.history`;
      mkdirSync(dirname(history), { recursive: true });
      const stamp = () => new Intl.DateTimeFormat('en-GB', {timeZone:'America/Los_Angeles', hour:'2-digit', minute:'2-digit', second:'2-digit', hourCycle:'h23'}).format(new Date());
      const log = text => { process.stdout.write(`${text}\n`); appendFileSync(history, `${text}\n`); };
      process.stdout.write(`queued ${stamp()} in ${process.cwd()}\n`);
      const result = await runTestSuite({cwd:process.cwd(), env, command:env.SUITE?.trim() ? env.SUITE : 'POCKET_BROWSER_BIN=/usr/bin/google-chrome npm test'}, {
        announceReceipt: false,
        say: text => text === 'running the full test suite' ? log(`started ${stamp()} in ${process.cwd()}`) : process.stdout.write(`${text}\n`),
      });
      log(`finished ${stamp()} exit ${result.exitCode} in ${process.cwd()}`);
      if (result.exitCode) process.stderr.write(`${result.message}\n`);
      process.exitCode = result.exitCode;
    }
  }
} catch (error) {
  process.stderr.write(`${directMode ? 'test-suite-entry' : 'vm-suite-lock'}: ${error.code ?? error.message}\n`);
  process.exitCode = 1;
}
