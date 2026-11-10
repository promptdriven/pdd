// Generated from prompts/cli/test-suite-queue.prompt.md.
// Compatibility entrypoint owned by prompts/cli/test-suite-queue.prompt.md.
import { appendFileSync, mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { runTestSuite, suiteQueueRoot } from './test-suite-queue.mjs';

const env = process.env;
try {
  const root = suiteQueueRoot(env);
  mkdirSync(root, { recursive: true, mode: 0o700 });
  if (process.argv[2] !== '--check') {
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
} catch (error) {
  process.stderr.write(`vm-suite-lock: ${error.code ?? error.message}\n`);
  process.exitCode = 1;
}
