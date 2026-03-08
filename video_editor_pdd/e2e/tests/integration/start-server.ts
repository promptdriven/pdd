import { spawn, spawnSync } from 'child_process';

import globalSetup from './global-setup';

globalSetup();

const commonEnv = {
  ...process.env,
  CLAUDE_FIX_MODEL: process.env.CLAUDE_FIX_MODEL ?? 'claude-sonnet-4-5',
  CLAUDE_DRY_RUN_MODEL:
    process.env.CLAUDE_DRY_RUN_MODEL ?? 'claude-sonnet-4-5',
  PDD_DETERMINISTIC_PIPELINE:
    process.env.PDD_DETERMINISTIC_PIPELINE ?? '1',
};

const build = spawnSync('npx', ['next', 'build'], {
  env: commonEnv,
  stdio: 'inherit',
});

if (build.status !== 0) {
  process.exit(build.status ?? 1);
}

const child = spawn(
  'npx',
  ['next', 'start', '-p', '3001'],
  {
    env: commonEnv,
    stdio: 'inherit',
  }
);

const forwardSignal = (signal: NodeJS.Signals) => {
  child.kill(signal);
};

process.on('SIGINT', () => forwardSignal('SIGINT'));
process.on('SIGTERM', () => forwardSignal('SIGTERM'));

child.on('exit', (code, signal) => {
  if (signal) {
    process.kill(process.pid, signal);
    return;
  }
  process.exit(code ?? 0);
});
