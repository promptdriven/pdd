import { spawn, spawnSync } from 'child_process';
import path from 'path';

import globalSetup from './global-setup';

globalSetup();

const activeProjectId = path.basename(process.cwd());

const commonEnv = {
  ...process.env,
  VIDEO_EDITOR_PROJECT_ID:
    process.env.VIDEO_EDITOR_PROJECT_ID ?? activeProjectId,
  CLAUDE_FIX_MODEL: process.env.CLAUDE_FIX_MODEL ?? 'claude-sonnet-4-5',
  CLAUDE_DRY_RUN_MODEL:
    process.env.CLAUDE_DRY_RUN_MODEL ?? 'claude-sonnet-4-5',
  PDD_DETERMINISTIC_PIPELINE:
    process.env.PDD_DETERMINISTIC_PIPELINE ?? '1',
  VIDEO_EDITOR_SKIP_COMPOSITION_VALIDATION:
    process.env.VIDEO_EDITOR_SKIP_COMPOSITION_VALIDATION ?? '1',
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
