// Generated from prompts/cli/runtime-exit.prompt.md (sha256: f84eec69f908e020e767796a3060315e1a4e5589c32b7cdfe90b8b0a52601a48).
export const STATE_EXIT_CODES = Object.freeze({
  passed: 0,
  failed: 1,
  unknown: 3,
  waiting: 3,
  sent: 3,
  partial: 3,
  queued: 3,
  running: 3,
  refused: 4,
  not_run: 5,
  'not run': 5,
});

export const COMMAND_EXIT_CODE = 2;

export function exitFor(value) {
  const state = typeof value === 'string' ? value : value?.overall ?? value?.state;
  return typeof state === 'string' && Object.hasOwn(STATE_EXIT_CODES, state) ? STATE_EXIT_CODES[state] : 3;
}

export function outcomeExitCode(outcomes, options, ports = {}) {
  if (typeof ports?.outcomeOverall !== 'function') {
    throw new Error('Exit code port (outcomeOverall) is not bound.');
  }
  return exitFor(ports.outcomeOverall(outcomes, options));
}

export const exitCodeFor = outcomeExitCode;
