// Generated from prompts/cli/calc.prompt.md (sha256: cb5be76252be8e3fba3be8485f5cf14c628616da5b2397deea9848806a2a47fe).
import { evaluateDerivation } from './runtime-seam.mjs';

/** Evaluate one exact arbitrary-precision arithmetic expression to its canonical string. */
export function evaluateCalcExpression(expression) {
  return evaluateDerivation(expression);
}

/** Run the pure local `pdd calc` command and return `{ exit_code, stdout, stderr }`. */
export function runCalc({ expression } = {}) {
  if (typeof expression !== 'string' || !expression.trim()) {
    return { exit_code: 2, stdout: '', stderr: 'pdd calc: missing expression\n' };
  }
  try {
    const result = evaluateCalcExpression(expression);
    return { exit_code: 0, stdout: `${result}\n`, stderr: '' };
  } catch (error) {
    const reason = typeof error?.message === 'string' ? error.message.replace(/\s+/g, ' ').trim() : '';
    return { exit_code: 2, stdout: '', stderr: `pdd calc: ${reason || 'invalid expression'}\n` };
  }
}
