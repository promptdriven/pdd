// Prompt: prompts/cli/target-both.prompt.md
import { isDeepStrictEqual } from 'node:util';
import { exactValue, stringifyScenarioJson } from '../runtime-seam.mjs';

const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const capture = () => ({ text: '', write(value) { this.text += String(value); return true; } });
const RAN = new Set(['passed', 'failed']);
const checkKey = (stepId, check) => JSON.stringify([stepId, check.criterion_id, check.target ?? 'result', check.path]);
const same = (a, b) => isDeepStrictEqual(exactValue(a), exactValue(b));

function parseJson(text) {
  const trimmed = text.trim();
  if (!trimmed) return null;
  try { return JSON.parse(trimmed); } catch {}
  const last = trimmed.split('\n').filter(Boolean).at(-1);
  try { return JSON.parse(last); } catch { return null; }
}

// One interpreter row per scenario test: which checks failed (with the actual value) and whether it ran.
function interpreterTests(report) {
  const tests = new Map();
  for (const row of Array.isArray(report?.rows) ? report.rows : []) {
    if (!object(row) || typeof row.test !== 'string') continue;
    const failed = new Map();
    for (const check of Array.isArray(row.failed_checks) ? row.failed_checks : []) {
      if (!object(check) || typeof check.step_id !== 'string') continue;
      const key = checkKey(check.step_id, check);
      if (!failed.has(key)) failed.set(key, []);
      failed.get(key).push(check);
    }
    // pdd test --json prints `reason` as {code, message}; older rows may carry a string.
    const reason = [row.why, row.reason, row.reason?.message, row.note?.message].find(text => typeof text === 'string' && text) ?? null;
    const listed = Array.isArray(row.failed_checks) ? row.failed_checks.length : 0;
    const named = [...failed.values()].reduce((sum, list) => sum + list.length, 0);
    const counts = Number.isSafeInteger(row.checks?.passed) && Number.isSafeInteger(row.checks?.total) ? row.checks.total - row.checks.passed : null;
    tests.set(row.test, { state: typeof row.state === 'string' ? row.state : 'unknown', failed, reason, cached: row.cached === true,
      complete: named > 0 && named === listed && (counts === null || counts === named), namesEvery: true });
  }
  return tests;
}

function interpreterCheck(test, stepId, check, seen) {
  if (!test) return { status: 'not run', reason: 'The interpreter did not report this scenario.' };
  if (!RAN.has(test.state)) return { status: 'not run', reason: `The interpreter reported ${test.state}${test.reason ? `: ${test.reason.replace(/\.$/, '')}` : ''}.` };
  const key = checkKey(stepId, check), list = test.failed.get(key) ?? [], index = seen.get(key) ?? 0;
  seen.set(key, index + 1);
  if (test.state === 'failed' && index < list.length) return { status: 'failed', actual: list[index].actual };
  if (test.state === 'failed' && !test.namesEvery) return { status: 'not run', reason: `The interpreter reported failed but did not name every failed check${test.reason ? `: ${test.reason.replace(/\.$/, '')}` : ''}.` };
  // A passed equals check means the interpreter's value is the expected value.
  return { status: 'passed', actual: check.expected };
}

const groupOf = (code, interpreter) => {
  if (code.status === 'not run' || interpreter.status === 'not run') return 'not compared';
  if (code.status !== interpreter.status) return 'disagree';
  if (code.status === 'failed' && !same(code.actual, interpreter.actual)) return 'disagree';
  return 'agree';
};

// A failed row names every failure only when each failed check points at a check of a code step (or a step the code did not run).
function markUnnamedFailures(tests, codeReport) {
  const codeSteps = new Map();
  for (const story of Array.isArray(codeReport?.stories) ? codeReport.stories : []) for (const step of Array.isArray(story.steps) ? story.steps : []) {
    if (typeof step.scenario !== 'string') continue;
    const keys = new Map();
    for (const check of Array.isArray(step.checks) ? step.checks : []) { const key = checkKey(step.step_id, { ...check, target: 'result' }); keys.set(key, (keys.get(key) ?? 0) + 1); }
    if (!codeSteps.has(step.scenario)) codeSteps.set(step.scenario, new Map());
    codeSteps.get(step.scenario).set(step.step_id, { ran: step.status !== 'not run', keys });
  }
  for (const [scenario, test] of tests) {
    if (test.state !== 'failed') continue;
    const steps = codeSteps.get(scenario) ?? new Map();
    test.namesEvery = test.complete && [...test.failed].every(([key, list]) => {
      const step = steps.get(list[0].step_id);
      return step && (!step.ran || (step.keys.get(key) ?? 0) >= list.length);
    });
  }
}

export function compareTargets(codeReport, interpreterReport) {
  const tests = interpreterTests(interpreterReport), used = new Set();
  markUnnamedFailures(tests, codeReport);
  const stories = (Array.isArray(codeReport?.stories) ? codeReport.stories : []).map(story => {
    const checks = [], notCompared = [], states = new Map();
    for (const step of Array.isArray(story.steps) ? story.steps : []) {
      const scenario = typeof step.scenario === 'string' ? step.scenario : null, test = scenario ? tests.get(scenario) : null;
      if (scenario) { used.add(scenario); states.set(scenario, test?.state ?? 'not reported'); }
      if (step.status === 'not run') {
        notCompared.push({ scenario, step_id: step.step_id, side: 'code', reason: step.reason ?? 'not run' });
        continue;
      }
      const seen = new Map();
      for (const check of Array.isArray(step.checks) ? step.checks : []) {
        const code = { status: check.status, actual: check.actual };
        const interpreter = interpreterCheck(test, step.step_id, { ...check, target: 'result' }, seen);
        const group = groupOf(code, interpreter);
        checks.push({ scenario, step_id: step.step_id, criterion_id: check.criterion_id, path: check.path, expected: check.expected, group, code, interpreter });
        if (group === 'not compared') notCompared.push({ scenario, step_id: step.step_id, criterion_id: check.criterion_id, path: check.path, side: 'interpreter', reason: interpreter.reason });
      }
    }
    const disagree = checks.filter(check => check.group === 'disagree');
    const status = disagree.length ? 'disagree' : notCompared.length || !checks.length ? 'not compared' : 'agree';
    return {
      story: story.story, status, code_status: story.status,
      interpreter_status: [...new Set(states.values())].join(', ') || 'not reported',
      differing_steps: [...new Set(disagree.map(check => `${check.scenario} · ${check.step_id}`))],
      differing_criteria: [...new Set(disagree.map(check => check.criterion_id))],
      checks, not_compared: notCompared,
    };
  });
  const extra = [...tests.keys()].filter(test => !used.has(test));
  if (extra.length) stories.push({ story: null, status: 'not compared', code_status: 'not run', interpreter_status: 'reported', differing_steps: [], differing_criteria: [], checks: [],
    not_compared: extra.map(scenario => ({ scenario, step_id: null, side: 'code', reason: 'Code did not select this scenario.' })) });
  const all = stories.flatMap(story => story.checks);
  const count = group => all.filter(check => check.group === group).length;
  return {
    stories,
    summary: { compared: count('agree') + count('disagree'), agree: count('agree'), disagree: count('disagree'), not_compared: stories.reduce((sum, story) => sum + story.not_compared.length, 0) },
  };
}

const show = value => { const text = stringifyScenarioJson(value); return text.length > 200 ? `${text.slice(0, 200)}…` : text; };

function textReport(report) {
  const { summary } = report;
  const calls = report.interpreter.calls === null ? 'interpreter calls unknown' : `${report.interpreter.calls} interpreter call(s)`;
  const lines = [`Target both: ${summary.compared} check(s) compared · ${summary.disagree} disagree · ${summary.agree} agree · ${summary.not_compared} not compared · ${calls}`];
  for (const story of report.stories) {
    lines.push(`${story.status.toUpperCase().padEnd(12)}  ${story.story ?? '(interpreter only)'}  (interpreter ${story.interpreter_status}, code ${story.code_status})`);
    for (const check of story.checks.filter(check => check.group === 'disagree')) {
      const side = value => value.status === 'passed' ? 'as expected' : show(value.actual);
      lines.push(`  ${check.scenario} · step ${check.step_id} · ${check.criterion_id} ${check.path}: expected ${show(check.expected)}, interpreter ${side(check.interpreter)}, code ${side(check.code)}`);
    }
    for (const item of story.not_compared) {
      const where = [item.scenario, item.step_id !== null && item.step_id !== item.scenario ? `step ${item.step_id}` : null, item.criterion_id ? `${item.criterion_id} ${item.path}` : null].filter(Boolean).join(' · ');
      lines.push(`  ${where}: not compared: ${item.side} not run: ${item.reason}`);
    }
  }
  if (report.interpreter.exit_code !== 0 && !report.interpreter.rows) lines.push(`The interpreter run did not report results (exit ${report.interpreter.exit_code}); its messages are above.`);
  return lines.join('\n') + '\n';
}

const INTERPRETER_OPTIONS = ['--fresh', '--max-calls', '--timeout'];

export async function runTargetBoth({ root, words = [], options = {}, json = false }, { stdout, stderr, env = process.env, check, codeTest } = {}) {
  const runCode = codeTest ?? (await import('../compiled-test.mjs')).runCompiledTest;
  const codeOut = capture();
  const codeExit = await runCode({ root, words, json: true }, { stdout: codeOut, stderr });
  if (codeExit === 2) return 2;
  const codeReport = parseJson(codeOut.text);
  if (!object(codeReport) || !Array.isArray(codeReport.stories)) { stderr.write('The code run did not produce a report.\n'); return 3; }

  // Only after the free local run: the interpreter run may cost AI calls.
  const runCheck = check ?? (await import('../runtime-seam.mjs')).check;
  const interpreterOptions = Object.fromEntries(INTERPRETER_OPTIONS.filter(key => options[key] !== undefined).map(key => [key, options[key]]));
  const interpreterOut = capture();
  const interpreterExit = await runCheck({ words: [...words], options: { ...interpreterOptions, '--json': true }, cwd: root }, { stdout: interpreterOut, stderr, env });
  const interpreterReport = parseJson(interpreterOut.text);
  const rows = object(interpreterReport) && Array.isArray(interpreterReport.rows) ? interpreterReport.rows : null;

  const compared = compareTargets(codeReport, rows ? interpreterReport : null);
  const calls = rows && rows.every(row => typeof row.calls === 'number') ? rows.reduce((sum, row) => sum + row.calls, 0) : rows ? null : 0;
  const report = {
    target: 'both', commit: codeReport.commit ?? null, dirty: codeReport.dirty ?? null,
    summary: compared.summary,
    interpreter: { exit_code: interpreterExit, batch: interpreterReport?.batch ?? null, calls, rows: rows ? rows.length : null },
    stories: compared.stories,
  };
  stdout.write(json ? stringifyScenarioJson(report) + '\n' : textReport(report));
  if (!rows && ![0, 1].includes(interpreterExit)) return interpreterExit;
  const passed = report.commit && compared.summary.disagree === 0 && compared.summary.not_compared === 0 && compared.summary.compared > 0
    && compared.stories.every(story => story.code_status === 'passed' && story.interpreter_status === 'passed');
  return passed ? 0 : 1;
}
