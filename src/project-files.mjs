// Generated from prompts/cli/files.prompt.md (sha256: 67cd2901fdf57bcbf7e5478b937784c650dee4f24ee336c2be97d7c610a36b7c).
import { spawnSync } from 'node:child_process';
import { findTests, preflight, promptRefusal, promptSchemaRefusals, readPrompt } from './runtime-seam.mjs';

const sorted = paths => [...new Set(paths)].sort();
const problemKey = problem => JSON.stringify([problem.path, problem.code, problem.section, problem.message]);
const uniqueProblems = problems => [...new Map(problems.map(problem => [problemKey(problem), problem])).values()];
const sourceProblem = (path, error) => ({ path, code: error.code ?? /^([\w-]+):/.exec(error.message)?.[1] ?? 'source-unreadable', section: 'source', message: error.message });

// This view projects the shared reader. It owns no parsing or matching rules.
export function inspectProjectFiles(root) {
  const found = findTests({ root, excludeFixtureProjects: true }), prompts = new Map(), failures = new Map();
  const warnings = [...found.warnings];
  const read = path => {
    if (!prompts.has(path) && !failures.has(path)) {
      try { prompts.set(path, readPrompt(root, found.visible, path, found.workspace)); }
      catch (error) { failures.set(path, sourceProblem(path, error)); }
    }
    return prompts.get(path);
  };
  const promptPaths = [...found.discoveryVisible].filter(path => path.endsWith('.prompt.md')).sort();
  for (const path of promptPaths) read(path);
  const reached = (path, paths) => {
    if (typeof path !== 'string' || paths.has(path)) return;
    paths.add(path);
    const prompt = read(path);
    for (const call of Array.isArray(prompt?.interface?.calls) ? prompt.interface.calls : []) reached(call?.target, paths);
  };
  const tests = found.tests.map(test => {
    const paths = new Set();
    for (const step of Array.isArray(test.doc?.steps) ? test.doc.steps : []) reached(step?.entry_path, paths);
    for (const path of Array.isArray(test.doc?.entry_paths) ? test.doc.entry_paths : []) reached(path, paths);
    let refusals;
    try {
      const checked = preflight({ root, found, selected: [test] });
      refusals = checked.rows[0].refusals.map(problem => ({ path: test.path, ...problem }));
      warnings.push(...checked.warnings, ...checked.rows[0].warnings);
    } catch (error) { refusals = [sourceProblem(test.path, error)]; }
    return { path: test.path, files: test.files, stories: sorted(test.storyPaths ?? []), prompts: sorted(paths), refusals };
  });
  const promptRows = promptPaths.map(path => {
    const prompt = read(path), users = tests.filter(test => test.prompts.includes(path));
    let refusals = [];
    if (!failures.has(path)) {
      const freshness = promptRefusal(prompt, 'interface');
      if (freshness) refusals.push({ path, ...freshness });
      try { refusals.push(...promptSchemaRefusals(root, found, prompt, prompts)); }
      catch (error) { refusals.push(sourceProblem(path, error)); }
    } else refusals.push(failures.get(path));
    return { path, has_interface: failures.has(path) ? null : prompt?.blocks?.length === 1, stories: sorted(users.flatMap(test => test.stories)),
      tests: users.map(test => test.path), references: prompt?.references ?? [], refusals: uniqueProblems(refusals) };
  });
  const stories = found.stories.map(story => ({ path: story.path, title: story.title,
    tests: sorted(tests.filter(test => test.stories.includes(story.path)).flatMap(test => test.files)) }));
  const refusals = uniqueProblems([...promptRows, ...tests].flatMap(row => row.refusals))
    .sort((a, b) => problemKey(a) < problemKey(b) ? -1 : problemKey(a) > problemKey(b) ? 1 : 0);
  return { schema_version: 'pdd.files.v1', prompts: promptRows, stories, tests, orphans: found.orphans, refusals, warnings: [...new Set(warnings)] };
}

export function runProjectFiles({ cwd = process.cwd(), json = false } = {}, ports = {}) {
  const stdout = ports.stdout ?? process.stdout, stderr = ports.stderr ?? process.stderr;
  const top = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  if (top.status !== 0) { stderr.write('pdd files works in a Git repository.\n'); return 2; }
  try {
    const view = inspectProjectFiles(top.stdout.trim());
    if (json) stdout.write(`${JSON.stringify(view)}\n`);
    else {
      for (const prompt of view.prompts) stdout.write(`Prompt: ${prompt.path} (${prompt.has_interface === null ? 'interface unavailable' : prompt.has_interface ? 'Runtime interface' : 'no single Runtime interface'})\n`);
      for (const story of view.stories) stdout.write(`Story: ${story.path}; tests: ${story.tests.join(', ') || 'none'}\n`);
      for (const test of view.tests) stdout.write(`Test: ${test.files.join(', ')}; Stories: ${test.stories.join(', ')}; prompts: ${test.prompts.join(', ')}\n`);
      for (const orphan of view.orphans) stdout.write(`${orphan.line}\n`);
      for (const problem of view.refusals) stdout.write(`${problem.path}: ${problem.code} ${problem.section} ${problem.message}\n`);
      for (const warning of view.warnings) stdout.write(`${warning}\n`);
    }
    return 0;
  } catch (error) { stderr.write(`${error.message}\n`); return error.exitCode ?? 4; }
}
