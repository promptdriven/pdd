// Generated from prompts/cli/test-selection.prompt.md (sha256: 4ddf23fa5256bbb745acb84cb104ce63b31974f859a064c791744bea1827471b).
import { basename, posix } from 'node:path';

const AC_HEADING = /(?<![^\n])##[ \t]+Acceptance(?:[ \t]+Criteria)?[ \t]*(?![^\n])/i;
const storyName = path => basename(path).replace(/\.md$/, '');
const folders = path => path.split('/').slice(0, -1);

// The test name rule (one owner): the tests of Story S (user_stories/**/S.md) are S.json and S.<variant>.json in a
// folder named test or tests, at any depth. It uses names only, so no size or content can hide a test.
export const isStoryPath = path =>
  path.endsWith('.md') && folders(path).includes('user_stories') && !/^(?:plan|readme)\.md$/i.test(basename(path));

export const hasAcceptance = text => AC_HEADING.test(text);

const isTestFolderJson = path => path.endsWith('.json') && folders(path).some(part => part === 'test' || part === 'tests');
const byText = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
const listed = items => (items.length < 3 ? items.join(' and ') : `${items.slice(0, -1).join(', ')} and ${items.at(-1)}`);

export function expectedTestPath(storyPath) {
  const parts = folders(storyPath);
  return [...parts.slice(0, parts.lastIndexOf('user_stories')), 'tests', `${storyName(storyPath)}.json`].join('/');
}

// The Story names that a test file name fits: N for N.json, and each S where N is S.<variant>.
function ownerNames(name, names) {
  const fits = names.has(name) ? [name] : [];
  for (let at = name.lastIndexOf('.'); at > 0; at = name.lastIndexOf('.', at - 1)) {
    if (names.has(name.slice(0, at))) fits.push(name.slice(0, at));
  }
  return fits;
}

export function matchTests(storyPaths, files) {
  const groups = new Map(), names = new Set();
  for (const path of [...new Set(storyPaths)].sort(byText)) {
    const name = storyName(path);
    names.add(name);
    if (!groups.has(name)) groups.set(name, { stories: [], files: new Map() });
    groups.get(name).stories.push(path);
  }
  const tests = [], untested = [], orphans = [], claimed = new Set();
  for (const path of [...new Set(files)].sort(byText)) {
    if (!isTestFolderJson(path)) continue;
    const base = basename(path, '.json'), owners = ownerNames(base, names);
    if (!owners.length) {
      orphans.push({ path, line: `${path} matches no Story (user_stories/**/${base}.md).` });
      continue;
    }
    if (owners.length > 1) {
      // A file name that fits two Story names (tests/a.b.json with Stories a and a.b): pdd never picks one.
      const stories = owners.flatMap(name => groups.get(name).stories).sort(byText);
      for (const name of owners) claimed.add(name);
      tests.push({
        path,
        files: [path],
        story: base,
        storyPath: null,
        storyPaths: stories,
        problem: `${path} matches ${stories.length} Stories: ${listed(stories)}. Rename one.`,
      });
      continue;
    }
    const same = groups.get(owners[0]).files;
    same.set(base, [...(same.get(base) ?? []), path]);
  }
  for (const [story, { stories, files: byName }] of groups) {
    if (!byName.size) {
      if (!claimed.has(story)) {
        untested.push(
          ...stories.map(storyPath => ({
            story,
            storyPath,
            line: `${storyPath} has no test: expected ${expectedTestPath(storyPath)} (or ${story}.json in any test or tests folder).`,
          })),
        );
      }
      continue;
    }
    const entry = (found, problem) => ({
      path: found[0],
      files: found,
      story,
      storyPath: stories.length === 1 ? stories[0] : null,
      storyPaths: stories,
      problem,
    });
    if (stories.length > 1) {
      const found = [...byName.values()].flat().sort(byText);
      tests.push(
        entry(found, `${listed(found)} ${found.length > 1 ? 'match' : 'matches'} ${stories.length} Stories: ${listed(stories)}. Rename one.`),
      );
      continue;
    }
    for (const [base, found] of byName) {
      tests.push(entry(found, found.length > 1 ? `${stories[0]} has ${found.length} files named ${base}.json: ${listed(found)}. Keep one.` : null));
    }
  }
  const sorted = (items, key) => items.sort((a, b) => byText(a[key], b[key]));
  return { tests: sorted(tests, 'path'), untested: sorted(untested, 'storyPath'), orphans: sorted(orphans, 'path') };
}

// One line for the JSON files in test folders that match no Story; `pdd test --files` and --json list each one.
export const orphanSummary = orphans =>
  orphans.length === 1
    ? `Warning: ${orphans[0].line}`
    : `Warning: ${orphans.length} JSON files in test folders match no Story (the tests of user_stories/**/S.md are S.json and S.<variant>.json). pdd test --files lists them.`;

// STORY words, by the test name rule: a test path, a story path, a story name or a test file name.
// Returns {selected, unknown, untested}: untested holds the line of each named Story that has no test.
export function selectTests(found, words = [], { native = false, captureSource } = {}) {
  if (!words.length) return { selected: [...found.tests], unknown: [], untested: [] };
  const selected = new Set(), unknown = [], untested = [], nativeSelections = new Map();
  for (const raw of words) {
    const word = raw.replace(/^\.\//, '');
    const hits = found.tests.filter(
      test =>
        test.path === word ||
        test.files?.includes(word) ||
        test.storyPath === word ||
        test.storyPaths?.includes(word) ||
        test.story === word ||
        word === '.' ||
        (!word.startsWith('../') &&
          word !== '..' &&
          [test.path, ...(test.files ?? []), ...(test.storyPaths ?? []), test.storyPath].some(path =>
            path?.startsWith(word.replace(/\/$/, '') + '/'),
          )) ||
        basename(test.path, '.json') === word ||
        test.storyPaths?.some(path => storyName(path) === word),
    );
    const nativeHits = native
      ? (found.nativeSelections ?? []).filter(
          item =>
            item.storyPath === word ||
            item.story === word ||
            word === '.' ||
            (!word.startsWith('../') && word !== '..' && item.storyPath.startsWith(word.replace(/\/$/, '') + '/')),
        )
      : [];
    for (const item of nativeHits) nativeSelections.set(item.storyPath, item);
    const missing = hits.length || nativeHits.length ? [] : (found.untested ?? []).filter(item => item.storyPath === word || item.story === word);
    if (missing.length) untested.push(...missing.map(item => item.line));
    else if (!hits.length && !nativeHits.length) unknown.push(raw);
    for (const hit of hits) selected.add(hit);
  }
  const descriptors = [...nativeSelections.values()].map(item => {
    const links = [...item.section.matchAll(/\[[^\]]*\]\(([^)\s]+)#native-validation-profile-([^)\s]+)\)/g)];
    if (links.length !== 1) return { storyPath: item.storyPath, profileId: null, promptPath: null, reason: 'Native Story owner link is missing or ambiguous.' };
    const promptPath = posix.normalize(posix.join(posix.dirname(item.storyPath), links[0][1]));
    try {
      if (!promptPath.endsWith('.prompt.md')) throw Error('Native owner must be a module prompt.');
      if (typeof captureSource !== 'function') {
        throw Object.assign(new Error('Test selection port (captureSource) is not bound.'), { unboundPort: true });
      }
      const captured = captureSource(found.root, { tests: [item.storyPath, promptPath] });
      return { storyPath: item.storyPath, promptPath, profileId: links[0][2], sourceReferences: captured.files };
    } catch (error) {
      // Workspace/source boundary and unbound-port failures retain their ordinary throw.
      if (error?.unboundPort || error?.name === 'PreflightError') throw error;
      return { storyPath: item.storyPath, promptPath, profileId: links[0][2], reason: error.message };
    }
  });
  return { selected: found.tests.filter(test => selected.has(test)), nativeSelections: descriptors, unknown, untested };
}

export const NO_TESTS = 'No tests found. The test of Story user_stories/S.md is S.json in a test or tests folder. See RUNBOOK.md §2.';

// Why a repo has no tests, by the test name rule (it opens no JSON file): Stories with no test, test-folder JSON
// that matches no Story, *.prompt names, prompts with no interface.
export function whyNoTests(root, visible, found, ports = {}) {
  if (typeof ports?.allowsPath !== 'function' || typeof ports?.hasInterfaceBlock !== 'function') {
    throw new Error('Empty-repository explanation ports (allowsPath, hasInterfaceBlock) are not bound.');
  }
  if (found === undefined) {
    if (typeof ports?.discoverTests !== 'function') {
      throw new Error('Empty-repository explanation port (discoverTests) is not bound.');
    }
    found = ports.discoverTests(root, [...visible]);
  }
  const files = [...visible].filter(path => ports.allowsPath(root, path)).sort();
  const why = [...(found.untested ?? []), ...(found.orphans ?? [])].map(item => item.line);
  for (const path of files.filter(file => file.endsWith('.prompt'))) {
    why.push(`PDD prompts must end in .prompt.md: rename ${path} to ${path}.md.`);
  }
  for (const path of files.filter(file => file.endsWith('.prompt.md'))) {
    if (!ports.hasInterfaceBlock(root, path)) why.push(`${path} has no Runtime interface block. See RUNBOOK.md §2.`);
  }
  return why.length > 5 ? [...why.slice(0, 5), `…and ${why.length - 5} more`] : why;
}
