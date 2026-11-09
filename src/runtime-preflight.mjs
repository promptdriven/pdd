import { markdownLinks, markdownDefinitions, markdownSectionText } from './runtime-markdown.mjs';
import { buildBindingPlan, runtimeBoundary } from './runtime-binding-plan.mjs';
// Generated from prompts/cli/runtime-preflight.prompt.md (sha256: 593795d5383de3ba190e67df257d1f7f1973f0e36c599efdc6a3f2459525eeb9).
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { closeSync, constants, fstatSync, lstatSync, openSync, readFileSync, readlinkSync, realpathSync, writeFileSync } from 'node:fs';
import { basename, join, posix, isAbsolute } from 'node:path';
import { isDeepStrictEqual } from 'node:util';
import { expandSource } from './contract-refs.mjs';
import {loadRuntimeWorkspace as loadWorkspacePolicy,allowsRuntimePath,requireRuntimePath as requireWorkspacePath} from './runtime-workspace.mjs';

function workspaceError(error){if(error?.code?.startsWith('workspace-'))throw Object.assign(new PreflightError(4,error.message),{code:error.code});throw error;}
function loadRuntimeWorkspace(input){try{return loadWorkspacePolicy(input);}catch(error){workspaceError(error);}}
function requireRuntimePath(policy,input){try{return requireWorkspacePath(policy,input);}catch(error){workspaceError(error);}}
function boundedWorkspace(root,supplied){const native=loadRuntimeWorkspace({root});if(!supplied||!supplied.configured)return native;if(!native.configured)return supplied;const allowed=[];for(const a of native.allowed_paths)for(const b of supplied.allowed_paths){if(a===b)allowed.push(a);else if(a.endsWith('/')&&b.startsWith(a))allowed.push(b);else if(b.endsWith('/')&&a.startsWith(b))allowed.push(a);}return Object.freeze({configured:true,allowed_paths:Object.freeze([...new Set(allowed)])});}
export const TEST_SCHEMA = 'prompt-runtime.program-scenario.v1';
// The interpreter's upload limit (prompt-runtime server/uploads.py: MAX_UPLOAD 10 MiB, at most 10,000 files).
// The only size limit on what pdd sends; over it, pdd names the largest files with their sizes.
export const LIMITS = Object.freeze({ bytes: 10_485_760, files: 10_000 });
const TOP_KEYS = new Set(['schema_version', 'story_path', 'criteria', 'initial_world', 'steps', 'entry_paths', 'simulation',
  'check_exemptions', 'context', 'context_byte_budget', 'criteria_scope', 'prompt_mappings']);
const REQUIRED_KEYS = ['schema_version', 'criteria', 'initial_world', 'steps'];
const STEP_KEYS = new Set(['step_id', 'entry_path', 'operation', 'input', 'checks', 'expected_error', 'simulation_overrides', 'model']);
const RULE_OPS = new Set(['at_most', 'at_least', 'not_contains', 'all_in', 'equals_ignore_case']);
const EXACT_OPS = new Set(['equals', 'not_equals', 'one_of', 'count', ...RULE_OPS]);
const SCHEMA_RULES = new Set(['type', 'properties', 'required', 'additionalProperties', 'items', 'enum', 'const', 'oneOf',
  'minimum', 'maximum', 'exclusiveMinimum', 'exclusiveMaximum', 'multipleOf', 'minLength', 'maxLength', 'pattern',
  'minItems', 'maxItems', 'uniqueItems', 'minProperties', 'maxProperties']);
const SCHEMA_NOTES = new Set(['title', 'description', 'default', 'examples', 'format', '$comment', '$schema', '$id']);

// The engine's _INTERFACE regex (prompt_program_discovery.py, eae2202a).
const INTERFACE = /<details\b[^>]*>\s*<summary\b[^>]*>\s*(?:<strong\b[^>]*>\s*)?Runtime\s+interface(?:\s*:\s*[^<]+?)?\s*(?:<\/strong\s*>\s*)?(?:\s*:\s*[^<]+?)?\s*<\/summary\s*>\s*```json\b\s*([\s\S]*?)\s*```\s*<\/details\s*>/gid;

export class PreflightError extends Error {
  constructor(exitCode, message) { super(message); this.name = 'PreflightError'; this.exitCode = exitCode; }
}

export const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
export const interfaceBlocks = text => [...text.matchAll(INTERFACE)];
export const proseSha256 = text => sha256(Buffer.from(text.replace(INTERFACE, ''), 'utf8'));

// Python str.isspace, str.splitlines and str.split, so story criteria equal the engine's.
const PY_SPACE = '[\\t\\n\\v\\f\\r\\x1c-\\x1f \\x85\\xa0\\u1680\\u2000-\\u200a\\u2028\\u2029\\u202f\\u205f\\u3000]';
const pyStrip = text => text.replace(new RegExp(`^${PY_SPACE}+|${PY_SPACE}+$`, 'g'), '');
const pyWords = text => text.split(new RegExp(`${PY_SPACE}+`)).filter(Boolean).join(' ');
function pySplitLines(text) {
  const lines = text.split(/\r\n|[\n\r\v\f\x1c\x1d\x1e\x85\u2028\u2029]/);
  if (lines.at(-1) === '') lines.pop();
  return lines;
}
const AC_HEADING = /(?<![^\n])##[ \t]+Acceptance(?:[ \t]+Criteria)?[ \t]*(?![^\n])/i;
const NEXT_HEADING = /(?<![^\n])##[ \t]+/;
const NUMBERED_ITEM = /^([1-9][0-9]*)[.)][ \t]+(.+)$/;
const BULLET_ITEM = /(?<![^\n])[ \t]*[-*][ \t]+([\s\S]+?)(?=\n[ \t]*[-*][ \t]+|(?![\s\S]))/g;

// A port of the engine's explicit_story_criteria (program_scenario.py, eae2202a).
export function storyCriteria(source) {
  const heading = AC_HEADING.exec(source);
  const body = heading ? source.slice(heading.index + heading[0].length) : source;
  const result = [];
  let current = null, expected = 1;
  for (const line of pySplitLines(body)) {
    const match = NUMBERED_ITEM.exec(line);
    if (match) {
      if (Number(match[1]) !== expected) {
        if (result.length || current !== null) break;
        continue;
      }
      if (current !== null) result.push(current.join(' '));
      current = [pyStrip(match[2])];
      expected += 1;
    } else if (current !== null) {
      if (!pyStrip(line) || line.startsWith('#')) { result.push(current.join(' ')); current = null; }
      else current.push(pyStrip(line));
    }
  }
  if (current !== null) result.push(current.join(' '));
  if (!result.length && heading) {
    const next = NEXT_HEADING.exec(body);
    const section = next ? body.slice(0, next.index) : body;
    return [...section.matchAll(BULLET_ITEM)].map(match => pyWords(match[1]));
  }
  return result;
}

export function gitFiles(root) {
  const listed = spawnSync('git', ['ls-files', '-z', '-co', '--exclude-standard'], { cwd: root, maxBuffer: 512 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
  if (listed.status !== 0) throw new PreflightError(5, 'pdd could not list the Git files of this repository.');
  return [...new Set(listed.stdout.toString('utf8').split('\0').filter(Boolean))].sort();
}

const statOf = path => { try { return lstatSync(path, { bigint: true }); } catch (error) { if (['ENOENT', 'ENAMETOOLONG'].includes(error.code)) return null; throw error; } };
const readText = (root, path) => {
  requireRuntimePath(loadRuntimeWorkspace({root}),{path,from:'Source read'});
  const stat=statOf(join(root,path));
  sourceLimit([{path,size:Number(stat?.size ?? 0)}]);
  return readFileSync(join(root,path),'utf8');
};
const storyName = path => basename(path).replace(/\.md$/, '');
const titleOf = text => text.split('\n').find(line => line.startsWith('# '))?.slice(2).trim() || null;

// The test name rule (one owner): the tests of Story S (user_stories/**/S.md) are S.json and S.<variant>.json in a
// folder named test or tests, at any depth. It uses names only, so no size or content can hide a test.
const folders = path => path.split('/').slice(0, -1);
export const isStoryPath = path => path.endsWith('.md') && folders(path).includes('user_stories') && !/^(?:plan|readme)\.md$/i.test(basename(path));
const hasAcceptance = text => AC_HEADING.test(text);
const isTestFolderJson = path => path.endsWith('.json') && folders(path).some(part => part === 'test' || part === 'tests');
const byText = (a, b) => a < b ? -1 : a > b ? 1 : 0;
const listed = items => items.length < 3 ? items.join(' and ') : `${items.slice(0, -1).join(', ')} and ${items.at(-1)}`;
export function expectedTestPath(storyPath) {
  const parts = folders(storyPath);
  return [...parts.slice(0, parts.lastIndexOf('user_stories')), 'tests', `${storyName(storyPath)}.json`].join('/');
}
// The Story names that a test file name fits: N for N.json, and each S where N is S.<variant>.
function ownerNames(name, names) {
  const fits = names.has(name) ? [name] : [];
  for (let at = name.lastIndexOf('.'); at > 0; at = name.lastIndexOf('.', at - 1)) if (names.has(name.slice(0, at))) fits.push(name.slice(0, at));
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
    if (!owners.length) { orphans.push({ path, line: `${path} matches no Story (user_stories/**/${base}.md).` }); continue; }
    if (owners.length > 1) {
      // A file name that fits two Story names (tests/a.b.json with Stories a and a.b): pdd never picks one.
      const stories = owners.flatMap(name => groups.get(name).stories).sort(byText);
      for (const name of owners) claimed.add(name);
      tests.push({ path, files: [path], story: base, storyPath: null, storyPaths: stories, problem: `${path} matches ${stories.length} Stories: ${listed(stories)}. Rename one.` });
      continue;
    }
    const same = groups.get(owners[0]).files;
    same.set(base, [...(same.get(base) ?? []), path]);
  }
  for (const [story, { stories, files: byName }] of groups) {
    if (!byName.size) {
      if (!claimed.has(story)) untested.push(...stories.map(storyPath => ({ story, storyPath, line: `${storyPath} has no test: expected ${expectedTestPath(storyPath)} (or ${story}.json in any test or tests folder).` })));
      continue;
    }
    const entry = (found, problem) => ({ path: found[0], files: found, story, storyPath: stories.length === 1 ? stories[0] : null, storyPaths: stories, problem });
    if (stories.length > 1) {
      const found = [...byName.values()].flat().sort(byText);
      tests.push(entry(found, `${listed(found)} ${found.length > 1 ? 'match' : 'matches'} ${stories.length} Stories: ${listed(stories)}. Rename one.`));
      continue;
    }
    for (const [base, found] of byName) tests.push(entry(found, found.length > 1 ? `${stories[0]} has ${found.length} files named ${base}.json: ${listed(found)}. Keep one.` : null));
  }
  const sorted = (items, key) => items.sort((a, b) => byText(a[key], b[key]));
  return { tests: sorted(tests, 'path'), untested: sorted(untested, 'storyPath'), orphans: sorted(orphans, 'path') };
}
// One line for the JSON files in test folders that match no Story; `pdd test --files` and --json list each one.
export const orphanSummary = orphans => orphans.length === 1 ? `Warning: ${orphans[0].line}`
  : `Warning: ${orphans.length} JSON files in test folders match no Story (the tests of user_stories/**/S.md are S.json and S.<variant>.json). pdd test --files lists them.`;

// Tests, stories and Git-visible regular files of one repo.
export function findTests({ root, files = gitFiles(root), workspace, excludeFixtureProjects = false }) {
  return discoverTests(root, files,false,workspace,excludeFixtureProjects);
}

// Identify projects by Git-visible names before inspecting any Story or test content.
function fixtureProjectRoots(root, files) {
  const directories = new Map();
  for (const path of files) {
    const parts = path.split('/');
    if (parts[0] !== 'test' || parts[1] !== 'fixtures') continue;
    // Do not follow an unchecked link while classifying a name.
    let safe = true;
    for (let i = 1; i < parts.length; i++) {
      const ancestor = statOf(join(root, ...parts.slice(0, i)));
      if (!ancestor?.isDirectory()) { safe = false; break; }
    }
    if (!safe) continue;
    const stat = statOf(join(root, path));
    if (!stat || (!stat.isFile() && !stat.isSymbolicLink())) continue;
    for (let i = 3; i < parts.length - 1; i++) {
      if (parts[i] !== 'user_stories' && parts[i] !== 'tests') continue;
      const project = parts.slice(0, i).join('/');
      if (!directories.has(project)) directories.set(project, new Set());
      directories.get(project).add(parts[i]);
    }
  }
  return [...directories].filter(([, dirs]) => dirs.has('user_stories') && dirs.has('tests')).map(([path]) => path).sort();
}

const outsideFixtureProjects = (files, roots) => files.filter(path => !roots.some(root => path.startsWith(`${root}/`)));

// Git-visible regular files and Stories: discovery reads Story files, never JSON files.
function discoverStories(root, files, strict = false, workspace=loadRuntimeWorkspace({root}), discoveryFiles = null) {
  workspace=boundedWorkspace(root,workspace);
  const visible = new Set(), stories = [], storyFiles = [], titles = new Map(), warnings = [], linkedPaths = new Set(), sizes = new Map();
  let linkedFiles = strict||workspace.configured ? filePort(root, new Set(files), strict,workspace) : undefined;
  for (const path of files) {
    if(!allowsRuntimePath(workspace,path))continue;
    let stat = strict ? null : statOf(join(root, path)), linked = false;
    if (strict || workspace.configured || stat?.isSymbolicLink()) {
      linkedFiles ??= sourceFilePort(root, new Set(files));
      try {
        const info = linkedFiles.stat({path});
        stat = { isFile: () => info.exists, size: BigInt(info.size) }; linked = true;
      } catch { continue; } // Unrelated unsafe links do not select or refuse source.
    }
    if (!stat?.isFile()) continue;
    visible.add(path); sizes.set(path, Number(stat.size));
    if (linked) linkedPaths.add(path);
    if ((!discoveryFiles || discoveryFiles.has(path)) && isStoryPath(path)) {
      // Every Story file can own a test by its name. An index (PLAN.md, README.md) or a file with no acceptance
      // criteria section is not listed as a Story (2048 session, 0.1.6), so it never gets a "has no test" line.
      storyFiles.push(path);
      if (stat.size > LIMITS.bytes) { warnings.push(`Warning: ${path}: discovery unavailable (too big; limit 10 MB).`); continue; }
      let text;
      try { text = linked ? linkedFiles.read({path}).content : readText(root, path); }
      catch (error) {
        if (!(error instanceof PreflightError && error.exitCode === 4) && !['EACCES','EPERM','EISDIR','ENOENT'].includes(error.code)) throw error;
        warnings.push(`Warning: ${path}: discovery unavailable (${error.code ?? error.message}).`); continue;
      }
      titles.set(path, titleOf(text));
      if (hasAcceptance(text)) stories.push({ path, name: storyName(path), title: titleOf(text) });
    }
  }
  const read = path => strict || linkedPaths.has(path) ? linkedFiles.read({path}).content : readText(root, path);
  return { visible, stories, storyFiles, titles, warnings, sizes, read };
}

function discoverTests(root, files, strict = false,workspace=loadRuntimeWorkspace({root}),excludeFixtureProjects=false) {
  const excluded = excludeFixtureProjects ? fixtureProjectRoots(root, files) : [];
  const discoveryFiles = new Set(outsideFixtureProjects(files, excluded));
  const { visible, stories, storyFiles, titles, warnings: storyWarnings, sizes, read } = discoverStories(root, files, strict,workspace,discoveryFiles);
  const named = new Set(stories.map(story => story.path)), rule = matchTests(storyFiles, [...visible].filter(path => discoveryFiles.has(path)));
  rule.untested = rule.untested.filter(item => named.has(item.storyPath));
  const tests = rule.tests.map(entry => {
    const size = sizes.get(entry.path);
    const test = { path: entry.path, files: entry.files, story: entry.story, storyPath: entry.storyPath, storyPaths: entry.storyPaths, title: titles.get(entry.storyPath) ?? entry.story };
    if (entry.problem) return { ...test, error: entry.problem };
    if (size > LIMITS.bytes) return { ...test, error: `${entry.path} is ${formatSize(size)}. The upload limit is 10 MB, so pdd cannot send it.` };
    // A matched test is read in full, at any size below the upload limit.
    try { return { ...test, doc: JSON.parse(read(entry.path)) }; }
    catch (error) {
      if (error instanceof SyntaxError) return { ...test, error: `${entry.path} is not valid JSON: ${error.message}` };
      if (error.code === 'EACCES' || error.code === 'EISDIR' || error.code === 'ENOENT' || error instanceof PreflightError) return { ...test, error: `${entry.path} cannot be read: ${error.code ?? error.message}.` };
      throw error;
    }
  });
  const warnings = [...excluded.map(path => `Warning: skipped nested fixture project ${path}.`), ...storyWarnings, ...rule.tests.filter(entry => entry.problem).map(entry => `Warning: ${entry.problem}`),
    ...rule.untested.map(item => `Warning: ${item.line}`), ...(rule.orphans.length ? [orphanSummary(rule.orphans)] : [])];
  // Discover declarations from already bounded Story reads. Owner files are
  // opened only after explicit lint selection.
  const nativeSelections = stories.flatMap(story => {
    const section = /^## Native validation\s*\n([\s\S]*?)(?=^## |$(?![\s\S]))/m.exec(read(story.path));
    return section ? [{ storyPath: story.path, story: story.name, section: section[1] }] : [];
  });
  const found={ root, visible, tests, stories, nativeSelections, warnings, untested: rule.untested, orphans: rule.orphans, excludedFixtureProjects: excluded, discoveryVisible: new Set([...visible].filter(path => discoveryFiles.has(path))) };
  Object.defineProperty(found,'workspace',{value:workspace});return found;
}

// STORY words, by the test name rule: a test path, a story path, a story name or a test file name.
// Returns {selected, unknown, untested}: untested holds the line of each named Story that has no test.
export function selectTests(found, words = [], { native = false } = {}) {
  if (!words.length) return { selected: [...found.tests], unknown: [], untested: [] };
  const selected = new Set(), unknown = [], untested = [], nativeSelections = new Map();
  for (const raw of words) {
    const word = raw.replace(/^\.\//, '');
    const hits = found.tests.filter(test => test.path === word || test.files?.includes(word) || test.storyPath === word || test.storyPaths?.includes(word) || test.story === word
      || word === '.' || (!word.startsWith('../') && word !== '..' && [test.path, ...(test.files ?? []), ...(test.storyPaths ?? []), test.storyPath].some(path => path?.startsWith(word.replace(/\/$/, '') + '/')))
      || basename(test.path, '.json') === word || test.storyPaths?.some(path => storyName(path) === word));
    const nativeHits = native ? (found.nativeSelections ?? []).filter(item => item.storyPath === word || item.story === word || word === '.' || (!word.startsWith('../') && word !== '..' && item.storyPath.startsWith(word.replace(/\/$/, '') + '/'))) : [];
    for (const item of nativeHits) nativeSelections.set(item.storyPath, item);
    const missing = hits.length || nativeHits.length ? [] : (found.untested ?? []).filter(item => item.storyPath === word || item.story === word);
    if (missing.length) untested.push(...missing.map(item => item.line));
    else if (!hits.length && !nativeHits.length) unknown.push(raw);
    for (const hit of hits) selected.add(hit);
  }
  const descriptors = [...nativeSelections.values()].map(item => {
    const links = [...item.section.matchAll(/\[[^\]]*\]\(([^)\s]+)#native-validation-profile-([^)\s]+)\)/g)];
    if (links.length !== 1) return {storyPath:item.storyPath,profileId:null,promptPath:null,reason:'Native Story owner link is missing or ambiguous.'};
    const promptPath = posix.normalize(posix.join(posix.dirname(item.storyPath),links[0][1]));
    try {
      if (!promptPath.endsWith('.prompt.md')) throw Error('Native owner must be a module prompt.');
      const captured = captureSource(found.root,{tests:[item.storyPath,promptPath]});
      return {storyPath:item.storyPath,promptPath,profileId:links[0][2],sourceReferences:captured.files};
    } catch (error) {
      // Workspace/source boundary failures retain their ordinary refusal exit.
      if (error instanceof PreflightError) throw error;
      return {storyPath:item.storyPath,promptPath,profileId:links[0][2],reason:error.message};
    }
  });
  return { selected: found.tests.filter(test => selected.has(test)), nativeSelections:descriptors, unknown, untested };
}

const refusal = (code, section, message, extra = {}) => ({ code, section, message, ...extra });
const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const show = value => { const text = JSON.stringify(value) ?? String(value); return text.length > 60 ? `${text.slice(0, 57)}...` : text; };
const plural = (count, word) => `${count} ${word}${count === 1 ? '' : 's'}`;
function range(min, max, unit = '') {
  const tail = unit ? ` ${unit}${(max ?? min) === 1 ? '' : 's'}` : '';
  if (min !== undefined && max !== undefined) return `${min} to ${max}${tail}`;
  return min !== undefined ? `at least ${min}${tail}` : `at most ${max}${tail}`;
}
const typeName = value => value === null ? 'null' : Array.isArray(value) ? 'array'
  : typeof value === 'number' ? (Number.isInteger(value) ? 'integer' : 'number') : typeof value;
const typeMatches = (value, type) => type === 'number' ? typeof value === 'number' : type === 'integer' ? Number.isInteger(value) : typeName(value) === type;
const article = type => /^[aeiou]/.test(type) ? `an ${type}` : `a ${type}`;

function unknownKeyword(schema) {
  if (!isObject(schema)) return null;
  for (const [key, value] of Object.entries(schema)) {
    if (!SCHEMA_RULES.has(key) && !SCHEMA_NOTES.has(key)) return key;
    if (key === 'properties' && isObject(value)) for (const child of Object.values(value)) { const found = unknownKeyword(child); if (found) return found; }
    if (key === 'items' || key === 'additionalProperties') { const found = unknownKeyword(value); if (found) return found; }
    if (key === 'oneOf' && Array.isArray(value)) for (const child of value) { const found = unknownKeyword(child); if (found) return found; }
  }
  return null;
}

const either = items => items.length > 1 ? `${items.slice(0, -1).join(', ')} or ${items.at(-1)}` : items[0];
const variantNames = variants => [...new Set(variants.map(variant => typeof variant?.type === 'string' ? (variant.type === 'null' ? 'null' : article(variant.type)) : 'another shape'))];

// The JSON Schema check of rule P9: every problem, not only the first. Pattern misses are warnings (JS and Python regexes differ).
// Only a common regex subset is evidence of cross-runtime membership. Other
// syntax may still be checked by the runtime, but cannot establish overlap.
function portablePattern(source, value) {
  // Character classes and end anchors differ outside this concrete domain.
  // Empty JS classes are also invalid in Python, even with ASCII input.
  if (/[^\x20-\x7e]/u.test(source) || /[^\x20-\x7e]/u.test(value) || /\[\^?\]/u.test(source)) return null;
  if (/\\(?:[1-9bBAZzGkpPuU]|x|c)|\(\?|[\s\S]*[\u0080-\uffff]/u.test(source)) return null;
  try { return new RegExp(source, 'u'); } catch { return null; }
}
function schemaRun(value, schema, tokens) {
  const problems = [], warnings = [], evidence = { miss: false, unknown: false };
  schemaProblems(value, schema, tokens, problems, warnings, evidence);
  return { problems, warnings, state: problems.length || evidence.miss ? 'miss' : evidence.unknown ? 'unknown' : 'match' };
}
function schemaProblems(value, schema, tokens, out, warnings, evidence = { miss: false, unknown: false }) {
  const at = rule => out.push({ tokens, rule });
  if (!isObject(schema)) return;
  if (Array.isArray(schema.oneOf)) {
    const runs = schema.oneOf.map(variant => schemaRun(value, variant, tokens));
    const fits = runs.filter(run => run.state === 'match').length;
    if (fits > 1) return at(`fits more than one of the allowed shapes (oneOf). Make the shapes exclusive.`);
    if (fits === 1) {
      if (runs.some(run => run.state === 'unknown')) evidence.unknown = true;
      return;
    }
    if (runs.some(run => run.state === 'unknown')) { evidence.unknown = true; return; }
    evidence.miss = true;
    const advisory = runs.find(run => !run.problems.length);
    if (advisory) { warnings.push(...advisory.warnings); return; }
    const same = schema.oneOf.findIndex(variant => typeof variant?.type === 'string' && typeMatches(value, variant.type));
    if (same >= 0) { out.push(...runs[same].problems); return; }
    return at(`is ${show(value)}. The prompt allows ${either(variantNames(schema.oneOf))}.`);
  }
  if (schema.type !== undefined) {
    const types = Array.isArray(schema.type) ? schema.type : [schema.type];
    if (!types.some(type => typeMatches(value, type))) return at(`is ${show(value)}. The prompt wants ${types.map(article).join(' or ')}.`);
  }
  if (Object.hasOwn(schema, 'const') && !isDeepStrictEqual(value, schema.const)) at(`is ${show(value)}. The prompt wants ${show(schema.const)}.`);
  if (Array.isArray(schema.enum) && !schema.enum.some(choice => isDeepStrictEqual(choice, value))) at(`is ${show(value)}. The prompt allows ${either(schema.enum.map(show))}.`);
  if (typeof value === 'number') {
    if ((schema.minimum !== undefined && value < schema.minimum) || (schema.maximum !== undefined && value > schema.maximum)) at(`is ${show(value)}. The prompt allows ${range(schema.minimum, schema.maximum)}.`);
    if (typeof schema.exclusiveMinimum === 'number' && value <= schema.exclusiveMinimum) at(`is ${show(value)}. The prompt wants more than ${schema.exclusiveMinimum}.`);
    if (typeof schema.exclusiveMaximum === 'number' && value >= schema.exclusiveMaximum) at(`is ${show(value)}. The prompt wants less than ${schema.exclusiveMaximum}.`);
    if (typeof schema.multipleOf === 'number' && schema.multipleOf > 0) {
      const ratio = value / schema.multipleOf;
      if (Math.abs(ratio - Math.round(ratio)) > 1e-9) at(`is ${show(value)}. The prompt wants a multiple of ${schema.multipleOf}.`);
    }
  }
  if (typeof value === 'string') {
    const length = [...value].length;
    if ((schema.minLength !== undefined && length < schema.minLength) || (schema.maxLength !== undefined && length > schema.maxLength)) {
      at(`has ${plural(length, 'character')}. The prompt allows ${range(schema.minLength, schema.maxLength, 'character')}.`);
    }
    if (typeof schema.pattern === 'string') {
      const pattern = portablePattern(schema.pattern, value);
      if (!pattern) evidence.unknown = true;
      const pointer = pointerOf(tokens);
      if (pattern && !pattern.test(value)) {
        evidence.miss = true;
        warnings.push(`input${pointer ? ` ${pointer}` : ''} is ${show(value)}. It does not match the pattern ${schema.pattern}, so the interpreter will likely refuse it.`);
      }
    }
  }
  if (Array.isArray(value)) {
    if ((schema.minItems !== undefined && value.length < schema.minItems) || (schema.maxItems !== undefined && value.length > schema.maxItems)) {
      at(`has ${plural(value.length, 'item')}. The prompt allows ${range(schema.minItems, schema.maxItems, 'item')}.`);
    }
    if (schema.uniqueItems === true && value.some((item, index) => value.findIndex(other => isDeepStrictEqual(other, item)) !== index)) at('has the same item twice. The prompt wants unique items.');
    if (isObject(schema.items)) for (const [index, item] of value.entries()) schemaProblems(item, schema.items, [...tokens, String(index)], out, warnings, evidence);
  }
  if (isObject(value)) {
    const count = Object.keys(value).length;
    if ((schema.minProperties !== undefined && count < schema.minProperties) || (schema.maxProperties !== undefined && count > schema.maxProperties)) {
      at(`has ${plural(count, 'field')}. The prompt allows ${range(schema.minProperties, schema.maxProperties, 'field')}.`);
    }
    for (const key of Array.isArray(schema.required) ? schema.required : []) if (!Object.hasOwn(value, key)) at(`has no ${show(key)}. The prompt requires it.`);
    const properties = isObject(schema.properties) ? schema.properties : {};
    for (const [key, child] of Object.entries(value)) {
      if (Object.hasOwn(properties, key)) schemaProblems(child, properties[key], [...tokens, key], out, warnings, evidence);
      else if (schema.additionalProperties === false) at(`has ${show(key)}. The prompt does not allow it.`);
      else if (isObject(schema.additionalProperties)) schemaProblems(child, schema.additionalProperties, [...tokens, key], out, warnings, evidence);
    }
  }
}

const hasReference = value => Array.isArray(value) ? value.some(hasReference)
  : isObject(value) && (Object.hasOwn(value, '$step_result') || Object.values(value).some(hasReference));
const pointerOf = tokens => tokens.map(token => `/${String(token).replace(/~/g, '~0').replace(/\//g, '~1')}`).join('');
const sectionOf = (base, tokens) => tokens.reduce((text, token) => /^\d+$/.test(token) ? `${text}[${token}]` : `${text}.${token}`, base);

// P9 on one step input: {refusals, warnings}. An unknown schema keyword skips that input with a warning.
export function checkInput(input, schema, index) {
  if (hasReference(input)) return { refusals: [], warnings: [] };
  const keyword = unknownKeyword(schema);
  if (keyword) return { refusals: [], warnings: [`steps[${index}] input was not checked here: the prompt schema uses "${keyword}". The interpreter still checks it.`] };
  const problems = [], warnings = [];
  schemaProblems(input, schema, [], problems, warnings);
  const seen = new Set();
  return {
    refusals: problems.filter(problem => { const key = `${pointerOf(problem.tokens)} ${problem.rule}`; if (seen.has(key)) return false; seen.add(key); return true; })
      .map(problem => refusal('invalid-input', sectionOf(`steps[${index}].input`, problem.tokens),
        `steps[${index}] input${problem.tokens.length ? ` ${pointerOf(problem.tokens)}` : ''} ${problem.rule}`, { step: index + 1 })),
    warnings: warnings.map(text => `steps[${index}] ${text}`),
  };
}

// The engine's executable schema subset (graph_runtime_protocol.py, _validate_schema_node, eae2202a).
const SCHEMA_ANNOTATIONS = new Set(['default', 'description', 'title', 'examples', 'format']);
const SCHEMA_FORBIDDEN = new Set(['$ref', '$dynamicRef', 'anyOf', 'allOf', 'not', 'if', 'then', 'else', 'contains',
  'unevaluatedProperties', 'patternProperties', 'propertyNames', 'contentEncoding']);
const NUMBER_FIELDS = ['type', 'enum', 'const', 'minimum', 'maximum', 'exclusiveMinimum', 'exclusiveMaximum', 'multipleOf'];
const SCHEMA_FIELDS = { null: ['type', 'enum', 'const'], boolean: ['type', 'enum', 'const'], string: ['type', 'enum', 'const', 'minLength', 'maxLength', 'pattern'],
  integer: NUMBER_FIELDS, number: NUMBER_FIELDS, array: ['type', 'items', 'enum', 'const', 'minItems', 'maxItems', 'uniqueItems'],
  object: ['type', 'properties', 'required', 'additionalProperties', 'enum', 'const', 'minProperties', 'maxProperties'] };
const COUNT_FIELDS = ['minLength', 'maxLength', 'minItems', 'maxItems', 'minProperties', 'maxProperties'];
const BOUND_FIELDS = ['minimum', 'maximum', 'exclusiveMinimum', 'exclusiveMaximum'];

function schemaRules(schema, pointer, out) {
  const add = (code, rule) => out.push({ code, pointer, rule });
  if (!isObject(schema) || !Object.keys(schema).length) return add('graph-schema-type-invalid', 'is not a schema. Use an object such as {"type": "string"}.');
  if (Array.isArray(schema.type)) {
    return add('graph-schema-type-list', `has a list of types (${schema.type.map(String).join(', ')}). Use "oneOf" with one schema for each type, for example {"oneOf": [{"type": "string"}, {"type": "null"}]}.`);
  }
  for (const key of Object.keys(schema)) if (SCHEMA_FORBIDDEN.has(key)) add('graph-schema-unsupported-keyword', `uses "${key}", which the interpreter does not support.`);
  if (Object.hasOwn(schema, 'oneOf')) {
    for (const key of Object.keys(schema)) if (key !== 'oneOf' && !SCHEMA_ANNOTATIONS.has(key) && !SCHEMA_FORBIDDEN.has(key)) add('graph-schema-unsupported-keyword', `has "${key}" next to "oneOf". Put it inside each oneOf schema.`);
    if (!Array.isArray(schema.oneOf) || !schema.oneOf.length) add('graph-schema-invalid', '"oneOf" must be a list of at least one schema.');
    else {
      schema.oneOf.forEach((variant, index) => schemaRules(variant, `${pointer}/oneOf/${index}`, out));
      if (schema.oneOf.some((variant, index) => schema.oneOf.findIndex(other => isDeepStrictEqual(other, variant)) !== index)) add('graph-schema-invalid', '"oneOf" has the same schema twice.');
    }
    return annotationRules(schema, add);
  }
  const type = schema.type;
  if (typeof type !== 'string' || !Object.hasOwn(SCHEMA_FIELDS, type)) {
    return add('graph-schema-type-invalid', `${type === undefined ? 'has no "type"' : `has the type ${show(type)}`}. Use null, boolean, string, integer, number, array or object, or "oneOf".`);
  }
  const allowed = new Set(SCHEMA_FIELDS[type]);
  for (const key of Object.keys(schema)) {
    if (!allowed.has(key) && !SCHEMA_ANNOTATIONS.has(key) && !SCHEMA_FORBIDDEN.has(key)) add('graph-schema-unsupported-keyword', `uses "${key}", which a ${type} schema cannot have. It can have ${[...allowed].join(', ')}.`);
  }
  if (type === 'array') {
    if (!Object.hasOwn(schema, 'items')) add('graph-schema-invalid', 'is an array with no "items". Add "items" with the schema of one item.');
    else schemaRules(schema.items, `${pointer}/items`, out);
  }
  if (type === 'object') {
    if (schema.additionalProperties !== false) add('graph-schema-open-object', 'needs "additionalProperties": false.');
    const properties = isObject(schema.properties) ? schema.properties : null, required = schema.required;
    if (!properties) add('graph-schema-invalid', 'needs "properties": an object with one schema for each field (it may be empty).');
    if (!Array.isArray(required)) add('graph-schema-invalid', 'needs "required": a list of the property names that must be present. It may be empty; a property that is not in the list is optional.');
    else {
      const wrong = required.find(name => typeof name !== 'string' || !properties || !Object.hasOwn(properties, name));
      if (wrong !== undefined) add('graph-schema-invalid', `has ${show(wrong)} in "required", but not in "properties".`);
      else if (new Set(required).size !== required.length) add('graph-schema-invalid', 'names a property twice in "required".');
    }
    for (const [name, child] of Object.entries(properties ?? {})) schemaRules(child, `${pointer}/properties/${pointerOf([name]).slice(1)}`, out);
  }
  for (const key of COUNT_FIELDS) if (Object.hasOwn(schema, key) && !(Number.isInteger(schema[key]) && schema[key] >= 0)) add('graph-schema-invalid', `"${key}" must be a whole number of 0 or more.`);
  for (const key of BOUND_FIELDS) if (Object.hasOwn(schema, key) && typeof schema[key] !== 'number') add('graph-schema-invalid', `"${key}" must be a number.`);
  if (Object.hasOwn(schema, 'multipleOf') && !(typeof schema.multipleOf === 'number' && schema.multipleOf > 0)) add('graph-schema-invalid', '"multipleOf" must be a number above 0.');
  if (Object.hasOwn(schema, 'pattern') && typeof schema.pattern !== 'string') add('graph-schema-invalid', '"pattern" must be a string.');
  if (Object.hasOwn(schema, 'uniqueItems') && typeof schema.uniqueItems !== 'boolean') add('graph-schema-invalid', '"uniqueItems" must be true or false.');
  if (Object.hasOwn(schema, 'enum')) {
    if (!Array.isArray(schema.enum) || !schema.enum.length) add('graph-schema-invalid', '"enum" must be a list of at least one value.');
    else if (schema.enum.some((item, index) => schema.enum.findIndex(other => isDeepStrictEqual(other, item)) !== index)) add('graph-schema-invalid', '"enum" has the same value twice.');
    else if (schema.enum.some(item => !typeMatches(item, type))) add('graph-schema-invalid', `"enum" has a value that is not ${article(type)}.`);
  }
  if (Object.hasOwn(schema, 'const') && !typeMatches(schema.const, type)) add('graph-schema-invalid', `"const" is not ${article(type)}.`);
  if (Object.hasOwn(schema, 'default') && !typeMatches(schema.default, type)) add('graph-schema-invalid', `"default" is not ${article(type)}.`);
  annotationRules(schema, add);
}

function annotationRules(schema, add) {
  for (const key of ['description', 'title', 'format']) if (Object.hasOwn(schema, key) && typeof schema[key] !== 'string') add('graph-schema-invalid', `"${key}" must be a string.`);
  if (Object.hasOwn(schema, 'examples') && !Array.isArray(schema.examples)) add('graph-schema-invalid', '"examples" must be a list.');
}

// Preserve numeric JSON spelling only for parsed prompt interfaces; ordinary callers supply JSON values.
const numberSources = new WeakMap();
function limitProblems(iface) {
  const out = [], keys = ['max_steps', 'max_model_calls'];
  const add = (code, pointer, rule, hint) => out.push({code,pointer,rule,hint});
  const shapeHint = 'Fix limits: use exactly "max_steps" and "max_model_calls", each an integer of at least 1.';
  if (!isObject(iface) || !Object.hasOwn(iface, 'limits')) {
    add('invalid-interface', '/limits', 'has no limits object.', 'Add "limits": {"max_steps": 1, "max_model_calls": 1}.');
    return out;
  }
  const limits = iface.limits;
  if (!isObject(limits)) {
    add('invalid-limits', '/limits', 'must be an object with exactly max_steps and max_model_calls.', shapeHint);
    return out;
  }
  for (const key of Object.keys(limits)) if (!keys.includes(key)) {
    add('invalid-limits', `/limits/${pointerOf([key]).slice(1)}`, 'is not an allowed limit field.', `Remove the extra limits key ${JSON.stringify(key)}; use exactly "max_steps" and "max_model_calls", each an integer of at least 1.`);
  }
  for (const key of keys) {
    const token = numberSources.get(limits)?.get(key);
    const integer = typeof limits[key] === 'number' && (token === undefined ? Number.isInteger(limits[key]) && limits[key] >= 1
      : /^-?(?:0|[1-9]\d*)$/.test(token) && BigInt(token) >= 1n);
    if (!Object.hasOwn(limits, key) || !integer) {
      add('invalid-limits', `/limits/${key}`, Object.hasOwn(limits, key) ? 'must be an integer JSON literal of at least 1.' : 'is missing; must be an integer JSON literal of at least 1.', `Fix limits.${key}: set an integer of at least 1 (for example 1), without a decimal point or exponent.`);
    }
  }
  return out;
}

// Every schema problem of one interface: entry input and result schemas (any root) and resource operation schemas (object root).
export function interfaceKindProblems(iface) {
  if (!isObject(iface)) return [{code:'invalid-interface',pointer:'',rule:'must be an object.'}];
  const kind = Object.hasOwn(iface, 'kind') ? iface.kind : 'full';
  if (!['full', 'partial', 'native-only'].includes(kind)) return [{code:'interface-kind-invalid',pointer:'/kind',rule:'must be full, partial or native-only.'}];
  if (kind === 'native-only' && (typeof iface.reason !== 'string' || !iface.reason.trim())) return [{code:'native-reason-missing',pointer:'/reason',rule:'must name the native effect that bound ports cannot fake (RUNBOOK §21).'}];
  return [];
}
export function interfaceSchemaProblems(iface) {
  const kindProblems = interfaceKindProblems(iface);
  if (kindProblems.length || iface?.kind === 'native-only') return kindProblems;
  const out = limitProblems(iface);
  if (Array.isArray(iface?.draft_gaps) && iface.draft_gaps.length) out.push({code:'interface-draft-incomplete',pointer:'/draft_gaps',rule:iface.draft_gaps.join('; ')});
  for (const [index, entry] of (Array.isArray(iface?.entries) ? iface.entries : []).entries()) {
    for (const key of ['input_schema', 'result_schema']) if (isObject(entry) && Object.hasOwn(entry, key)) schemaRules(entry[key], `/entries/${index}/${key}`, out);
  }
  for (const [index, resource] of (Array.isArray(iface?.resources) ? iface.resources : []).entries()) {
    for (const [opIndex, operation] of (Array.isArray(resource?.operations) ? resource.operations : []).entries()) {
      for (const key of ['arguments_schema', 'result_schema']) {
        if (!isObject(operation) || !Object.hasOwn(operation, key)) continue;
        const pointer = `/resources/${index}/operations/${opIndex}/${key}`;
        schemaRules(operation[key], pointer, out);
        if (isObject(operation[key]) && !Array.isArray(operation[key].type) && operation[key].type !== 'object' && !Object.hasOwn(operation[key], 'oneOf')) {
          out.push({ code: 'graph-schema-invalid', pointer, rule: 'must be an object schema ("type": "object").' });
        }
      }
    }
  }
  return out;
}

// The prompt file of an entry: {path, text, blocks, interface, error}.
export function readPrompt(root, visible, path,workspace=loadRuntimeWorkspace({root})) {
  workspace=boundedWorkspace(root,workspace);
  if(typeof path==='string')requireRuntimePath(workspace,{path,from:'Prompt'});
  if (typeof path !== 'string' || !path.endsWith('.prompt.md') || !visible.has(path)) return { path, error: 'entry-missing' };
  const rawText = sourceFilePort(root,visible,workspace).read({path}).content, prepared = preparedText(root,visible,path,rawText,'prompt',workspace), text = prepared.text, blocks = interfaceBlocks(text);
  const source = { path, rawText, text, blocks, references: prepared.references };
  if (!blocks.length) return { ...source, error: 'interface-missing' };
  if (blocks.length > 1) return { ...source, error: 'pdd-two-interfaces' };
  let value;
  try {
    value = JSON.parse(blocks[0][1], function(key, value, context) {
      if (typeof value === 'number' && context?.source !== undefined) {
        if (!numberSources.has(this)) numberSources.set(this, new Map());
        numberSources.get(this).set(key, context.source);
      }
      return value;
    });
  } catch (error) { return { ...source, error: 'invalid-json', detail: error.message }; }
  if (!isObject(value)) return { ...source, error: 'invalid-json', detail: 'The interface is not a JSON object.' };
  return { ...source, interface: value, prose: proseSha256(text) };
}

// Drafts may run; until the server takes them, its refusal gets this plain text.
export const DRAFT_SERVER_TEXT = 'The server does not run draft prompts yet. Approve the prompt first, or wait for the server update.';
const draftStaleHint = path => `pdd: ${path} is a draft whose text changed after its hash was filled. Run pdd test --fill-hash.`;
export const STALE_HINT = 'the text changed after approval: set status to draft, run pdd test --fill-hash, ask the person';
export const staleHint = `pdd: ${STALE_HINT}.`;
const PROMPT_MESSAGES = {
  'entry-missing': path => `${path} is not a Git-visible *.prompt.md file.`,
  'interface-missing': path => `${path} has no Runtime interface block. Run pdd interface draft ${/^[A-Za-z0-9_./-]+$/.test(path) ? path : "'" + path.replaceAll("'", "'\\''") + "'"}.`,
  'pdd-two-interfaces': path => `${path} has more than one Runtime interface block. Keep one.`,
  'invalid-json': path => `The Runtime interface of ${path} is not valid JSON.`,
};

// Rule P7 for one prompt. Returns null or a refusal (without the step).
export function promptRefusal(prompt, section) {
  if (prompt.error) return refusal(prompt.error, section, PROMPT_MESSAGES[prompt.error](prompt.path));
  const kindProblems = interfaceKindProblems(prompt.interface);
  if (kindProblems.length) return refusal(kindProblems[0].code, section, `${prompt.path} ${kindProblems[0].rule}`);
  const status = prompt.interface.status;
  if (status !== 'approved' && status !== 'draft') {
    return refusal('interface-unapproved', section, `${prompt.path} has status ${show(status)}. Use "draft" or "approved".`);
  }
  if (prompt.interface.prose_sha256 !== prompt.prose) {
    return status === 'draft' ? refusal('interface-stale', section, `${prompt.path} has a prose_sha256 that is not current.`, { hint: draftStaleHint(prompt.path) })
      : refusal('interface-stale', section, `${prompt.path} changed after its interface was approved.`, { hint: staleHint });
  }
  return null;
}

function numbersIn(text) {
  const numbers = [];
  for (const match of text.matchAll(/\d+(?:,\d{3})*(?:\.\d+)?/g)) {
    const before = text.slice(0, match.index);
    const negative = before.endsWith('-') && !/[\w.]-$/.test(before);
    numbers.push({ index: match.index, end: match.index + match[0].length, text: `${negative ? '-' : ''}${match[0]}`, value: Number(match[0].replace(/,/g, '')) * (negative ? -1 : 1) });
  }
  return numbers;
}

const REVIEW_FILE = 'pdd-numeric-reviews.json';
const REVIEW_KEYS = ['test_path','test_sha256','step_id','criterion_id','target','path','value','reason'];
function validNumericReview(row) {
  return isObject(row) && Object.keys(row).length === REVIEW_KEYS.length && REVIEW_KEYS.every(key => Object.hasOwn(row,key))
    && ['test_path','step_id','criterion_id','target','path','test_sha256','reason'].every(key => typeof row[key] === 'string')
    && row.test_path.endsWith('.json') && !row.test_path.startsWith('/') && posix.normalize(row.test_path) === row.test_path
    && !row.test_path.split('/').includes('..') && /^[a-f0-9]{64}$/i.test(row.test_sha256)
    && !!row.step_id.trim() && !!row.criterion_id.trim() && ['result','error'].includes(row.target)
    && (row.path === '' || row.path.startsWith('/')) && Number.isFinite(row.value)
    && !!row.reason.trim() && row.reason.length <= 1000 && !/[\r\n]/.test(row.reason);
}
function numericReviews(root, found, warnings) {
  const path = join(root, REVIEW_FILE), stat = statOf(path);
  if (!stat) return [];
  const ignore = () => { warnings.push(`Warning: ${REVIEW_FILE} is invalid, unreadable or not a Git-visible regular file; its numeric reviews are ignored.`); return []; };
  if (!found.visible.has(REVIEW_FILE) || !stat.isFile() || stat.isSymbolicLink() || stat.size > 16n * 1024n) return ignore();
  let fd;
  try {
    fd = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW);
    const actual = fstatSync(fd);
    if (!actual.isFile() || actual.size > 16 * 1024) return ignore();
    const source = readFileSync(fd,'utf8');
    if (Buffer.byteLength(source) > 16 * 1024) return ignore();
    const data = JSON.parse(source);
    if (!isObject(data) || Object.keys(data).length !== 2 || data.schema_version !== 'pdd.numeric-reviews.v1'
      || !Array.isArray(data.reviews) || data.reviews.length > 100 || !data.reviews.every(validNumericReview)) return ignore();
    return data.reviews;
  } catch { return ignore(); } finally { if (fd !== undefined) closeSync(fd); }
}
const quantityWords = text => String(text ?? '').replace(/([a-z])([A-Z])/g,'$1 $2').toLowerCase().split(/[^a-z]+/).filter(Boolean);
const aggregateWords = new Set(['total','combined','cumulative','aggregate','sum','cap','limit','budget']);

const namedQuantity = text => {
  const words = quantityWords(text);
  const names = new Set(words.map(word => /^(scores?|points?)$/.test(word) ? 'score'
    : /^(moves?|turns?)$/.test(word) ? 'moves' : /^seeds?$/.test(word) ? 'seed' : null).filter(Boolean));
  return names.size === 1 ? [...names][0] : null;
};
function numberQuantity(text, number) {
  // Prefer an immediately following unit ("30 moves"), then a preceding
  // subject ("score is 30"). Do not cross clauses or another number.
  const after = /^\s*([a-z]+)/i.exec(text.slice(number.end));
  const following = after && namedQuantity(after[1]);
  if (following) return following;
  const before = /([a-z]+)(?:\s+(?:is|of|equals|at|the|fixed))*\s*$/i.exec(text.slice(0, number.index));
  return before ? namedQuantity(before[1]) : null;
}

// A number can be a component of the criterion's quantity, rather than a typo.
export function numberWarnings(doc, { testPath, testSha, reviews = [] } = {}) {
  const texts = new Map((Array.isArray(doc?.criteria) ? doc.criteria : []).filter(isObject).map(item => [item.id, item.text]));
  const steps = Array.isArray(doc?.steps) ? doc.steps : [], allChecks = steps.flatMap(step => Array.isArray(step?.checks) ? step.checks : []);
  const warnings = new Set();
  for (const [stepIndex,step] of steps.entries()) for (const [checkIndex,check] of (Array.isArray(step?.checks) ? step.checks : []).entries()) {
    const text = texts.get(check?.criterion_id);
    if (!isObject(check) || typeof text !== 'string' || !['result','error'].includes(check.target)) continue;
    const values = check.op === 'one_of' && Array.isArray(check.value) ? check.value : check.op === 'equals' ? [check.value] : [];
    const allNumbers = numbersIn(text), quantity = namedQuantity(check.path);
    const associated = allNumbers.map(item => ({ ...item, quantity: numberQuantity(text, item) }));
    const matching = associated.filter(item => quantity && item.quantity === quantity);
    const found = quantity && matching.length ? matching
      : quantity && associated.length && associated.every(item => item.quantity) ? [] : associated;
    const leaf = quantityWords(String(check.path ?? '').split('/').at(-1));
    const sameQuantity = leaf.some(word => aggregateWords.has(word)) && quantityWords(text).some(word => aggregateWords.has(word));
    const members = /\bacross\b([\s\S]*)/i.exec(text)?.[1] ?? '';
    const namedComponent = !sameQuantity && /\b(?:combined|cumulative|total|aggregate|sum|across)\b/i.test(text)
      && quantityWords(check.path).some(word => word.length > 2 && quantityWords(members).includes(word));
    for (const value of values) {
      if (typeof value !== 'number' || !found.length || found.some(item => item.value === value)) continue;
      const closest = found.reduce((best,item) => Math.abs(item.value-value) < Math.abs(best.value-value) ? item : best);
      if (Math.abs(closest.value-value) > 0.1 * Math.max(Math.abs(closest.value),Math.abs(value))) continue;
      const companion = allChecks.some(peer => isObject(peer) && peer !== check && peer.criterion_id === check.criterion_id
        && peer.target === check.target && peer.path !== check.path && peer.op === 'equals' && peer.value === closest.value);
      if (namedComponent || (!sameQuantity && !matching.length && companion)) continue;
      if (reviews.some(row => validNumericReview(row) && row.test_path === testPath && row.test_sha256.toLowerCase() === testSha
        && row.step_id === step.step_id && row.criterion_id === check.criterion_id && row.target === check.target && row.path === check.path && row.value === value)) continue;
      const location = `${testPath ?? 'test'} steps[${stepIndex}].checks[${checkIndex}] (${check.target} ${check.path})`;
      warnings.add(`Warning: possible numeric mismatch at ${location}: expected ${value}; ${doc.story_path ?? 'criterion text'} ${check.criterion_id} contains ${closest.text}. These may be different quantities. Confirm against the Story and prompt; retain a correct expected value. Record a scoped rationale in ${REVIEW_FILE} if needed (RUNBOOK §4).`);
    }
  }
  return [...warnings];
}

const stepCount = doc => Array.isArray(doc?.steps) ? doc.steps.length : 0;
// Leave room for the whole call graph; the budget is a ceiling, not a charge.
export const defaultMaxCalls = doc => Math.min(1000, Math.max(18, stepCount(doc) * 12));

function firstDifference(testTexts, storyTexts) {
  const left = [...storyTexts];
  for (const text of testTexts) {
    const index = left.indexOf(text);
    if (index < 0) return `The test has this criterion, but the story does not: "${text}"`;
    left.splice(index, 1);
  }
  return `The story has this criterion, but the test does not: "${left[0]}"`;
}

// Coverage is structural. A negative assertion with an exact calls/world check is checkable.
const exactCheck = check => EXACT_OPS.has(check?.op) || (isObject(check) && Object.hasOwn(check, 'html') && check.op === 'exists');
const ordinaryInexactCheck = check => isObject(check) && ['exists','contains'].includes(check.op)
  && ['result','world','calls','error'].includes(check.target) && typeof check.path === 'string'
  && (check.path === '' || check.path.startsWith('/')) && !/~(?![01])/.test(check.path)
  && (check.op !== 'contains' || Object.hasOwn(check,'value'));
function criterionPlan(doc, story) {
  if (!Array.isArray(doc?.criteria) || !doc.criteria.length || !Array.isArray(doc.steps)
    || Object.hasOwn(doc, 'criteria_scope')
    || (Object.hasOwn(doc,'check_exemptions') && !(Array.isArray(doc.check_exemptions) && !doc.check_exemptions.length))
    || doc.criteria.some(item => !isObject(item) || !isDeepStrictEqual(Object.keys(item).sort(),['id','text']) || typeof item.id !== 'string' || !item.id || typeof item.text !== 'string')
    || new Set(doc.criteria.map(item => item.id)).size !== doc.criteria.length) return null;
  const remaining = [...story], criteria = doc.criteria.map(item => ({...item}));
  for (const item of criteria) {
    const index = remaining.indexOf(item.text);
    if (index < 0) return null;
    remaining.splice(index, 1);
  }
  const assigned = new Set(), exact = new Set();
  const declared = new Set(doc.criteria.map(item=>item.id));
  for (const step of doc.steps) for (const check of Array.isArray(step?.checks) ? step.checks : []) {
    if (!isObject(check) || !declared.has(check.criterion_id)) return null;
    assigned.add(check?.criterion_id);
    if (exactCheck(check)) exact.add(check.criterion_id);
  }
  for (const step of doc.steps) for (const check of Array.isArray(step?.checks) ? step.checks : []) {
    if (!exact.has(check.criterion_id) && !ordinaryInexactCheck(check)) return null;
  }
  const not_checked = criteria.filter(item => !exact.has(item.id)).map(item => ({criterion_id:item.id,text:item.text,
    reason:assigned.has(item.id) ? 'no exact check is assigned' : 'no check is assigned'}));
  const unmatched = [...doc.criteria.map(item => item.text)], used = new Set(criteria.map(item => item.id));
  for (const [index, text] of story.entries()) {
    const at = unmatched.indexOf(text);
    if (at >= 0) { unmatched.splice(at, 1); continue; }
    const base = `ac-${index + 1}`; let id = base;
    for (let n = 2; used.has(id); n++) id = `${base}-${n}`;
    used.add(id); criteria.push({id,text});
    not_checked.push({criterion_id:id,text,reason:'the test has no criterion for this Story item'});
  }
  return {criteria,not_checked,checked:criteria.length-not_checked.length};
}

// This applies to authored/effective input before capture adds automatic exemptions.
function partialTestRefusal(doc) {
  if (Object.hasOwn(doc, 'criteria_scope') || (Object.hasOwn(doc, 'check_exemptions') && !(Array.isArray(doc.check_exemptions) && !doc.check_exemptions.length))) {
    return refusal('pdd-partial-test', Object.hasOwn(doc, 'criteria_scope') ? 'criteria_scope' : 'check_exemptions', 'In the beta a test checks the whole story. Remove criteria_scope and check_exemptions.');
  }
  return null;
}

function capturedCriterionPlan(doc, story, path) {
  let broken = partialTestRefusal(doc);
  const plan = broken ? null : criterionPlan(doc, story);
  if (!broken && !story.length) broken = refusal('story-criteria-missing', 'story_path', `${doc.story_path} has no numbered "## Acceptance criteria" list.`);
  if (!broken && !plan) {
    const testTexts = doc.criteria.map(item => item.text).sort(), storyTexts = [...story].sort();
    broken = !isDeepStrictEqual(testTexts, storyTexts)
      ? refusal('story-criterion-mismatch', 'criteria', firstDifference(testTexts, storyTexts))
      : refusal('criterion-needs-exact-check', 'criteria', 'The checks do not establish valid criterion coverage.');
  }
  if (!broken && !plan.checked) broken = refusal('unchecked-criteria', 'criteria', 'No criterion has an exact check.',
    {hint:'Add an exact result, world or call-count check for an observable criterion.'});
  if (broken) throw Object.assign(new PreflightError(4, `${path}: ${broken.message}`), broken,
    {message:`${path}: ${broken.message}`,hint:broken.hint ?? 'Fix the test criterion text or partial-test metadata, then run the selection again.'},
    plan ? {not_checked:plan.not_checked,criteria_total:plan.criteria.length} : {});
  return plan;
}

// The schema rules of a prompt and of the prompts it calls, all at once (cached per prompt).
export function promptSchemaRefusals(root, found, prompt, prompts, seen = new Set()) {
  if (!prompt || seen.has(prompt.path)) return [];
  seen.add(prompt.path);
  if (prompt.error) return [{ ...promptRefusal(prompt, 'interface'), path: prompt.path }];
  if (!prompt.interface) return [];
  prompt.schemaIssues ??= interfaceSchemaProblems(prompt.interface).map(problem =>
    refusal(problem.code, problem.pointer, `${prompt.path} ${problem.pointer} ${problem.rule}`, {path:prompt.path, ...(problem.hint ? {hint:problem.hint} : {})}));
  const called = (Array.isArray(prompt.interface.calls) ? prompt.interface.calls : []).map(call => call?.target).filter(target => typeof target === 'string');
  const statusProblems = ['draft', 'approved'].includes(prompt.interface.status) ? [] : [{ ...promptRefusal(prompt, 'interface'), path: prompt.path }];
  return [...statusProblems, ...prompt.schemaIssues, ...called.flatMap(target => {
    if (!prompts.has(target)) prompts.set(target, readPrompt(root, found.visible, target,found.workspace));
    return promptSchemaRefusals(root, found, prompts.get(target), prompts, seen);
  })];
}

// A refusal that discovery alone proves: a conflict, an unreadable or invalid file, a file over the upload limit,
// or a story_path that names another Story than the test name rule matched.
export function discoveryRefusal(test) {
  if (test.error) return refusal('invalid-document', 'scenario', test.error,
    {hint:'Fix the named test file, make it readable, or keep one file for the Story.'});
  if (test.storyPath && isObject(test.doc) && typeof test.doc.story_path === 'string' && test.doc.story_path !== test.storyPath) {
    return refusal('pdd-story-mismatch', 'story_path', `${test.path} is the test of ${test.storyPath} by its name, but its story_path names ${test.doc.story_path}. Make them agree.`);
  }
  return null;
}

const criterionShape = item => isObject(item) && isDeepStrictEqual(Object.keys(item).sort(), ['id','text'])
  && typeof item.id === 'string' && !!item.id && typeof item.text === 'string' && !!item.text;
const stepShape = step => isObject(step) && !Object.keys(step).some(key=>!STEP_KEYS.has(key))
  && ['step_id','entry_path','operation','input','checks'].every(key=>Object.hasOwn(step,key))
  && ['step_id','entry_path','operation'].every(key=>typeof step[key]==='string'&&!!step[key]);
const checkShape = check => isObject(check) && ['criterion_id','target','path','op'].every(key=>Object.hasOwn(check,key));
function documentRefusal(doc,path) {
  if (!isObject(doc)) return refusal('invalid-document', 'scenario', `${path} is not a JSON object.`);
  const missing = REQUIRED_KEYS.filter(key => !Object.hasOwn(doc, key)), extra = Object.keys(doc).filter(key => !TOP_KEYS.has(key));
  if (missing.length) return refusal('invalid-document', 'scenario', `The test has no ${missing.map(key => `"${key}"`).join(', ')}.`);
  if (extra.length) return refusal('invalid-document', 'scenario', `The test has keys the interpreter does not know: ${extra.map(key => `"${key}"`).join(', ')}.`);
  if (doc.schema_version !== TEST_SCHEMA) return refusal('invalid-document', 'schema_version', `schema_version must be "${TEST_SCHEMA}".`);
  return null;
}

export function scenarioShapeRefusal(doc,path) {
  const broken=documentRefusal(doc,path);if(broken)return broken;
  if (!Array.isArray(doc.criteria)||!doc.criteria.length) return refusal('invalid-criterion','criteria','The test has no criteria.');
  const ids=new Set();
  for (const [index,item] of doc.criteria.entries()) {
    if(!criterionShape(item))return refusal('invalid-criterion',`criteria[${index}]`,'Each criterion has only a nonempty "id" and "text".');
    if(ids.has(item.id))return refusal('duplicate-criterion',`criteria[${index}]`,`The criterion ID ${item.id} is used twice.`);
    ids.add(item.id);
  }
  if(!Array.isArray(doc.steps)||!doc.steps.length)return refusal('missing-steps','steps','The test has no steps.');
  for(const [index,step] of doc.steps.entries()) {
    const section=`steps[${index}]`;
    if(!stepShape(step))return refusal('invalid-step',section,'A step has step_id, entry_path, operation, input and checks.');
    if(Object.hasOwn(step,'model')&&(typeof step.model!=='string'||!step.model.trim()))return refusal('invalid-step-model',`${section}.model`,'A step model must be a model name (a string).');
    if(!Array.isArray(step.checks))return refusal('invalid-check',`${section}.checks`,'checks must be a list.');
    for(const [at,check] of step.checks.entries()) {
      if(!checkShape(check))return refusal('invalid-check',`${section}.checks[${at}]`,'A check has criterion_id, target, path and op.');
      if(!ids.has(check.criterion_id))return refusal('unknown-criterion',`${section}.checks[${at}]`,`The check names ${show(check.criterion_id)}, which is not a criterion ID.`);
    }
  }
  return null;
}

function checkTest(root, found, test, prompts) {
  let doc = test.doc;
  if (!test.error && isObject(doc)) {
    const prepared = preparedText(root,found.visible,test.path,readText(root,test.path),'scenario');
    try { doc = JSON.parse(prepared.text); } catch { /* Preserve ordinary malformed scenario handling. */ }
  }
  if (test.error) return discoveryRefusal(test);
  const shape=documentRefusal(doc,test.path);if(shape)return shape;
  if (typeof doc.story_path !== 'string' || !doc.story_path) return refusal('pdd-no-story', 'story_path', 'The test has no story_path. Name its story, for example "user_stories/<story>.md".');
  if (!found.visible.has(doc.story_path)) return refusal('story-missing', 'story_path', `${doc.story_path} is not a Git-visible file.`);
  if (test.storyPath && doc.story_path !== test.storyPath) return discoveryRefusal({ ...test, doc });
  const partial = partialTestRefusal(doc); if (partial) return partial;
  if (!Array.isArray(doc.criteria) || !doc.criteria.length) return refusal('invalid-criterion', 'criteria', 'The test has no criteria.');
  const ids = new Set();
  for (const [index, item] of doc.criteria.entries()) {
    if (!criterionShape(item)) {
      return refusal('invalid-criterion', `criteria[${index}]`, 'Each criterion has only a nonempty "id" and "text".');
    }
    if (ids.has(item.id)) return refusal('duplicate-criterion', `criteria[${index}]`, `The criterion ID ${item.id} is used twice.`);
    ids.add(item.id);
  }
  const story = storyCriteria(readText(root, doc.story_path));
  if (!story.length) return refusal('story-criteria-missing', 'story_path', `${doc.story_path} has no numbered "## Acceptance criteria" list.`);
  const testTexts = doc.criteria.map(item => item.text).sort(), storyTexts = [...story].sort();
  if (!isDeepStrictEqual(testTexts, storyTexts) && !criterionPlan(doc, story)) return refusal('story-criterion-mismatch', 'criteria', firstDifference(testTexts, storyTexts));
  if (!Array.isArray(doc.steps) || !doc.steps.length) return refusal('missing-steps', 'steps', 'The test has no steps.');
  const exact = new Set(), inputIssues = [];
  for (const [index, step] of doc.steps.entries()) {
    const section = `steps[${index}]`, at = { step: index + 1 };
    if (!stepShape(step)) {
      return refusal('invalid-step', section, 'A step has step_id, entry_path, operation, input and checks.', at);
    }
    if (Object.hasOwn(step, 'model') && (typeof step.model !== 'string' || !step.model.trim())) {
      return refusal('invalid-step-model', `${section}.model`, 'A step model must be a model name (a string).', at);
    }
    if (!prompts.has(step.entry_path)) prompts.set(step.entry_path, readPrompt(root, found.visible, step.entry_path,found.workspace));
    const prompt = prompts.get(step.entry_path), broken = promptRefusal(prompt, section);
    if (broken) return { ...broken, ...at };
    const schemaIssues = promptSchemaRefusals(root, found, prompt, prompts);
    if (schemaIssues.length) return schemaIssues;
    const entry = (Array.isArray(prompt.interface.entries) ? prompt.interface.entries : []).find(item => item?.operation === step.operation);
    const native = [...prompts.values()].some(item => item.interface?.kind === 'native-only');
    if (!entry && !native) return refusal('entry-operation-missing', section, `${step.entry_path} has no operation "${step.operation}".`, at);
    const errorStep = Object.hasOwn(step, 'expected_error');
    if (!native && errorStep && !(Array.isArray(entry.errors) && entry.errors.includes(step.expected_error))) {
      return refusal('pdd-unknown-error', `${section}.expected_error`, `"${step.expected_error}" is not in the errors of ${step.operation} in ${step.entry_path}.`, at);
    }
    if (!Array.isArray(step.checks)) return refusal('invalid-check', `${section}.checks`, 'checks must be a list.', at);
    let errorChecks = 0;
    for (const [checkIndex, check] of step.checks.entries()) {
      if (!checkShape(check)) {
        return refusal('invalid-check', `${section}.checks[${checkIndex}]`, 'A check has criterion_id, target, path and op.', at);
      }
      if (!ids.has(check.criterion_id)) return refusal('unknown-criterion', `${section}.checks[${checkIndex}]`, `The check names ${show(check.criterion_id)}, which is not a criterion ID.`, at);
      if (EXACT_OPS.has(check.op) || (Object.hasOwn(check, 'html') && check.op === 'exists')) exact.add(check.criterion_id);
      if (check.target === 'error' && check.path === '/code' && check.op === 'equals' && check.value === step.expected_error) errorChecks += 1;
    }
    if (errorStep && errorChecks === 0) {
      return refusal('missing-error-check', `${section}.checks`, `An error step needs one check: target "error", path "/code", op "equals", value "${step.expected_error}".`, at);
    }
    if (!native) inputIssues.push(...checkInput(step.input, entry.input_schema, index).refusals);
  }
  if (inputIssues.length) return inputIssues;
  for (const step of doc.steps) for (const check of step.checks) {
    if (!exact.has(check.criterion_id) && !ordinaryInexactCheck(check)) return refusal('criterion-needs-exact-check', 'criteria',
      `The checks for ${check.criterion_id} do not establish valid criterion coverage.`, {hint:'Fix the check operation, target and JSON pointer before checking this test.'});
  }
  if (!exact.size) return refusal('unchecked-criteria', 'criteria', 'No criterion has an exact check.',
    {hint:'Add an exact result, world or call-count check for an observable criterion.'});
  return null;
}

// Rules P1-P10 for the selected tests. Returns rows and warnings; never throws for a test problem.
export function preflight({ root, found, selected,workspace=found.workspace??loadRuntimeWorkspace({root}) }) {
  found={...found,workspace};for(const test of selected)requireRuntimePath(workspace,{path:test.path,from:'Selected test'});
  const warnings = [];
  const reviews = numericReviews(root, found, warnings);
  const rows = selected.map(test => {
    const prompts = new Map();
    // Discover identity independently of validation: an early criterion error or
    // stale caller must not make a reachable native-only declaration executable.
    const visit = path => {
      if (typeof path !== 'string' || prompts.has(path)) return;
      const prompt = readPrompt(root, found.visible, path, workspace);
      prompts.set(path, prompt);
      for (const call of Array.isArray(prompt.interface?.calls) ? prompt.interface.calls : []) visit(call?.target);
    };
    let refused, plan, testSha = null;
    try {
      for (const step of Array.isArray(test.doc?.steps) ? test.doc.steps : []) visit(step?.entry_path);
      refused = checkTest(root, found, test, prompts);
      const nativeProblems = [...prompts.values()].filter(prompt => prompt.interface?.kind === 'native-only')
        .map(prompt => promptRefusal(prompt,'interface')).filter(Boolean);
      if (nativeProblems.length) refused = [...(refused ? [refused].flat() : []),...nativeProblems];
      if (!refused || refused.code === 'unchecked-criteria') {
        plan = criterionPlan(test.doc, storyCriteria(readText(root, test.doc.story_path)));
      }
      if (!refused && reviews.length) testSha = sha256(readFileSync(join(root,test.path)));
    } catch (error) {
      if (!(error instanceof PreflightError && error.exitCode === 4) && !['ENOENT','EACCES','EPERM','EISDIR'].includes(error.code)) throw error;
      refused = refusal(error.code ?? 'source-unavailable', 'source', error.message,
        {hint:'Restore the named dependency, make it readable, or correct its declared path.'});
    }
    const row = { test: test.path, story: test.story, title: test.title, refusals: refused ? [refused].flat() : [], warnings: numberWarnings(test.doc, { testPath: test.path, testSha, reviews }),
      max_calls: defaultMaxCalls(test.doc), steps: Array.isArray(test.doc?.steps) ? test.doc.steps : [],
      criteria_total: plan?.criteria.length ?? (Array.isArray(test.doc?.criteria) ? test.doc.criteria.length : 0),
      ...(plan?.not_checked.length ? {not_checked:plan.not_checked} : {}), draft: false };
    row.native_only = [...prompts.values()].filter(item => item.interface?.kind === 'native-only').map(item => ({path:item.path,reason:item.interface.reason}));
    row.draft = row.steps.some(step => prompts.get(step?.entry_path)?.interface?.status === 'draft');
    for (const [index, step] of row.steps.entries()) {
      const prompt = prompts.get(step?.entry_path), entry = prompt?.interface?.entries?.find?.(item => item?.operation === step?.operation);
      for (const text of entry ? checkInput(step.input, entry.input_schema, index).warnings : []) warnings.push(`Warning: ${test.path} ${text}`);
    }
    return row;
  });
  return { rows, warnings };
}

// The caller has parsed a root object. Keep surrounding whitespace and all
// string/token bytes; remove only JSON whitespace between tokens.
function compactInterface(body) {
  const start = body.indexOf('{'), end = body.lastIndexOf('}') + 1;
  let compacted = '', inString = false, escaped = false;
  for (const char of body.slice(start, end)) {
    if (inString) {
      compacted += char;
      if (escaped) escaped = false;
      else if (char === '\\') escaped = true;
      else if (char === '"') inString = false;
    } else if (char === '"') { inString = true; compacted += char; }
    else if (![' ', '\t', '\r', '\n'].includes(char)) compacted += char;
  }
  return body.slice(0, start) + compacted + body.slice(end);
}

// --fill-hash: fill draft hashes; optionally compact safe draft interfaces.
export function fillHashes({ root, files = gitFiles(root), compact = false,workspace=loadRuntimeWorkspace({root}) }) {
  workspace=boundedWorkspace(root,workspace);
  const result = { filled: [], current: [], refused: [], stale: [], warnings: [] };
  if (compact === true) result.compacted = [];
  for (const path of files) {
    if (!allowsRuntimePath(workspace,path) || !path.endsWith('.prompt.md') || !statOf(join(root, path))?.isFile()) continue;
    let text;try{text=filePort(root,new Set(files),true,workspace).read({path}).content;}catch(error){result.refused.push({path,message:error.message});continue;}
    const blocks = interfaceBlocks(text);
    try {
      preparedText(root,new Set(files),path,text,'prompt',workspace);
      if(workspace.configured){const pending=[path],seen=new Set(),port=sourceFilePort(root,new Set(files));
      for(let i=0;i<pending.length;i++){const owner=pending[i];if(seen.has(owner))continue;seen.add(owner);const content=owner===path?text:port.read({path:owner}).content;
        for(const raw of markdownContext(content)){const target=contextPath(raw,owner,new Set(files));if(target){requireRuntimePath(workspace,{path:target,from:owner,chain:[path]});pending.push(target);}}
        if(owner.endsWith('.prompt.md'))for(const block of interfaceBlocks(content)){let doc;try{doc=JSON.parse(block[1]);}catch{continue;}for(const call of doc.calls??[])if(typeof call?.target==='string'){requireRuntimePath(workspace,{path:call.target,from:owner,chain:[path]});pending.push(call.target);}}
      }}
    }
    catch (error) { result.refused.push({path,message:error.message}); continue; }
    if (!blocks.length) continue;
    if (blocks.length > 1) { result.refused.push({ path, message: `${path} has more than one Runtime interface block. Keep one.` }); continue; }
    const [start, end] = blocks[0].indices[1], body = blocks[0][1];
    let value;
    try { value = JSON.parse(body); } catch { result.refused.push({ path, message: `The Runtime interface of ${path} is not valid JSON.` }); continue; }
    if (!isObject(value)) { result.refused.push({ path, message: `The Runtime interface of ${path} is not a JSON object.` }); continue; }
    if (!Object.hasOwn(value, 'status')) {
      if (Object.hasOwn(value, 'prose_sha256')) result.refused.push({ path, message: `The Runtime interface of ${path} has no status. Add "status": "draft" and run pdd test --fill-hash again.` });
      else result.warnings.push({ path, message: `The Runtime interface of ${path} has no status and no prose_sha256, so pdd skipped it. If this is a prompt you check, add "status": "draft" and run pdd test --fill-hash again.` });
      continue;
    }
    const hash = proseSha256(text);
    if (value.status === 'approved') { (value.prose_sha256 === hash ? result.current : result.stale).push({ path }); continue; }
    if (value.status !== 'draft') { result.refused.push({ path, message: `${path} has status ${show(value.status)}. Use "draft" until the person approves it.` }); continue; }
    if (!Object.hasOwn(value, 'prose_sha256')) { result.refused.push({ path, message: `${path} has no "prose_sha256" key. Add "prose_sha256": "" to its Runtime interface.` }); continue; }
    const current = value.prose_sha256 === hash;
    let changed = body;
    if (!current) {
      const key = /("prose_sha256"\s*:\s*)"(?:[^"\\]|\\.)*"/g;
      changed = [...body.matchAll(key)].length === 1 ? body.replace(key, `$1"${hash}"`) : null;
      let same = false;
      try { same = changed !== null && isDeepStrictEqual(JSON.parse(changed), { ...value, prose_sha256: hash }); } catch { same = false; }
      if (!same) { result.refused.push({ path, message: `pdd could not fill "prose_sha256" in ${path}. Make it one string value, for example "prose_sha256": "".` }); continue; }
    }
    const compacted = compact === true ? compactInterface(changed) : changed;
    const whitespaceChanged = compacted !== changed;
    changed = compacted;
    const next = text.slice(0, start) + changed + text.slice(end);
    if (proseSha256(next) !== hash) { result.refused.push({ path, message: `pdd could not fill "prose_sha256" in ${path} without a change to its text.` }); continue; }
    if (next !== text) {
      requireRuntimePath(loadRuntimeWorkspace({root}),{path,from:'Hash destination'});
      const safe=filePort(root,new Set(files),true);
      if(safe.read({path}).content!==text)throw new PreflightError(5,`${path}: changed before hash write.`);
      writeFileSync(join(root, path), next);
    }
    (current ? result.current : result.filled).push({ path });
    if (whitespaceChanged) result.compacted.push({ path });
  }
  return result;
}

const SECRET_NAME = /^(?:\.env.*|auth\.json|credentials\.json|id_rsa|id_ed25519|id_ecdsa|id_dsa|\.npmrc|\.netrc|\.git-credentials|\.pypirc|.+\.(?:pem|key|p12|pfx|keystore|tfstate|tfvars))$/;
const SECRET_PART = new Set(['secrets', '.ssh', '.codex', '.terraform', '.aws']);
export const isSecretPath = path => SECRET_NAME.test(basename(path)) || path.split('/').some(part => SECRET_PART.has(part))
  || /(?:^|\/)\.docker\/config\.json$/.test(path)
  || /(?:^|\/)(?:\.pdd\/agents\.json|\.config\/pdd\/agents\.json)$/i.test(path);

function octal(header, offset, length, value) { header.write(`${value.toString(8).padStart(length - 1, '0')}\0`, offset, length, 'latin1'); }
function tarHeader(name, size, type) {
  const header = Buffer.alloc(512);
  header.write(name, 0, 100, 'utf8');
  octal(header, 100, 8, 0o600); octal(header, 108, 8, 0); octal(header, 116, 8, 0);
  octal(header, 124, 12, size); octal(header, 136, 12, 0);
  header.fill(0x20, 148, 156);
  header.write(type, 156, 1, 'latin1');
  header.write('ustar\0', 257, 6, 'latin1'); header.write('00', 263, 2, 'latin1');
  octal(header, 329, 8, 0); octal(header, 337, 8, 0);
  let sum = 0;
  for (const byte of header) sum += byte;
  header.write(`${sum.toString(8).padStart(6, '0')}\0 `, 148, 8, 'latin1');
  return header;
}
const pad = size => Buffer.alloc((512 - (size % 512)) % 512);
function paxRecord(key, value) {
  const body = ` ${key}=${value}\n`;
  let length = Buffer.byteLength(body) + 1;
  while (Buffer.byteLength(`${length}${body}`) !== length) length += 1;
  return Buffer.from(`${length}${body}`, 'utf8');
}

// A deterministic ustar archive: Git names, mode 0600, mtime 0, PAX path for long or non-ASCII names.
export function tarFiles(entries) {
  const parts = [];
  for (const { path, bytes } of entries) {
    let name = path;
    if (Buffer.byteLength(path) > 100 || /[^\x20-\x7e]/.test(path)) {
      const record = paxRecord('path', path);
      parts.push(tarHeader('PaxHeader', record.length, 'x'), record, pad(record.length));
      name = path.replace(/[^\x20-\x7e]/g, '_').slice(-100);
    }
    parts.push(tarHeader(name, bytes.length, '0'), bytes, pad(bytes.length));
  }
  parts.push(Buffer.alloc(1024));
  return Buffer.concat(parts);
}

export const formatSize = bytes => bytes < 1024 ? `${bytes} bytes` : bytes < 1024 * 1024 ? `${Math.round(bytes / 1024)} KB` : `${(bytes / 1048576).toFixed(1)} MB`;

// Selection is metadata, not a rewritten project: every archive name remains authored in the repo.
const SOURCE_CONFIG = 'pdd-source.json';
const sameStat = (a, b) => a && b && a.ino === b.ino && a.dev === b.dev && a.size === b.size && a.mtimeNs === b.mtimeNs && a.ctimeNs === b.ctimeNs;
const unstableSource = Symbol('unstable source');
const sourceProblem = (from, path, reason) => Object.assign(new PreflightError(4, `${from}: ${path}${reason.startsWith(':') ? '' : ' '}${reason}`),
  {selection:from === SOURCE_CONFIG || from === 'App map'});

function sourcePath(raw, from) {
  if (typeof raw !== 'string' || !raw || raw.includes('\\') || /[\0-\x1f]/.test(raw) || raw.startsWith('/') || /^[A-Za-z]:/.test(raw)
    || raw.split('/').includes('..')) throw sourceProblem(from, String(raw), 'must be a repository-relative file path with no traversal.');
  const path = posix.normalize(raw);
  if (path === '.' || path === '.git' || path.startsWith('.git/')) throw sourceProblem(from, raw, 'must be a repository-relative file path.');
  return path;
}

// Markdown links are relative to their owner; repo-root spellings also work when Git names them.
function contextPath(raw, from, visible) {
  if (!raw || raw.startsWith('#') || /^(?:[a-z][a-z0-9+.-]*:|\/\/)/i.test(raw)) return null;
  let target;
  try { target = decodeURIComponent(raw.split('#')[0]); }
  catch { throw sourceProblem(from, raw, 'is not a valid local context path.'); }
  if (!target) return null;
  if (target.startsWith('/') || target.includes('\\')) throw sourceProblem(from, raw, 'must stay inside this repository.');
  const relative = posix.normalize(posix.join(posix.dirname(from), target));
  const path = visible.has(relative) ? relative : visible.has(target.replace(/^\.\//, '')) ? target.replace(/^\.\//, '') : relative;
  return sourcePath(path, from);
}

// Read only a section name, never rewritten HTML. Ambiguous markup retains context.
function markdownSectionTitle(text) {
  const tokens = /<\/(strong|em|b|i)\s*>|<(strong|em|b|i)(?:\s+[A-Za-z_:][A-Za-z0-9_.:-]*(?:\s*=\s*(?:"[^"]*"|'[^']*'|[^\s"'=<>`]+))?)*\s*>|[^<>]+/giy;
  const parts = [], tags = [];
  let consumed = 0;
  for (let match; (match = tokens.exec(text));) {
    if (match[1]) {
      if (tags.pop() !== match[1].toLowerCase()) return null;
    } else if (match[2]) tags.push(match[2].toLowerCase());
    else parts.push(match[0]);
    consumed = tokens.lastIndex;
  }
  if (consumed !== text.length || tags.length) return null;
  return parts.join('').replace(/\s+/g, ' ').trim();
}

function markdownContext(text) {
  const prose = text.replace(INTERFACE, ''), markdown = markdownSectionText(prose), definitions = markdownDefinitions(markdown);
  const heading = /^##[ \t]+Dependencies[ \t]*\r?$/im.exec(markdown);
  const rest = heading ? prose.slice(heading.index + heading[0].length) : '';
  const maskedRest = heading ? markdown.slice(heading.index + heading[0].length) : '';
  const end = /^#{1,2}[ \t]+/m.exec(maskedRest);
  let dependencies = end ? rest.slice(0, end.index) : rest;
  let maskedDependencies = end ? maskedRest.slice(0, end.index) : maskedRest;
  // Legacy prompts use collapsible rule/reference sections instead of Markdown headings.
  // Keep collapsible dependency context; only an explicitly named new section ends it.
  for (const match of maskedDependencies.matchAll(/^ {0,3}<details\b[^>]*>\s*<summary\b[^>]*>([\s\S]*?)<\/summary\s*>/gim)) {
    const title = markdownSectionTitle(match[1]);
    if (title !== null && /^(?:(?:required )?(?:module )?rules|(?:required )?interface reference|decision path)(?:\s*:|$)/i.test(title)) {
      dependencies = dependencies.slice(0, match.index);
      maskedDependencies = maskedDependencies.slice(0, match.index);
      break;
    }
  }
  const paths = [...markdownLinks(maskedDependencies, definitions), ...markdownLinks(markdown, definitions, true)];
  // A bare filename is shorthand for a dependency item, not every code span in its description.
  for (const match of dependencies.matchAll(/^ {0,3}(?:[-+*]|[0-9]+[.)])[ \t]+`([^`\n]+)`(?=[ \t:]|$)/gm)) {
    // The list marker must be prose, even though this shorthand's path is a code span.
    const prefix = match[0].slice(0, match[0].indexOf('`'));
    if (!maskedDependencies.startsWith(prefix, match.index)) continue;
    const path = match[1];
    const externalOrCode = /^[~/%$]/.test(path) || /[\s\\:$%~<>*?|[\]{}()]/.test(path);
    const fileName = /\.[A-Za-z][A-Za-z0-9_-]*$/.test(posix.basename(path));
    const commonFile = /\.(?:md|prompt|txt|json|svg|css|csv|ya?ml|toml|xml|html?|[cm]?js|[cm]?ts|jsx|tsx|py|sh|sql|ini|conf)$/i.test(path);
    if (!externalOrCode && ((path.includes('/') && fileName) || commonFile || isSecretPath(path))) paths.push(path);
  }
  return paths;
}

function sourceLimit(files) {
  const total = files.reduce((sum, file) => sum + file.size, 0);
  if (files.length > LIMITS.files || total > LIMITS.bytes) {
    const largest = [...files].sort((a, b) => b.size - a.size).slice(0, 5).map(file => `  ${file.path}  ${formatSize(file.size)}`);
    throw Object.assign(new PreflightError(4, [`The repository is too big to send: ${files.length} files, ${formatSize(total)}. The limit is ${LIMITS.files} files and 10 MB.`,
      'The largest files:', ...largest].join('\n')), {selection:true});
  }
  return total;
}

function snapshotReader(root, diskVisible, beforeRead = () => {}, strict = false, workspace=loadRuntimeWorkspace({root})) {
  const snapshots = new Map();
  let unstable = false;
  root = realpathSync(root);
  const observations = new Map();
  const changed = () => { unstable = true; throw unstableSource; };
  function observe(path) {
    const stat = statOf(join(root, path));
    let link = null;
    if (stat?.isSymbolicLink()) {
      try { link = readlinkSync(join(root, path)); }
      catch (error) { if (['ENOENT', 'EINVAL', 'ENOTDIR'].includes(error.code)) changed(); throw error; }
    }
    const prior = observations.get(path);
    if (prior && (!(stat === null && prior.stat === null) && !sameStat(stat, prior.stat) || link !== prior.link)) changed();
    observations.set(path, { stat, link });
    return { stat, link };
  }
  function stable(paths = observations.keys()) {
    for (const path of paths) {
      const before = observations.get(path);
      const after = statOf(join(root, path));
      if (before.stat === null ? after !== null : !sameStat(before.stat, after)) return false;
      if (before.link !== null) {
        try { if (readlinkSync(join(root, path)) !== before.link) return false; }
        catch (error) { if (['ENOENT', 'EINVAL', 'ENOTDIR'].includes(error.code)) return false; throw error; }
      }
    }
    return true;
  }
  observe('');
  function inspectRaw(path, from, allowMissing = false, noLinks = false, control = false) {
    path = sourcePath(path, from);
    if(!control)requireRuntimePath(workspace,{path,from});
    if (isSecretPath(path)) {
      // Refusal is already decided. Enrich it only along non-following metadata
      // whose ancestors have each been checked as directories.
      let detail = '';
      try {
        const parts = path.split('/');
        for (let i = 1; i <= parts.length; i++) {
          const current = parts.slice(0, i).join('/');
          const stat = statOf(join(root, current));
          if (stat?.isSymbolicLink()) { detail = `link ${current} -> ${readlinkSync(join(root, current))}: `; break; }
          if (!stat?.isDirectory()) break;
        }
      } catch {} // Metadata failure cannot override the secret refusal.
      throw sourceProblem(from, path, `: ${detail}the name looks like a secret. pdd never sends it.`);
    }
    if (snapshots.has(path)) {
      const file = snapshots.get(path);
      if (noLinks && file.target) throw sourceProblem(from, path, ': symbolic links are not allowed for prepared output.');
      return file;
    }
    let pending = path.split('/').map(part => ({part, context:null})), resolved = [], lastLink = null, firstLink = null, linkedVisible = false, authored = true;
    const seen = new Set(), observed = new Set(['']);
    const refuse = (reason, context = lastLink, plain = false) => {
      throw sourceProblem(from, path, context ? `: link ${context.path} -> ${context.link}: ${reason}` : `${plain ? '' : ': '}${reason}`);
    };
    // Resolve components individually: an ancestor link must be checked before any
    // descendant is inspected. No host lookup follows an unchecked link.
    while (pending.length) {
      const {part, context} = pending.shift();
      if (!part || part === '.') continue;
      if (part === '..') {
        if (!resolved.length) refuse('resolution is outside the repository.', context);
        resolved.pop(); continue;
      }
      resolved.push(part);
      const current = resolved.join('/');
      observed.add(current);
      const { stat, link } = observe(current);
      if (link !== null) {
        lastLink = { path: current, link };
        firstLink ??= lastLink;
        // Only an ancestor in the authored spelling can authorize that spelling.
        // Links encountered after substitution cannot grant authored visibility.
        linkedVisible ||= authored && current !== path && diskVisible.has(current);
        authored = false;
        if (strict) refuse(current === path ? 'symbolic links are not allowed.' : 'symbolic link ancestor: symbolic links are not allowed.');
        if (noLinks) refuse('symbolic links are not allowed for prepared output.');
        if (isSecretPath(path) || isSecretPath(current)) refuse('the name looks like a secret. pdd never sends it.');
        const state = `${current}\0${pending.map(item => item.part).join('/')}`;
        if (seen.has(state)) refuse('symbolic link loop.');
        if (seen.size >= 40) refuse('too many links (loop or chain longer than 40).');
        seen.add(state);
        resolved.pop();
        if (isAbsolute(link)) {
          if (!link.startsWith(`${root}/`)) refuse('resolution is outside the repository.');
          const local = link.slice(root.length + 1);
          resolved = []; pending = [...local.split('/').map(part => ({part, context:lastLink})), ...pending];
        } else pending = [...link.split('/').map(part => ({part, context:lastLink})), ...pending];
        if(!control)requireRuntimePath(workspace,{path:posix.normalize([...resolved,...pending.map(x=>x.part)].join('/')),from,chain:[path,current]});
        continue;
      }
      if (isSecretPath(current) || (!pending.length && isSecretPath(path))) refuse('the name looks like a secret. pdd never sends it.', context ?? lastLink);
      if (!stat) {
        if (lastLink) refuse('broken link: target does not exist.', context ?? lastLink);
        if (!allowMissing) refuse('is not a Git-visible file on disk. Restore it or correct the declared dependency.', null, true);
        const file = { path, stat: null, size: 0, observed }; snapshots.set(path, file); return file;
      }
      if (pending.length && !stat.isDirectory()) refuse(`${lastLink ? 'non-directory ancestor' : 'has a non-directory ancestor'} (${current}).`, context ?? lastLink, !lastLink);
      if (!pending.length) {
        if (!stat.isFile()) refuse('a submodule, folder or other non-regular file. pdd sends only regular files.', context ?? lastLink);
        if (!diskVisible.has(path) && !linkedVisible && firstLink) refuse('link itself is not a Git-visible file. Add it to Git or correct the declared dependency.', firstLink);
        if (!diskVisible.has(current)) refuse(`${lastLink ? 'target is not' : 'is not'} a Git-visible file. Add it to Git or correct the declared dependency.`, context ?? lastLink, !lastLink);
        const file = { path, stat, size: Number(stat.size), observed, ...(lastLink ? { target: current } : {}) };
        snapshots.set(path, file); return file;
      }
    }
    refuse('a folder or other non-regular file.');
  }
  function bytes(file) {
    if (file.bytes) return file.bytes;
    sourceLimit([file]);
    beforeRead(file);
    let fd;
    try {
      fd = openSync(join(root, file.target ?? file.path), constants.O_RDONLY | constants.O_NOFOLLOW);
      if (!sameStat(file.stat, fstatSync(fd, { bigint: true }))) { unstable = true; throw unstableSource; }
      if (!stable(file.observed)) changed();
      file.bytes = readFileSync(fd);
      if (!stable(file.observed)) changed();
      if (!sameStat(file.stat, fstatSync(fd, { bigint: true })) || file.bytes.length !== file.size) { unstable = true; throw unstableSource; }
      return file.bytes;
    } catch (error) {
      if (['ENOENT', 'ELOOP', 'ENOTDIR'].includes(error.code)) { unstable = true; throw unstableSource; }
      throw error;
    } finally { if (fd !== undefined) closeSync(fd); }
  }
  return { inspectRaw, bytes, snapshots, stable, get unstable() { return unstable; } };
}

export function sourceFilePort(root, visible = new Set(gitFiles(root)),workspace) {
  return filePort(root, visible,false,workspace);
}

function filePort(root, visible, strict = false,workspace) {
  let policy=boundedWorkspace(root,workspace),key=JSON.stringify(policy),reader = snapshotReader(root, visible, undefined, strict,policy);
  const refresh=path=>{const current=boundedWorkspace(root,workspace),next=JSON.stringify(current);requireRuntimePath(current,{path,from:'Source'});if(next!==key){policy=current;key=next;reader=snapshotReader(root,visible,undefined,strict,policy);}};
  return {
    stat({path}) {
      if(path!=='pdd-bindings.json')refresh(path);
      const file = reader.inspectRaw(path, 'Source', true, path==='pdd-bindings.json',path==='pdd-bindings.json');
      return { exists: !!file.stat, is_symlink: false, size: file.size };
    },
    read({path}) {
      if(path!=='pdd-bindings.json')refresh(path);
      const file = reader.inspectRaw(path, 'Source',false,path==='pdd-bindings.json',path==='pdd-bindings.json');
      if (!file.stat) throw sourceProblem('Source',path,'is missing.');
      try { return { content: reader.bytes(file).toString('utf8') }; }
      catch (error) { if (error === unstableSource) throw new PreflightError(5, `${path}: the file changed while pdd read it.`); throw error; }
    },
  };
}

function preparedText(root, visible, path, text, format,workspace) {
  try { return expandSource({path,text,format},sourceFilePort(root,visible,workspace)); }
  catch (error) {
    if (error.code) throw new PreflightError(4, `${error.code}: ${error.message}`);
    throw error;
  }
}

function captureOnce(root, { tests, appMap = null, prepareSource,workspace=loadRuntimeWorkspace({root}),excludeFixtureProjects=tests === undefined }, strict = false) {
  const policyBefore=JSON.stringify(loadRuntimeWorkspace({root}));workspace=boundedWorkspace(root,workspace);
  const names = gitFiles(root), visible = new Set(names), overlay = new Map(), payload = new Map(), queue = [], visited = new Set();
  const chains=new Map(),preparationReads=new Set(),referenceReads=new Set();
  const effective = new Map(), provenance = new Map(), edges = new Map(), shared = new Set(), footprintPayload = new Map();
  let selecting = true;
  const unavailable = new Map();
  const markUnavailable = (path,error) => unavailable.set(path,{path,cause:String(error.message ?? error).replace(/[\r\n\x00-\x1f\x7f]/g,' ').slice(0,4000)});
  const reader = snapshotReader(root,new Set(names),file => { if (payload.has(file.path)) sourceLimit([...payload.values()]); }, strict,workspace);
  const { inspectRaw, bytes, snapshots } = reader;
  function inspect(path, from) {
    if (overlay.has(path)) return overlay.get(path);
    const file = inspectRaw(path, from);
    if (!file.stat) throw sourceProblem(from, path, 'is missing. Restore it or correct the declared dependency.');
    return file;
  }
  function add(raw, from, role = 'context') {
    const path = sourcePath(raw, from);
    const chain=chains.get(from)??[];requireRuntimePath(workspace,{path,from,chain});
    if(!chains.has(path))chains.set(path,[...chain,from]);
    const file = inspect(path, from);
    for (const selected of payload.keys()) if (selected.startsWith(`${path}/`) || path.startsWith(`${selected}/`)) {
      throw sourceProblem(from, path, `conflicts with selected file ${selected}.`);
    }
    if (!footprintPayload.has(path)) footprintPayload.set(path,file);
    if (selecting && !payload.has(path)) payload.set(path, file);
    if (visible.has(from)) {
      if (!edges.has(from)) edges.set(from,new Set());
      edges.get(from).add(path);
    }
    queue.push({ path, role, upload:selecting });
  }
  const referenceFiles = {
    stat({path}) {
      const file = overlay.get(path) ?? inspectRaw(path,'Reference',true);
      return {exists:overlay.has(path) || !!file.stat,is_symlink:false,size:file.size};
    },
    read({path}) {referenceReads.add(path); return {content:bytes(inspect(path,'Reference')).toString('utf8')}; },
  };
  function prepare(file, format) {
    if (effective.has(file.path)) return effective.get(file.path);
    let expanded;
    try { expanded = expandSource({path:file.path,text:bytes(file).toString('utf8'),format},referenceFiles); }
    catch (error) {
      if (reader.unstable || error === unstableSource) throw unstableSource;
      if (error.code) throw new PreflightError(4, `${error.code}: ${error.message}`);
      throw error;
    }
    let content = expanded.references.length ? Buffer.from(expanded.text,'utf8') : bytes(file);
    if (format === 'scenario') {
      let doc; try { doc = JSON.parse(content.toString('utf8')); } catch { /* Keep invalid-source handling. */ }
      const expected = matchTests(names.filter(isStoryPath), names).tests.find(test=>test.path===file.path);
      const authority = doc?.schema_version !== TEST_SCHEMA ? null : isObject(doc) && (typeof doc.story_path !== 'string' || !doc.story_path)
        ? refusal('pdd-no-story', 'story_path', 'The test has no story_path. Name its Story.')
        : discoveryRefusal({path:file.path,storyPath:expected?.storyPath,doc});
      if (authority) throw Object.assign(new PreflightError(4, `${file.path}: ${authority.message}`), authority,
        {message:`${file.path}: ${authority.message}`,hint:'Restore the Story path selected by the test name, then run the selection again.'});
      if (typeof doc?.story_path === 'string' && !scenarioShapeRefusal(doc, file.path)) {
        add(doc.story_path, file.path, 'story');
        const plan = capturedCriterionPlan(doc, storyCriteria(bytes(inspect(doc.story_path, file.path)).toString('utf8')), file.path);
        if (plan?.not_checked.length && plan.checked) content = Buffer.from(JSON.stringify({...doc,criteria:plan.criteria,
          check_exemptions:plan.not_checked.map(item => ({criterion_id:item.criterion_id,reason:'out-of-scope',detail:item.reason}))}), 'utf8');
      }
    }
    const result = {...file,bytes:content,size:content.length};
    effective.set(file.path,result); provenance.set(file.path,expanded.references);
    footprintPayload.set(file.path,result);
    if (selecting) payload.set(file.path,result);
    return result;
  }
  const addStrings = (values, from, role) => { if (Array.isArray(values)) for (const path of values) if (typeof path === 'string') add(path, from, role); };
  try {
    if (prepareSource !== undefined) {
      if (typeof prepareSource !== 'function') throw new PreflightError(4, 'prepareSource must be a synchronous function.');
      let active = true, prepared;
      const raw = path => {
        if (!active) throw new PreflightError(4, 'Preparation ports are valid only during prepareSource.');
        return inspectRaw(sourcePath(path, 'prepareSource'), 'prepareSource', true);
      };
      try {
        prepared = prepareSource({
          readFile(path) {
            preparationReads.add(path);const file = raw(path);
            if (!file.stat) throw sourceProblem('prepareSource', path, 'is missing.');
            return Buffer.from(bytes(file));
          },
          statFile(path) {
            const file = raw(path);
            return { exists: !!file.stat, is_symlink: false, size: file.size };
          },
        });
      } finally { active = false; }
      if (reader.unstable) throw unstableSource;
      if (!Array.isArray(prepared)) throw new PreflightError(4, 'prepareSource must return an array of files synchronously.');
      for (const output of prepared) {
        if (!isObject(output) || !(typeof output.bytes === 'string' || output.bytes instanceof Uint8Array)) throw new PreflightError(4, 'prepareSource files need a path and Buffer, Uint8Array or UTF-8 string bytes.');
        const path = sourcePath(output.path, 'prepareSource');
        if (overlay.has(path)) throw sourceProblem('prepareSource', path, `duplicates prepared file ${path}.`);
        for (const other of overlay.keys()) if (other.startsWith(`${path}/`) || path.startsWith(`${other}/`)) throw sourceProblem('prepareSource', path, `conflicts with prepared file ${other}.`);
        inspectRaw(path, 'prepareSource', true, true);
        const content = Buffer.from(output.bytes), file = { path, bytes: content, size: content.length };
        overlay.set(path, file);
        visible.add(path);
      }
      for (const path of overlay.keys()) add(path, 'prepareSource');
    }
    if (visible.has(SOURCE_CONFIG)) {
      try {
      const config = overlay.get(SOURCE_CONFIG)??inspectRaw(SOURCE_CONFIG, SOURCE_CONFIG, false, false, true);
      let doc;
      try { doc = JSON.parse(bytes(config).toString('utf8')); } catch (error) {
        if (error === unstableSource) throw error;
        throw sourceProblem(SOURCE_CONFIG, '', 'must be valid JSON with only an include array.');
      }
      if (!isObject(doc) || Object.keys(doc).length !== 1 || !Array.isArray(doc.include)) throw sourceProblem(SOURCE_CONFIG, '', 'must contain only an include array of file paths.');
      for (const path of doc.include) { add(path, SOURCE_CONFIG); shared.add(sourcePath(path,SOURCE_CONFIG)); }
      } catch (error) { if (error !== unstableSource) error.selection = true; throw error; }
    }
    // The test name rule over the effective source (Git-visible files and prepared files); it opens no JSON file.
    const excluded = excludeFixtureProjects ? fixtureProjectRoots(root, names) : [];
    const discoveryNames = outsideFixtureProjects(names, excluded);
    const onDisk = discoverStories(root,discoveryNames,strict,workspace);
    const named = matchTests(onDisk.storyFiles, outsideFixtureProjects([...onDisk.visible, ...overlay.keys()], excluded)).tests.filter(test=>!test.problem);
    const allNamed=matchTests(onDisk.storyFiles,discoveryNames).tests.flatMap(test=>(test.files??[test.path]).map(path=>({...test,path})));
    const selected = tests ?? named.map(test=>test.path);
    for (const path of selected) add(path, 'Selected test',path.endsWith('.prompt.md')?'context':isStoryPath(path)?'story':'test');
    if (appMap) { add(appMap, 'App map', 'app-map'); shared.add(sourcePath(appMap,'App map')); }
    const storyTests = new Map(), boundaries = new Map();
    let siblingsAdded = false;
    for (let index = 0; index < queue.length || !siblingsAdded; index++) {
      if (index === queue.length && !siblingsAdded) {
        siblingsAdded = true; selecting = false;
        const selectedStories = new Set(storyTests.keys());
        for (const test of allNamed) {
          if (!selectedStories.has(test.storyPath)) continue;
          if (!storyTests.get(test.storyPath).includes(test.path)) storyTests.get(test.storyPath).push(test.path);
          try { if(test.problem)markUnavailable(test.path,new Error(test.problem));add(test.path,'Story footprint','test'); } catch (error) { if (reader.unstable || error === unstableSource) throw error; markUnavailable(test.path,error); }
        }
        if (index === queue.length) break;
      }
      const { path, role, upload } = queue[index], key = `${path}\0${role}\0${upload}`;
      selecting = upload;
      if (visited.has(key)) continue;
      visited.add(key);
      try {
        let file = effective.get(path) ?? footprintPayload.get(path);
        if (selecting) payload.set(path,file);
        if (path.endsWith('.prompt.md')) file = prepare(file,'prompt');
        else if (role === 'test') file = prepare(file,'scenario');
        if (role === 'test' || role === 'app-map' || path.endsWith('.prompt.md') || path.endsWith('.md')) {
          const text = bytes(file).toString('utf8');
          if (role === 'test') {
            let doc;
            try { doc = JSON.parse(text); } catch { continue; } // Format refusals belong to preflight or server lint.
            if (!isObject(doc)) continue;
            if (typeof doc.story_path === 'string') {
              if (selecting) { if (!storyTests.has(doc.story_path)) storyTests.set(doc.story_path,[]); if (!storyTests.get(doc.story_path).includes(path)) storyTests.get(doc.story_path).push(path); }
              add(doc.story_path, path, 'story');
            }
            addStrings(doc.entry_paths, path);
            for (const step of Array.isArray(doc.steps) ? doc.steps : []) if (typeof step?.entry_path === 'string') add(step.entry_path, path);
            for (const item of Array.isArray(doc.context) ? doc.context : []) {
              if (typeof item?.prompt_path === 'string') add(item.prompt_path, path);
              addStrings(item?.paths, path);
            }
          } else if (role === 'app-map') {
            let map;
            try { map = JSON.parse(text); } catch { throw sourceProblem(path, '', 'must be valid app-map JSON.'); }
            const walk = value => {
              if (Array.isArray(value)) { for (const item of value) walk(item); return; }
              if (!isObject(value)) return;
              if (typeof value.prompt_path === 'string') add(value.prompt_path, path);
              addStrings(value.stylesheets, path);
              for (const key of ['screens', 'router', 'routes', 'handlers', 'handler', 'after']) walk(value[key]);
            };
            walk(map);
          } else {
            if (role === 'story') {
              const notes=[];
              let boundary=runtimeBoundary(path,text,{notes});
              if (boundary) {
                try {
                  // Validate all members before admitting any boundary-only source.
                  for (const member of boundary) {
                    requireRuntimePath(workspace,{path:member,from:path,chain:chains.get(path)??[]});
                    bytes(inspect(member,path));
                  }
                } catch (error) {
                  if (reader.unstable || error === unstableSource) throw error;
                  boundary=null;
                  notes.push({code:'boundary-not-applied',reason:'unreadable-path',
                    message:'boundary not applied: unreadable-path; full dependency closure is required'});
                }
              }
              boundaries.set(path,{boundary,notes});
              for (const member of boundary ?? []) add(member,path);
            }
            for (const raw of markdownContext(text)) { const context = contextPath(raw, path, visible); if (context) add(context, path); }
            if (path.endsWith('.prompt.md')) {
              for (const block of interfaceBlocks(text)) {
                let doc;
                try { doc = JSON.parse(block[1]); } catch { continue; }
                for (const call of Array.isArray(doc?.calls) ? doc.calls : []) if (typeof call?.target === 'string') add(call.target, path);
              }
            }
          }
        }
        // Footprint-only binary/plain inputs still need bounded bytes for hashes.
        if (!selecting) bytes(file);
      } catch (error) {
        if (role === 'app-map' && error !== unstableSource) error.selection = true;
        if (selecting || reader.unstable || error === unstableSource) throw error;
        markUnavailable(path,error);
      }
    }
    // A Story boundary selects executable interfaces, while preserving context prose.
    const bindingPrompts = new Map();
    for (const [path,file] of footprintPayload) if (path.endsWith('.prompt.md')) {
      try { bindingPrompts.set(path,JSON.parse(interfaceBlocks(bytes(file).toString('utf8'))[0][1])); } catch { /* Admission reports malformed interfaces. */ }
    }
    const bindingPlans = [];
    for (const path of selected) {
      const file = payload.get(path); if (!file) continue;
      let doc; try { doc=JSON.parse(bytes(file).toString('utf8')); } catch { continue; }
      if (!doc?.story_path || !Array.isArray(doc.steps)) continue;
      try {
        const reached=new Set(), pending=[path,...shared];
        for (let index=0;index<pending.length;index++) {
          const dependency=pending[index];
          if (reached.has(dependency)) continue;
          reached.add(dependency);pending.push(...(edges.get(dependency)??[]));
        }
        bindingPlans.push(buildBindingPlan({test:{path,storyPath:doc.story_path,doc},
          storyText:bytes(inspect(doc.story_path,path)).toString('utf8'),prompts:bindingPrompts,
          dependencyPaths:[...reached].filter(dependency=>dependency.endsWith('.prompt.md')).sort(),
          boundaryState:boundaries.get(doc.story_path)}));
      } catch (error) { throw Object.assign(new PreflightError(4,error.message),{code:error.code}); }
    }
    const scoped = bindingPlans.filter(plan=>plan.boundary !== null);
    for (const plan of scoped) {
      for (const path of plan.boundary) inspect(path,plan.story);
      const crossing=plan.problems[0];
      if (crossing) throw Object.assign(new PreflightError(4,`${plan.story}: ${crossing.step_id}: ${crossing.prompt_path}: ${crossing.code}. Correct the Runtime interface boundary or call target.`),{code:'binding-boundary-invalid'});
    }
    const required = new Set(scoped.flatMap(plan=>plan.boundary));
    if (scoped.length === bindingPlans.length && scoped.length) for (const [path,file] of payload) {
      if (!path.endsWith('.prompt.md') || required.has(path)) continue;
      const projected=Buffer.from(bytes(file).toString('utf8').replace(INTERFACE,''),'utf8');
      const next={...file,bytes:projected,size:projected.length};
      payload.set(path,next); footprintPayload.set(path,next); effective.set(path,next);
    }
    const files = [...payload.values()].sort((a, b) => a.path < b.path ? -1 : a.path > b.path ? 1 : 0), total = sourceLimit(files);
    const entries = files.map(file => ({ path: file.path, bytes: bytes(file) }));
    const rawFileHashes = Object.fromEntries([...footprintPayload.values()].flatMap(file=>{
      if (unavailable.has(file.path)) return [];
      try {
        // Cache metadata reuses observed raw bytes; it must not read an unread
        // replacement original merely to make a Story eligible for reuse.
        if (!file.path.endsWith('.prompt.md')) {
          const original = snapshots.get(file.path);
          return original?.bytes ? [[file.path,sha256(original.bytes)]] : [];
        }
        const original=inspectRaw(file.path,'Prompt snapshot',true);
        return original.stat ? [[file.path,sha256(bytes(original))]] : [];
      } catch (error) {
        if (payload.has(file.path) || reader.unstable || error === unstableSource) throw error;
        markUnavailable(file.path,error);
        return [];
      }
    }));
    const tar = tarFiles(entries);
    if (tar.length > LIMITS.bytes) throw Object.assign(new PreflightError(4, `The source archive is ${formatSize(tar.length)}. The limit is 10 MB.`), {selection:true});
    const same = !reader.unstable && isDeepStrictEqual(gitFiles(root), names) && reader.stable() && JSON.stringify(loadRuntimeWorkspace({root}))===policyBefore;
    if (!same) return null;
    const stories = new Map();
    for (const path of selected) {
      let doc; try { doc = JSON.parse(bytes(payload.get(sourcePath(path,'Selected test'))).toString('utf8')); } catch { continue; }
      if (typeof doc?.story_path !== 'string') continue;
      if (!stories.has(doc.story_path)) stories.set(doc.story_path,{story_path:doc.story_path,tests:[],selected:new Set(shared)});
      const story = stories.get(doc.story_path);
      story.tests = storyTests.get(doc.story_path) ?? [path];
      for (const sibling of story.tests) story.selected.add(sibling);
    }
    const footprints = [...stories.values()].map(story => {
      const reached = new Set(), pending = [...story.selected];
      for (let i=0;i<pending.length;i++) {
        const path=pending[i]; if (reached.has(path)) continue;
        reached.add(path); pending.push(...(edges.get(path) ?? []));
      }
      const failures = [...reached].sort().filter(path=>unavailable.has(path)).map(path=>unavailable.get(path));
      if (failures.length) return {story_path:story.story_path,tests:story.tests.sort(),unavailable:failures};
      return {story_path:story.story_path,tests:story.tests.sort(),files:[...reached].sort().filter(path=>footprintPayload.has(path)).map(path=>({path,sha256:sha256(bytes(footprintPayload.get(path)))})),references:[...reached].sort().flatMap(path=>provenance.get(path) ?? [])};
    });
    return { tar, sha256: sha256(tar), files: files.map(({ path, size, target }) => ({ path, size, ...(target ? { target } : {}) })), bytes: total,
      references:[...provenance.keys()].filter(path=>payload.has(path)).sort().flatMap(path=>provenance.get(path)), stories:footprints,
      warnings:footprints.flatMap(story=>(story.unavailable ?? []).map(item=>`Warning: ${story.story_path}: footprint unavailable: ${item.cause}`)),
      raw_file_hashes:rawFileHashes,
      raw_prompt_hashes:Object.fromEntries(Object.entries(rawFileHashes).filter(([path])=>path.endsWith('.prompt.md'))),
      reads:[...new Set([...onDisk.storyFiles,...snapshots.keys()])].filter(path=>path!==SOURCE_CONFIG&&!payload.has(path)&&(snapshots.get(path)?.bytes||onDisk.storyFiles.includes(path))).sort().map(path=>({path,roles:[...(onDisk.storyFiles.includes(path)?['discovery']:[]),...(referenceReads.has(path)?['reference']:[]),...(preparationReads.has(path)?['preparation']:[]),...(!onDisk.storyFiles.includes(path)&&!referenceReads.has(path)&&!preparationReads.has(path)?['footprint']:[])].sort()})),
      bindingPlans,
      sources:entries.map(file=>({path:file.path,bytes:Buffer.from(file.bytes)})) };
  } catch (error) { if (reader.unstable || error === unstableSource) return null; throw error; }
}

// Rebuild the selection on each attempt, including metadata and newly declared dependencies.
export function captureSource(root, { attempts = 3, ...selection } = {}) {
  return captureWithPolicy(root, { attempts, ...selection });
}

function captureWithPolicy(root, { attempts = 3, ...selection } = {}, strict = false) {
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    const captured = captureOnce(root, selection, strict);
    if (captured) return captured;
  }
  throw new PreflightError(5, `The files changed while pdd read them (${attempts} times). Stop other edits, then run pdd test again.`);
}

// A bound capability keeps strict command reads isolated from source-upload reads.
export function createStrictSourceAccess(root,workspace) {
  return {
    sourceFilePort(visible = new Set(gitFiles(root))) { return filePort(root, visible, true,workspace); },
    findTests({files = gitFiles(root)} = {}) { return discoverTests(root, files, true,workspace); },
    captureSource(options = {}) { return captureWithPolicy(root, {...options,...(workspace?{workspace}:{})}, true); },
  };
}

export const NO_TESTS = 'No tests found. The test of Story user_stories/S.md is S.json in a test or tests folder. See RUNBOOK.md §2.';

// Why a repo has no tests, by the test name rule (it opens no JSON file): Stories with no test, test-folder JSON
// that matches no Story, *.prompt names, prompts with no interface.
export function whyNoTests(root, visible, found = discoverTests(root, [...visible])) {
  const files = [...visible].filter(path=>allowsRuntimePath(loadRuntimeWorkspace({root}),path)).sort(), why = [...(found.untested ?? []), ...(found.orphans ?? [])].map(item => item.line);
  for (const path of files.filter(file => file.endsWith('.prompt'))) why.push(`PDD prompts must end in .prompt.md: rename ${path} to ${path}.md.`);
  for (const path of files.filter(file => file.endsWith('.prompt.md'))) {
    if (!interfaceBlocks(readText(root, path)).length) why.push(`${path} has no Runtime interface block. See RUNBOOK.md §2.`);
  }
  return why.length > 5 ? [...why.slice(0, 5), `…and ${why.length - 5} more`] : why;
}

// Source files named (in backticks) by more than one prompt: one warning line each (real-user cli issue 10).
export function sharedSourceFiles(root, visible) {
  const owners = new Map(), warnings = [];
  for (const prompt of [...visible].filter(path => allowsRuntimePath(loadRuntimeWorkspace({root}),path)&&path.endsWith('.prompt.md')).sort()) {
    if (Number(statOf(join(root,prompt))?.size ?? 0) > LIMITS.bytes) continue;
    let text;
    try { text = readText(root, prompt); }
    catch (error) {
      if (!(error instanceof PreflightError && error.exitCode === 4) && !['EACCES','EPERM','EISDIR','ENOENT'].includes(error.code)) throw error;
      warnings.push(`Warning: ${prompt}: source ownership advice unavailable (${error.code ?? error.message}).`); continue;
    }
    for (const match of text.matchAll(/`([^`\s]+)`/g)) {
      const path = match[1].replace(/^\.\//, '');
      if (path === prompt || path.endsWith('.md') || !visible.has(path)) continue;
      owners.set(path, new Set([...(owners.get(path) ?? []), prompt]));
    }
  }
  return [...warnings,...[...owners].filter(([, prompts]) => prompts.size > 1).sort(([a], [b]) => a.localeCompare(b))
    .map(([path, prompts]) => `Warning: ${path} is named by ${prompts.size} prompts (${[...prompts].join(', ')}). One prompt should own each source file.`)];
}

// Files sent that are not prompt, story or test files.
export function otherFiles(files, found) {
  const known = new Set([...found.tests.map(test => test.path), ...found.stories.map(story => story.path)]);
  return files.filter(file => !file.path.endsWith('.prompt.md') && !known.has(file.path));
}
