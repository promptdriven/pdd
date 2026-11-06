import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { findTests, preflight } from '../src/runtime-preflight.mjs';
import { harbor, root } from './runtime-fake.mjs';

const bin = join(root, 'bin/pdd.mjs');
const write = (repo, path, bytes) => { mkdirSync(dirname(join(repo, path)), { recursive: true }); writeFileSync(join(repo, path), bytes); };
const cli = (setup, ...words) => {
  const result = spawnSync(process.execPath, [bin, 'test', '--files', ...words], { cwd: setup.repo, encoding: 'utf8', env: { ...process.env, HOME: setup.home } });
  return { code: result.status, output: result.stdout + result.stderr };
};
const project = (repo, path, name) => {
  const story = readFileSync(join(repo, 'user_stories/place-order.md'));
  const doc = JSON.parse(readFileSync(join(repo, 'tests/place-order.json')));
  doc.story_path = `${path}/user_stories/${name}.md`;
  doc.steps[0].entry_path = 'prompts/missing-fixture.prompt.md';
  write(repo, `${path}/user_stories/${name}.md`, story);
  write(repo, `${path}/tests/${name}.json`, JSON.stringify(doc));
};

test('default CLI excludes every qualified project before matching or reading and preserves fixture bytes', t => {
  const setup = harbor(t), { repo } = setup;
  const paths = ['test/fixtures/one', 'test/fixtures/one/nested', 'test/fixtures/two'];
  project(repo, paths[0], 'place-order'); // same-name conflict with the root
  project(repo, paths[1], 'nested');
  project(repo, paths[2], 'broken');
  write(repo, `${paths[2]}/tests/broken.json`, '{ invalid JSON');
  const files = paths.flatMap((path, i) => [`${path}/user_stories/${['place-order', 'nested', 'broken'][i]}.md`, `${path}/tests/${['place-order', 'nested', 'broken'][i]}.json`]);
  const before = files.map(path => readFileSync(join(repo, path)));
  const result = cli(setup);
  assert.equal(result.code, 0, result.output);
  for (const path of paths) assert.ok(result.output.split(/\r?\n/).some(line => line.includes(path) && line.endsWith(`${path}.`)), `missing distinct excluded root ${path}: ${result.output}`);
  assert.ok(result.output.includes('tests/place-order.json'), result.output);
  assert.doesNotMatch(result.output, /not valid JSON|matches \d+ Stories|has \d+ files named/);
  files.forEach((path, i) => assert.deepEqual(readFileSync(join(repo, path)), before[i], path));
});

test('explicit fixture Story, test and directory selections retain errors and root-relative dependencies', t => {
  const setup = harbor(t), path = 'test/fixtures/example';
  project(setup.repo, path, 'fixture-only');
  for (const selection of [`${path}/user_stories/fixture-only.md`, `${path}/tests/fixture-only.json`, path]) {
    const result = cli(setup, selection);
    assert.equal(result.code, 4, `${selection}: ${result.output}`);
    assert.ok(result.output.includes('prompts/missing-fixture.prompt.md'), result.output);
  }
  write(setup.repo, `${path}/tests/fixture-only.json`, '{ malformed');
  const malformed = cli(setup, `${path}/tests/fixture-only.json`);
  assert.match(malformed.output, /valid JSON/i);
});

test('a real missing root dependency remains a refusal with a qualified fixture present', t => {
  const setup = harbor(t);
  project(setup.repo, 'test/fixtures/example', 'fixture-only');
  const path = join(setup.repo, 'tests/place-order.json');
  const doc = JSON.parse(readFileSync(path));
  doc.steps[0].entry_path = 'prompts/missing-root.prompt.md';
  writeFileSync(path, JSON.stringify(doc));
  const result = cli(setup);
  assert.equal(result.code, 4, result.output);
  assert.ok(result.output.includes('prompts/missing-root.prompt.md'), result.output);
});

test('incomplete projects and projects elsewhere remain in ordinary discovery', t => {
  const setup = harbor(t), { repo } = setup;
  project(repo, 'test/fixtures/incomplete', 'incomplete');
  // Direct tests root is empty: a test under a different folder is still discoverable.
  cpSync(join(repo, 'test/fixtures/incomplete/tests/incomplete.json'), join(repo, 'test/incomplete.json'));
  rmSync(join(repo, 'test/fixtures/incomplete/tests'), { recursive: true });
  project(repo, 'examples/complete', 'example');
  project(repo, 'fixtures/complete', 'other');
  mkdirSync(join(repo, 'test/fixtures/incomplete/tests'), { recursive: true });
  write(repo, '.gitignore', 'test/fixtures/ignored/tests/*\n');
  project(repo, 'test/fixtures/ignored', 'ignored');
  project(repo, 'test/fixtures/empty-story', 'empty-story');
  rmSync(join(repo, 'test/fixtures/empty-story/user_stories'), { recursive: true });
  mkdirSync(join(repo, 'test/fixtures/empty-story/user_stories'), { recursive: true });
  const found = findTests({ root: repo, excludeFixtureProjects: true });
  assert.ok(found.orphans.some(row => row.path === 'test/fixtures/empty-story/tests/empty-story.json'));
  assert.ok(found.untested.some(row => row.story === 'ignored'));
  for (const name of ['incomplete', 'example', 'other']) assert.ok(found.tests.some(row => row.story === name), name);
});


test('without a qualified project default selection and explicit selection remain usable', t => {
  const setup = harbor(t);
  const found = findTests({ root: setup.repo });
  assert.ok(found.tests.some(row => row.path === 'tests/place-order.json'));
  assert.equal(cli(setup).code, 0);
  assert.equal(cli(setup, 'tests/place-order.json').code, 0);
});

test('without a qualified project --files preserves the orphan warning stream', t => {
  const setup = harbor(t), { repo } = setup;
  write(repo, 'user_stories/untested.md', '# Untested\n\n## Acceptance criteria\n\n1. Something happens.\n');
  write(repo, 'tests/orphan-one.json', '{}');
  write(repo, 'tests/orphan-two.json', '{}');
  const result = cli(setup);
  assert.equal(result.code, 0, result.output);
  assert.ok(result.output.includes('tests/place-order.json'), result.output);
  const warnings = result.output.split(/\r?\n/).filter(line => line.startsWith('Warning:'));
  assert.deepEqual(warnings, [
    'Warning: tests/orphan-one.json matches no Story (user_stories/**/orphan-one.md).',
    'Warning: tests/orphan-two.json matches no Story (user_stories/**/orphan-two.md).',
  ]);
});


test('selected root dependencies under an excluded project stay available and safe', t => {
  const setup = harbor(t), { repo } = setup, path = 'test/fixtures/example';
  project(repo, path, 'fixture-only');
  const target = `${path}/prompts/selected.prompt.md`;
  const docPath = join(repo, 'tests/place-order.json');
  const doc = JSON.parse(readFileSync(docPath));
  const original = doc.steps[0].entry_path;
  write(repo, target, readFileSync(join(repo, original)));
  doc.steps[0].entry_path = target;
  writeFileSync(docPath, JSON.stringify(doc));
  const valid = cli(setup);
  assert.equal(valid.code, 0, valid.output);
  assert.ok(valid.output.includes(target), valid.output);
  rmSync(join(repo, target));
  const missing = cli(setup);
  assert.equal(missing.code, 4, missing.output);
  assert.ok(missing.output.includes(target), missing.output);
  doc.steps[0].entry_path = `${path}/secrets/hidden.prompt.md`;
  write(repo, doc.steps[0].entry_path, 'secret');
  writeFileSync(docPath, JSON.stringify(doc));
  const unsafe = cli(setup);
  assert.equal(unsafe.code, 4, unsafe.output);
  assert.ok(unsafe.output.includes(doc.steps[0].entry_path), unsafe.output);
});

test('all excluded roots are reported when no tests remain', t => {
  const setup = harbor(t), { repo } = setup;
  const paths = ['test/fixtures/one', 'test/fixtures/one/nested'];
  project(repo, paths[0], 'one');
  project(repo, paths[1], 'nested');
  rmSync(join(repo, 'user_stories'), { recursive: true });
  rmSync(join(repo, 'tests'), { recursive: true });
  const result = cli(setup);
  assert.equal(result.code, 2, result.output);
  assert.ok(result.output.startsWith('No tests found. The test of Story user_stories/S.md is S.json in a test or tests folder. See RUNBOOK.md §2.'), result.output);
  for (const path of paths) assert.ok(result.output.split(/\r?\n/).some(line => line.includes(path) && line.endsWith(`${path}.`)), `missing distinct excluded root ${path}: ${result.output}`);
});

test('explicit same-name selection still reports collision', t => {
  const setup = harbor(t);
  project(setup.repo, 'test/fixtures/example', 'place-order');
  const result = cli(setup, 'place-order');
  assert.match(result.output, /match(?:es)? \d+ Stories|has \d+ files named/i);
});


test('local preflight keeps selected root dependency under excluded fixture visible', t => {
  const setup = harbor(t), { repo } = setup, path = 'test/fixtures/example';
  project(repo, path, 'fixture-only');
  const docPath = join(repo, 'tests/place-order.json');
  const doc = JSON.parse(readFileSync(docPath));
  const target = `${path}/prompts/selected.prompt.md`;
  write(repo, target, readFileSync(join(repo, doc.steps[0].entry_path)));
  doc.steps[0].entry_path = target;
  writeFileSync(docPath, JSON.stringify(doc));
  const found = findTests({ root: repo, excludeFixtureProjects: true });
  const row = preflight({ root: repo, found, selected: found.tests.filter(item => item.path === 'tests/place-order.json') }).rows[0];
  assert.deepEqual(row.refusals, [], JSON.stringify(row.refusals));
});
