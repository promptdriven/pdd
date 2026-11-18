import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { parseScenarioJson, stringifyScenarioJson } from '../../src/runtime-seam.mjs';

export const sourceRoot = fileURLToPath(new URL('../../', import.meta.url));
export const scenarioPath = 'test/runtime/fake-recorded-call.json';
export const promptPath = 'examples/fakes/service.prompt.md';
export const storyPath = 'user_stories/fake-recorded-call.md';
export const version = 'prompt-runtime.code-call.v1';
export const seamModule = new URL('../../src/runtime-seam.mjs', import.meta.url).href;
export const read = path => readFileSync(join(sourceRoot, path), 'utf8');
export const clean = root => rmSync(root, { recursive: true, force: true });

export function save(root, path, text) {
  mkdirSync(dirname(join(root, path)), { recursive: true });
  writeFileSync(join(root, path), text);
}

export function commit(root) {
  for (const argv of [
    ['add', '.'],
    ['-c', 'user.name=fixture', '-c', 'user.email=fixture@example.com', 'commit', '-qm', 'native fixture'],
  ]) {
    const out = spawnSync('git', argv, { cwd: root, encoding: 'utf8' });
    if (out.status !== 0) throw Error(out.stderr);
  }
}

export function fixtureProject({
  change = () => {},
  interfaceChange = () => {},
  appChange = text => text,
  implementation,
  useCommittedPrompt = false,
  policy,
} = {}) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-code-call-'));
  spawnSync('git', ['init', '-q', root]);
  for (const path of [storyPath, 'docs/code-call-adapters.md']) save(root, path, read(path));
  const rawPrompt = read(promptPath);
  if (useCommittedPrompt) {
    save(root, promptPath, rawPrompt);
  } else {
    const match = /```json\n([\s\S]*?)\n```/.exec(rawPrompt);
    const iface = parseScenarioJson(match[1]);
    iface.entries[0].implementation =
      implementation !== undefined
        ? implementation
        : { kind: 'call', command: [process.execPath, 'examples/fakes/service.mjs'], symbol: 'lookup' };
    interfaceChange(iface);
    save(root, promptPath, rawPrompt.replace(match[1], stringifyScenarioJson(iface, 2)));
  }
  save(root, 'examples/fakes/service.mjs', appChange(read('examples/fakes/service.mjs')));
  const doc = parseScenarioJson(read(scenarioPath));
  change(doc);
  // The ordinary replay copies exact original bytes. Variants are separate
  // synthetic native boundary tests, never repairs to the canonical scenario.
  save(
    root,
    scenarioPath,
    stringifyScenarioJson(doc) === stringifyScenarioJson(parseScenarioJson(read(scenarioPath)))
      ? read(scenarioPath)
      : stringifyScenarioJson(doc, 2)
  );
  save(root, '.gitignore', 'node_modules/\n');
  symlinkSync(join(sourceRoot, 'node_modules'), join(root, 'node_modules'), 'dir');
  if (policy) save(root, 'pdd-workspace.json', JSON.stringify(policy));
  commit(root);
  return root;
}

export function run(root, { json = true, words = ['fake-recorded-call'] } = {}) {
  return spawnSync(
    process.execPath,
    [join(sourceRoot, 'bin/pdd.mjs'), 'test', '--target', 'code', ...words, ...(json ? ['--json'] : [])],
    {
      cwd: root,
      encoding: 'utf8',
      env: { ...process.env, GH_TOKEN: '', GITHUB_TOKEN: '', PDD_RUNTIME_URL: 'http://127.0.0.1:1' },
    }
  );
}

export function report(root, options) {
  const out = run(root, options);
  return { out, data: out.stdout ? parseScenarioJson(out.stdout) : null };
}

export function pureProject({
  inputSchema = { type: 'object', properties: { id: { type: 'string' } }, required: ['id'], additionalProperties: false },
  resultSchema = { type: 'object', properties: { id: { type: 'string' } }, required: ['id'], additionalProperties: false },
  errors = [],
  app,
  change = () => {},
  ...options
} = {}) {
  return fixtureProject({
    ...options,
    interfaceChange: iface => {
      iface.resources = [];
      iface.calls = [];
      iface.entries[0].input_schema = inputSchema;
      iface.entries[0].result_schema = resultSchema;
      iface.entries[0].errors = errors;
      options.interfaceChange?.(iface);
    },
    appChange: () =>
      app ??
      `import {parseScenarioJson,stringifyScenarioJson} from ${JSON.stringify(seamModule)};
import {writeFileSync} from 'node:fs';
let raw='';process.stdin.setEncoding('utf8');for await(const c of process.stdin)raw+=c;
writeFileSync('request.json',raw);
const r=parseScenarioJson(raw);
process.stdout.write(stringifyScenarioJson({schema_version:r.schema_version,result:r.input,world:r.initial_world,calls:{resources:{},internal:{}}}));`,
    change: doc => {
      doc.simulation = {};
      doc.initial_world = {};
      for (const step of doc.steps) {
        step.input = { id: 'book-7' };
        step.checks = [
          {
            criterion_id: step.checks[0].criterion_id,
            target: 'result',
            path: '/id',
            op: 'equals',
            value: 'book-7',
          },
        ];
      }
      change(doc);
    },
  });
}
