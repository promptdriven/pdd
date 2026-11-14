import { execFile, execFileSync } from 'node:child_process';
import { chmodSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, relative, sep } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { promisify } from 'node:util';

const execFileAsync = promisify(execFile);
const root = fileURLToPath(new URL('../..', import.meta.url));
const srcDir = join(root, 'src');

export const SEAM_LOADS_RECORD = join(root, 'test/fixtures/seam-loads.txt');
export const REPLAY_CHILD_EXPR = 'source.identity({root:process.argv[1],tests:JSON.parse(process.argv[2])}).files';

const ASYNC_SEAM_BRIDGE_PROBES = new Set([
  'cli:approve-automatic', 'cli:approve-automatic-tests',
  'cli:test', 'cli:lint', 'cli:simulate', 'cli:contracts', 'cli:contracts-sync',
  'cli:jobs', 'cli:mcp', 'child:try-doors-launcher',
]);

const PROBE_HOOK = `import { registerHooks } from 'node:module';
import { appendFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
const out = process.env.PROBE_OUT;
registerHooks({
  resolve(specifier, context, nextResolve) {
    const res = nextResolve(specifier, context);
    if (res.url && res.url.startsWith('file://')) {
      const parent = context.parentURL && context.parentURL.startsWith('file://') ? fileURLToPath(context.parentURL) : '';
      appendFileSync(out, parent + '\\t' + fileURLToPath(res.url) + '\\n');
    }
    return res;
  }
});
`;

export function findTarjanCycles(adj) {
  let idx = 0;
  const indices = new Map();
  const low = new Map();
  const stack = [];
  const onStack = new Set();
  const cycles = [];
  const strong = v => {
    indices.set(v, idx);
    low.set(v, idx);
    idx++;
    stack.push(v);
    onStack.add(v);
    for (const w of adj.get(v) ?? []) {
      if (!indices.has(w)) {
        strong(w);
        low.set(v, Math.min(low.get(v), low.get(w)));
      } else if (onStack.has(w)) {
        low.set(v, Math.min(low.get(v), indices.get(w)));
      }
    }
    if (low.get(v) === indices.get(v)) {
      const scc = [];
      let w;
      do {
        w = stack.pop();
        onStack.delete(w);
        scc.push(w);
      } while (w !== v);
      if (scc.length > 1) cycles.push(scc.sort().join(' <-> '));
    }
  };
  for (const v of adj.keys()) {
    if (!indices.has(v)) strong(v);
  }
  return cycles.sort();
}

const srcName = full => {
  if (!full) return null;
  const name = relative(srcDir, full).split(sep).join('/');
  return name.endsWith('.mjs') && !name.startsWith('../') ? name : null;
};

export async function inBatches(items, run) {
  const results = [];
  for (let i = 0; i < items.length; i += 8) results.push(...await Promise.all(items.slice(i, i + 8).map(run)));
  return results;
}

function analyzeProbeLines(lines, ignoreAsyncSeamOutgoing) {
  const loaded = new Set();
  const adj = new Map();
  for (const line of lines) {
    const tab = line.indexOf('\t');
    const parent = srcName(line.slice(0, tab));
    const name = srcName(line.slice(tab + 1));
    if (!name) continue;
    loaded.add(name);
    if (parent && parent !== name && !(ignoreAsyncSeamOutgoing && parent === 'runtime-seam.mjs' && !name.startsWith('runtime/'))) {
      const from = `src/${parent}`;
      if (!adj.has(from)) adj.set(from, new Set());
      adj.get(from).add(`src/${name}`);
    }
  }
  return { loaded: [...loaded].sort(), cycles: findTarjanCycles(adj) };
}

export function seamWorld() {
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-seam5-'));
  const home = join(scratch, 'home');
  const stateDir = join(scratch, 'state');
  const nonGit = join(scratch, 'nongit');
  const repo = join(scratch, 'repo');
  const fakeBin = join(scratch, 'bin');
  for (const d of [home, stateDir, nonGit, join(repo, 'prompts'), join(repo, 'user_stories'), join(repo, 'tests'), fakeBin]) {
    mkdirSync(d, { recursive: true });
  }
  for (const tool of ['gh', 'claude', 'gemini', 'agy', 'herdr']) {
    const p = join(fakeBin, tool);
    writeFileSync(p, '#!/bin/sh\nexit 1\n');
    chmodSync(p, 0o755);
  }
  writeFileSync(join(fakeBin, 'codex'), '#!/bin/sh\nif [ "$1" = "login" ]; then echo "Logged in"; exit 0; fi\nexit 1\n');
  chmodSync(join(fakeBin, 'codex'), 0o755);
  writeFileSync(join(repo, 'prompts/a.prompt.md'), '# A\n\nDo a.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(repo, 'user_stories/a.md'), '# A\n\nI can a.\n\n## Acceptance criteria\n\n1. A.\n');
  writeFileSync(
    join(repo, 'tests/a.json'),
    JSON.stringify({
      schema_version: 'prompt-runtime.program-scenario.v1',
      story_path: 'user_stories/a.md',
      criteria: [{ id: 'AC1', text: 'A.' }],
      initial_world: {},
      steps: [{ step_id: 's1', entry_path: 'prompts/a.prompt.md', operation: 'a', input: {}, checks: [{ criterion_id: 'AC1', target: 'result', path: '', op: 'equals', value: 1 }] }],
    }) + '\n',
  );
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=T', '-c', 'user.email=t@e.c', 'commit', '-q', '-m', 'init'], { cwd: repo });
  const preload = join(scratch, 'hook.mjs');
  writeFileSync(preload, PROBE_HOOK);

  const env = { PATH: `${fakeBin}:/usr/bin:/bin`, HOME: home, PDD_STATE_DIR: stateDir, PDD_RUNTIME_URL: 'http://127.0.0.1:9' };
  const bin = join(root, 'bin/pdd.mjs');
  const moduleUrl = rel => pathToFileURL(join(root, rel)).href;
  const replayScript = `import {source} from ${JSON.stringify(moduleUrl('src/runtime-seam.mjs'))};process.stdout.write(JSON.stringify(${REPLAY_CHILD_EXPR}));`;
  const launcherScript = 'import(process.argv[1]).then(async ({ runShim }) => { process.exitCode = await runShim(process.argv[2], process.argv.slice(3)); }).catch(() => { process.exitCode = 125; });';
  const libProbe = name => [`lib:${name}`, ['--input-type=module', '-e', `await import(${JSON.stringify(moduleUrl(`src/${name}`))})`], nonGit];
  const probes = [
    ['cli:--help', [bin, '--help'], repo],
    ['cli:help-topic', [bin, 'help', 'prompting'], repo],
    ['cli:--version', [bin, '--version'], repo],
    ['cli:completion', [bin, 'completion', 'bash'], repo],
    ['cli:setup', [bin, 'setup', '--yes'], repo],
    ['cli:files', [bin, 'files', '--json'], repo],
    ['cli:owner', [bin, 'owner', 'prompts/a.prompt.md', '--json'], repo],
    ['cli:interface-draft', [bin, 'interface', 'draft', 'prompts/a.prompt.md', '--json'], repo],
    ['cli:approve', [bin, 'approve', 'prompts/missing.prompt.md', '--said', 'ok'], repo],
    ['cli:approve-automatic', [bin, 'approve', 'prompts/a.prompt.md', '--automatic'], repo],
    ['cli:approve-automatic-tests', [bin, 'approve', 'prompts/a.prompt.md', '--automatic', '--tests', 'npm test'], repo],
    ['cli:test', [bin, 'test', 'a'], repo],
    ['cli:lint', [bin, 'lint', '--local'], repo],
    ['cli:simulate', [bin, 'simulate', '--stop', 'a'], repo],
    ['cli:contracts', [bin, 'contracts'], repo],
    ['cli:contracts-sync', [bin, 'contracts', 'sync'], repo],
    ['cli:jobs', [bin, 'jobs'], repo],
    ['cli:mcp', [bin, 'mcp'], repo],
    ['cli:metrics', [bin, 'metrics', '--json'], repo],
    ['cli:graph', [bin, 'graph', '--issue', '1'], nonGit],
    ['cli:dependencies-prepare', [bin, 'dependencies', 'prepare'], nonGit],
    ['cli:dependencies-complete', [bin, 'dependencies', 'complete', '--input', '-'], nonGit],
    ['cli:product-status', [bin, 'product', 'status'], repo],
    ['cli:product-next', [bin, 'product', 'next'], repo],
    ['cli:product-start', [bin, 'product', 'start', 'r1', '--no-run'], repo],
    ['cli:workflow-list', [bin, 'workflow', 'list'], repo],
    ['cli:workflow-status', [bin, 'workflow', 'status'], repo],
    ['cli:workflow-run', [bin, 'workflow', 'run', 'feature', '1'], nonGit],
    ['cli:workflow-done', [bin, 'workflow', 'done', 'story'], nonGit],
    ['cli:workflow-publish', [bin, 'workflow', 'publish', '1'], nonGit],
    ['cli:workflow-view', [bin, 'workflow', 'view', '1'], nonGit],
    ['cli:workflow-cost', [bin, 'workflow', 'cost', '1'], nonGit],
    ['cli:workflow-prove', [bin, 'workflow', 'prove', '1', '--test', 'true', '--expect', 'ok'], nonGit],
    ['cli:autopilot-status', [bin, 'autopilot', 'status'], nonGit],
    ['cli:autopilot-doctor', [bin, 'autopilot', 'doctor'], repo],
    ['cli:autopilot-regressions', [bin, 'autopilot', 'regressions'], nonGit],
    ['cli:autopilot-alerts', [bin, 'autopilot', 'alerts', 'clear'], nonGit],
    ['cli:autopilot-off', [bin, 'autopilot', 'off'], nonGit],
    ['child:workflow-worker-completion', [join(root, 'src/workflow-worker-completion.mjs'), '{}'], nonGit],
    ['child:workflow-replay-selector', ['--input-type=module', '-e', replayScript, repo, JSON.stringify(['tests/a.json'])], nonGit],
    ['child:try-doors-launcher', ['--input-type=commonjs', '-e', launcherScript, '--', moduleUrl('src/try-doors.mjs'), join(scratch, 'missing.door.json')], nonGit],
    ['child:scripts/autopilot-smoke.mjs', [join(root, 'scripts/autopilot-smoke.mjs')], nonGit],
    ['child:scripts/route-runtime-issues.mjs', [join(root, 'scripts/route-runtime-issues.mjs')], nonGit],
    ['tick:autopilot-launcher', [join(root, 'src/autopilot-launcher.mjs'), join(scratch, 'missing-state.json')], nonGit],
    libProbe('svg-layout.mjs'),
    libProbe('prompt-approve.mjs'),
    libProbe('file-owner.mjs'),
    libProbe('agent-adapters.mjs'),
    libProbe('product.mjs'),
    libProbe('autopilot-doctor.mjs'),
  ];

  const run = (importUrl, args, cwd, extraEnv = {}) => {
    const child = execFileAsync(process.execPath, ['--import', importUrl, ...args], { cwd, env: { ...env, ...extraEnv }, timeout: 8000 });
    child.child.stdin?.end();
    return child.then(({ stdout, stderr }) => ({ status: 0, stdout, stderr }), error => ({ status: error.code, stdout: error.stdout, stderr: error.stderr }));
  };
  let seq = 0;
  const probe = async ([key, args, cwd]) => {
    const outFile = join(scratch, `out-${++seq}.txt`);
    writeFileSync(outFile, '');
    await run(pathToFileURL(preload).href, args, cwd, { PROBE_OUT: outFile });
    const lines = readFileSync(outFile, 'utf8').split('\n').filter(Boolean);
    return [key, analyzeProbeLines(lines, ASYNC_SEAM_BRIDGE_PROBES.has(key))];
  };
  const probeAll = async () => new Map(await inBatches(probes, probe));
  const remove = () => rmSync(scratch, { recursive: true, force: true });
  return { scratch, repo, nonGit, bin, moduleUrl, probes, run, probeAll, remove };
}
