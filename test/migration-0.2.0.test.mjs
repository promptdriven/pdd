import './helpers/test-home.mjs';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { existsSync, lstatSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';
import { setupSkills, syncOwnedUserSkills } from '../src/shared/skills-install.mjs';
import { createDependencyReadPorts, readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { projectIssueGraph } from '../src/autopilot/graph/dag.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const BIN = join(ROOT, 'bin', 'pdd.mjs');

function tempDir(t, prefix) {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), prefix)));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function writeMarkedSkill(parent, name, version = '0.1.42') {
  const dir = join(parent, name);
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, 'SKILL.md'), `---\nname: ${name}\ndescription: Old skill\nmetadata:\n  pdd-skills: ${version}\n---\n`);
  writeFileSync(join(dir, '.pdd-skill.json'), JSON.stringify({ package: 'pdd', version, digest: 'old-digest' }) + '\n');
}

function writeUnmarkedSkill(parent, name) {
  const dir = join(parent, name);
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, 'SKILL.md'), `---\nname: ${name}\ndescription: User-managed skill\n---\n`);
}

function git(cwd, args) {
  const env = {
    ...process.env,
    GIT_AUTHOR_NAME: 'Test',
    GIT_AUTHOR_EMAIL: 'test@example.test',
    GIT_COMMITTER_NAME: 'Test',
    GIT_COMMITTER_EMAIL: 'test@example.test',
  };
  return execFileSync('git', args, { cwd, env, encoding: 'utf8' });
}

test('0.1.42 -> 0.2.0 skill sync removes marked split skills (including under Claude plugin) while preserving unmarked and symlinked folders', t => {
  const sandbox = tempDir(t, 'pdd-mig-skills-');
  const home = join(sandbox, 'home');
  const stateDir = join(sandbox, 'state');
  const externalTarget = join(sandbox, 'external-skill');
  mkdirSync(home, { recursive: true });
  mkdirSync(stateDir, { recursive: true });
  mkdirSync(externalTarget, { recursive: true });
  writeFileSync(join(externalTarget, 'SKILL.md'), '---\nname: pdd-graph\ndescription: Symlinked external\n---\n');

  const agentsSkills = join(home, '.agents', 'skills');
  const claudeBase = join(home, '.claude');
  const claudeSkills = join(claudeBase, 'skills');
  mkdirSync(join(claudeBase, 'plugins'), { recursive: true });
  writeFileSync(
    join(claudeBase, 'plugins', 'installed_plugins.json'),
    JSON.stringify({ plugins: { 'pdd@promptdriven': [{ installPath: join(claudeBase, 'plugins/cache/pdd') }] } }),
  );

  // Seed Codex (~/.agents/skills): marked old split skills + unmarked custom copy + symlinked split skill.
  writeMarkedSkill(agentsSkills, 'pdd-feature', '0.1.42');
  writeMarkedSkill(agentsSkills, 'pdd-bug', '0.1.42');
  writeUnmarkedSkill(agentsSkills, 'pdd-prompting');
  symlinkSync(externalTarget, join(agentsSkills, 'pdd-graph'));

  // Seed Claude (~/.claude/skills) with Claude plugin installed: marked old split skills + unmarked + symlinked.
  writeMarkedSkill(claudeSkills, 'pdd-feature', '0.1.42');
  writeMarkedSkill(claudeSkills, 'pdd-small-change', '0.1.42');
  writeMarkedSkill(claudeSkills, 'pdd-product', '0.1.42');
  writeUnmarkedSkill(claudeSkills, 'pdd-bug');
  symlinkSync(externalTarget, join(claudeSkills, 'pdd-graph'));

  // 1. setupSkills installs /pdd in Codex, skips copying /pdd into plugin-managed Claude,
  //    AND STILL cleans marked retired split skills in BOTH Codex and plugin-managed Claude!
  const results = setupSkills({ packageRoot: ROOT, cwd: sandbox, home, env: { HOME: home, PATH: '' } });
  const codex = results.find(r => r.agent === 'Codex');
  const claude = results.find(r => r.agent === 'Claude');
  assert.ok(codex && claude);

  assert.equal(existsSync(join(agentsSkills, 'pdd', 'SKILL.md')), true);
  assert.equal(existsSync(join(agentsSkills, 'pdd-feature')), false);
  assert.equal(existsSync(join(agentsSkills, 'pdd-bug')), false);
  assert.equal(existsSync(join(agentsSkills, 'pdd-prompting', 'SKILL.md')), true, 'unmarked skill preserved');
  assert.equal(lstatSync(join(agentsSkills, 'pdd-graph')).isSymbolicLink(), true, 'symlinked skill preserved');

  assert.equal(claude.pluginManaged, true);
  assert.equal(existsSync(join(claudeSkills, 'pdd')), false, 'plugin-managed Claude must not duplicate /pdd');
  assert.equal(existsSync(join(claudeSkills, 'pdd-feature')), false, 'plugin-managed Claude removes marked retired pdd-feature');
  assert.equal(existsSync(join(claudeSkills, 'pdd-small-change')), false, 'plugin-managed Claude removes marked retired pdd-small-change');
  assert.equal(existsSync(join(claudeSkills, 'pdd-product')), false, 'plugin-managed Claude removes marked retired pdd-product');
  assert.equal(existsSync(join(claudeSkills, 'pdd-bug', 'SKILL.md')), true, 'unmarked skill in Claude preserved');
  assert.equal(lstatSync(join(claudeSkills, 'pdd-graph')).isSymbolicLink(), true, 'symlinked skill in Claude preserved');
  assert.ok(claude.removed.includes(join(claudeSkills, 'pdd-feature')));

  // 2. syncOwnedUserSkills also cleans marked retired split skills in plugin-managed Claude without installing /pdd!
  writeMarkedSkill(claudeSkills, 'pdd-prompting', '0.1.42');
  const synced = syncOwnedUserSkills({ packageRoot: ROOT, home, stateRoot: stateDir, force: true });
  assert.ok(synced.updated.includes(claudeSkills));
  assert.equal(existsSync(join(claudeSkills, 'pdd-prompting')), false);
  assert.equal(existsSync(join(claudeSkills, 'pdd')), false, 'sync must not copy /pdd into plugin-managed Claude');
  assert.equal(existsSync(join(claudeSkills, 'pdd-bug', 'SKILL.md')), true);
  assert.equal(lstatSync(join(claudeSkills, 'pdd-graph')).isSymbolicLink(), true);
});

test('0.1.42 -> 0.2.0 orphaned legacy paused workflow-runs hold is ignored gracefully and does not stick pdd graph', async t => {
  const repo = tempDir(t, 'pdd-mig-paused-hold-');
  const home = tempDir(t, 'pdd-mig-paused-home-');
  writeFileSync(join(repo, 'README.md'), '# Demo\n');
  git(repo, ['init', '-q', '-b', 'main']);
  git(repo, ['remote', 'add', 'origin', 'https://github.com/acme/demo.git']);
  git(repo, ['add', '.']);
  git(repo, ['commit', '-q', '-m', 'init']);

  // Seed an orphaned 0.1.42 paused workflow run with runtimeWait inside .git/pdd/runs/42/status.json.
  const runDir = join(repo, '.git', 'pdd', 'runs', '42');
  mkdirSync(runDir, { recursive: true });
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({
    v: 1,
    number: 42,
    repo: 'acme/demo',
    runId: 'legacy-run-42',
    root: join(repo, '.worktree-missing-42'),
    state: 'paused',
    runtimeWait: { state: 'waiting', until: Date.now() + 60_000 },
    areas: [],
    chats: [],
  }));

  const issue42 = {
    id: 4200,
    number: 42,
    html_url: 'https://github.com/acme/demo/issues/42',
    title: 'Upgrade issue',
    body: 'Body',
    state: 'open',
    user: { login: 'owner' },
    assignees: [],
    labels: [],
    updated_at: '2026-11-22T00:00:00Z',
    comments: 0,
  };

  const readPorts = {
    env: { HOME: home, PDD_STATE_DIR: join(home, 'state') },
    snapshotStore: null,
    execFile: async (file, args, opts = {}) => {
      if (file === 'gh' && args[0] === 'repo' && args[1] === 'view') {
        return {
          code: 0,
          stdout: JSON.stringify({
            nameWithOwner: 'acme/demo',
            defaultBranchRef: { name: 'main' },
            url: 'https://github.com/acme/demo',
          }),
          stderr: '',
        };
      }
      const res = spawnSync(file, args, { cwd: opts.cwd ?? repo, encoding: 'utf8' });
      return { code: res.status ?? 1, stdout: res.stdout ?? '', stderr: res.stderr ?? '' };
    },
    clock: { now: () => ({ iso: '2026-11-22T12:00:00Z' }) },
    authority: { read: async () => ({ authority: 'trusted' }) },
    readSuiteProgress: () => ({ state: 'none' }),
    github: {
      page: async ({ kind }) => ({ json: JSON.stringify({ items: kind === 'issues' ? [issue42] : [], next: '' }) }),
      issue: async () => ({ json: JSON.stringify(issue42) }),
    },
  };

  // Directly confirm native owners.read actually parsed .git/pdd/runs/42/status.json (runsKnown: true) and ignored the dead legacy paused hold.
  const issueKey = 'https://github.com/acme/demo/issues/42';
  const ports = createDependencyReadPorts({ cwd: repo }, readPorts);
  const observed = JSON.parse((await ports.owners.read({ repository: 'acme/demo', issues: [issueKey] })).json);
  assert.equal(observed.runsKnown, true, JSON.stringify(observed));
  assert.deepEqual(observed.runs, [], 'dead legacy paused workflow-runs record must not block occupancy or emit runtime wait');

  const { snapshot } = await readDependencySnapshot({ cwd: repo, repository: 'acme/demo' }, readPorts);

  const issue = snapshot.issues.find(i => i.key === issueKey);
  assert.ok(issue, 'issue #42 present in snapshot');
  assert.equal(issue.holds.includes('Waiting for the interpreter'), false, `unexpected interpreter hold: ${JSON.stringify(issue.holds)}`);
  assert.deepEqual(issue.runIds, []);

  const graph = projectIssueGraph({ snapshot });
  const node = graph.nodes.find(n => n.key === issueKey);
  assert.ok(node);
  assert.equal(node.executionState, 'idle');
  assert.equal(node.reasons.includes('Waiting for the interpreter'), false);
});

test('spawned bin/pdd.mjs workflow status prints actionable migration pointer to /pdd, pdd prove, and pdd autopilot', t => {
  const home = tempDir(t, 'pdd-mig-wf-home-');
  const res = spawnSync(process.execPath, [BIN, 'workflow', 'status'], {
    cwd: home,
    env: { HOME: home, PDD_STATE_DIR: join(home, 'state'), PATH: process.env.PATH },
    encoding: 'utf8',
    timeout: 15000,
  });
  assert.equal(res.status, 2);
  assert.equal(res.stdout, '');
  assert.match(res.stderr, /pdd workflow was removed/);
  assert.match(res.stderr, /\/pdd/);
  assert.match(res.stderr, /pdd prove/);
  assert.match(res.stderr, /pdd autopilot/);
  assert.doesNotMatch(res.stderr, /Unknown command "workflow"/);
});

test('spawned bin/pdd.mjs lint, lint --diff, native Story lint STORY, and prove --base --test --expect run end-to-end offline', t => {
  const repo = tempDir(t, 'pdd-mig-e2e-repo-');
  const home = tempDir(t, 'pdd-mig-e2e-home-');
  const env = { HOME: home, PDD_STATE_DIR: join(home, 'state'), PATH: process.env.PATH, PDD_RUNTIME_URL: 'http://127.0.0.1:9' };

  mkdirSync(join(repo, 'prompts'), { recursive: true });
  mkdirSync(join(repo, 'src'), { recursive: true });
  mkdirSync(join(repo, 'user_stories'), { recursive: true });
  mkdirSync(join(repo, 'test'), { recursive: true });

  writeFileSync(join(repo, 'package.json'), JSON.stringify({ name: 'demo', type: 'module', scripts: { test: 'node --test test/math.test.mjs' } }, null, 2) + '\n');
  writeFileSync(join(repo, 'prompts', 'math.prompt.md'), '# Math\n\nOwn `src/math.mjs`. Export `add(a, b)` returning `a + b`.\n\n## Dependencies\n\nNone.\n');
  writeFileSync(join(repo, 'src', 'math.mjs'), '// Prompt: prompts/math.prompt.md\nexport function add(a, b) { return a - b; }\n');
  writeFileSync(
    join(repo, 'user_stories', 'add-numbers.md'),
    '# Add numbers\n\nAs a developer, I want `add(2, 3)` to return `5`.\n\n## Acceptance criteria\n\n1. `add(2, 3)` returns `5`.\n',
  );
  writeFileSync(
    join(repo, 'test', 'math.test.mjs'),
    `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { add } from '../src/math.mjs';\ntest('add sums integers', () => { assert.equal(add(2, 3), 5, 'BUG_WRONG_SUM'); });\n`,
  );

  git(repo, ['init', '-q', '-b', 'main']);
  git(repo, ['add', '.']);
  git(repo, ['commit', '-q', '-m', 'base with bug']);
  const baseSha = git(repo, ['rev-parse', 'HEAD']).trim();

  // Fix the bug on HEAD so prove --base --test --expect contrasts failing base vs passing head.
  writeFileSync(join(repo, 'src', 'math.mjs'), '// Prompt: prompts/math.prompt.md\nexport function add(a, b) { return a + b; }\n');
  git(repo, ['add', 'src/math.mjs']);
  git(repo, ['commit', '-q', '-m', 'fix add']);

  // 1. Spawned `bin/pdd.mjs lint` (offline, 0 AI/network)
  const lintAll = spawnSync(process.execPath, [BIN, 'lint'], { cwd: repo, env, encoding: 'utf8', timeout: 15000 });
  assert.equal(lintAll.status, 0, lintAll.stderr);
  assert.match(lintAll.stdout, /Local lint: 0 errors/);

  // 2. Spawned `bin/pdd.mjs lint --diff <baseSha>`
  const lintDiff = spawnSync(process.execPath, [BIN, 'lint', '--diff', baseSha], { cwd: repo, env, encoding: 'utf8', timeout: 15000 });
  assert.equal(lintDiff.status, 0, lintDiff.stderr);

  // 3. Spawned native Story `bin/pdd.mjs lint user_stories/add-numbers.md`
  const lintStory = spawnSync(process.execPath, [BIN, 'lint', 'user_stories/add-numbers.md'], { cwd: repo, env, encoding: 'utf8', timeout: 15000 });
  assert.equal(lintStory.status, 0, lintStory.stderr);
  assert.match(lintStory.stdout, /Local lint: 0 errors/);

  // 4. Spawned `bin/pdd.mjs prove --base <baseSha> --test "node --test test/math.test.mjs" --expect "BUG_WRONG_SUM"`
  const proveRes = spawnSync(
    process.execPath,
    [BIN, 'prove', '--base', baseSha, '--test', 'node --test test/math.test.mjs', '--expect', 'BUG_WRONG_SUM'],
    { cwd: repo, env, encoding: 'utf8', timeout: 30000 },
  );
  assert.equal(proveRes.status, 0, `stdout:\n${proveRes.stdout}\nstderr:\n${proveRes.stderr}`);
  assert.match(proveRes.stdout, /Proved/);
});
