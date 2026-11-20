import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  SHORT_SCENARIO_SCHEMA,
  V1_SCENARIO_SCHEMA,
  compileScenario,
  compileScenarioText,
} from '../src/scenario-compile.mjs';

const REPO_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const BIN_PDD = join(REPO_ROOT, 'bin/pdd.mjs');

const GRANT_STORY = [
  '# Employee self-service grant read',
  '',
  'As an employee, I want to read my own grant without delegation fields set.',
  '',
  '## Acceptance criteria',
  '',
  '1. Reading an employee grant returns the grant record when delegation fields are null.',
  '',
].join('\n');

function makeTempRepo(t, files) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-patch-null-3568-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const env = {
    ...process.env,
    GIT_AUTHOR_NAME: 'PDD Test',
    GIT_AUTHOR_EMAIL: 'pdd-test@example.com',
    GIT_COMMITTER_NAME: 'PDD Test',
    GIT_COMMITTER_EMAIL: 'pdd-test@example.com',
  };
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: dir, env });
  for (const [rel, body] of Object.entries(files)) {
    const abs = join(dir, rel);
    mkdirSync(dirname(abs), { recursive: true });
    writeFileSync(abs, typeof body === 'string' ? body : `${JSON.stringify(body, null, 2)}\n`);
  }
  execFileSync('git', ['add', '.'], { cwd: dir, env });
  execFileSync('git', ['commit', '-q', '-m', 'init'], { cwd: dir, env });
  return dir;
}

function runPddSubprocess(args, cwd, stateDir, homeDir) {
  return spawnSync(process.execPath, [BIN_PDD, ...args], {
    cwd,
    encoding: 'utf8',
    timeout: 15000,
    env: {
      PATH: process.env.PATH,
      HOME: homeDir,
      PDD_STATE_DIR: stateDir,
    },
  });
}

test('compileScenario warns on top-level and nested explicit null in step patch, preserves RFC 7396 deletion, escapes JSON Pointers, and ignores nulls inside arrays', () => {
  const shortDoc = {
    schema_version: SHORT_SCENARIO_SCHEMA,
    entry_path: 'prompts/grant.prompt.md',
    seeds: {
      base_input: {
        top_nullable: 'present',
        actor: {
          user_id: 'emp-1',
          delegation_id: 'del-1',
          delegator_id: 'mgr-1',
        },
        tags: ['initial'],
        items: [{ note: 'filled' }],
      },
    },
    steps: [
      {
        id: 'finance-reads-grant',
        op: 'read_grant',
        from: 'base_input',
        patch: {
          top_nullable: null,
          absent_key: null,
          actor: {
            delegation_id: null,
            delegator_id: null,
          },
          'a/b': {
            'c~d': null,
          },
          tags: [null, 'kept'],
          items: [{ note: null }],
        },
        checks: {
          1: [['result', '/ok', '=', true]],
        },
      },
    ],
  };

  const res = compileScenario(shortDoc, {
    path: 'tests/P21-employee-self-service.json',
    storyPath: 'user_stories/P21-employee-self-service.md',
    storySource: GRANT_STORY,
  });

  assert.equal(res.refusal, null);
  assert.equal(res.changed, true);

  // Existing RFC 7396 mergePatch behavior remains intact (non-breaking).
  const compiledInput = res.doc.steps[0].input;
  assert.equal(Object.hasOwn(compiledInput, 'top_nullable'), false);
  assert.equal(Object.hasOwn(compiledInput, 'absent_key'), false);
  assert.equal(compiledInput.actor.user_id, 'emp-1');
  assert.equal(Object.hasOwn(compiledInput.actor, 'delegation_id'), false);
  assert.equal(Object.hasOwn(compiledInput.actor, 'delegator_id'), false);
  // Arrays are replaced wholesale under RFC 7396, keeping nulls intact.
  assert.deepEqual(compiledInput.tags, [null, 'kept']);
  assert.deepEqual(compiledInput.items, [{ note: null }]);

  // Exactly 5 null-property warnings (arrays produce zero warnings).
  assert.equal(res.warnings.length, 5, JSON.stringify(res.warnings, null, 2));
  assert.deepEqual(
    res.warnings.map(w => ({
      code: w.code,
      step_id: w.step_id,
      step: w.step,
      field_path: w.field_path,
      pointer: w.pointer,
      exists_on_target: w.exists_on_target,
    })),
    [
      {
        code: 'patch-null-deletes-key',
        step_id: 'finance-reads-grant',
        step: 1,
        field_path: 'top_nullable',
        pointer: '/top_nullable',
        exists_on_target: true,
      },
      {
        code: 'patch-null-deletes-key',
        step_id: 'finance-reads-grant',
        step: 1,
        field_path: 'absent_key',
        pointer: '/absent_key',
        exists_on_target: false,
      },
      {
        code: 'patch-null-deletes-key',
        step_id: 'finance-reads-grant',
        step: 1,
        field_path: 'actor.delegation_id',
        pointer: '/actor/delegation_id',
        exists_on_target: true,
      },
      {
        code: 'patch-null-deletes-key',
        step_id: 'finance-reads-grant',
        step: 1,
        field_path: 'actor.delegator_id',
        pointer: '/actor/delegator_id',
        exists_on_target: true,
      },
      {
        code: 'patch-null-deletes-key',
        step_id: 'finance-reads-grant',
        step: 1,
        field_path: 'a/b.c~d',
        pointer: '/a~1b/c~0d',
        exists_on_target: false,
      },
    ],
  );

  const delegationWarn = res.warnings.find(w => w.field_path === 'actor.delegation_id');
  assert.match(delegationWarn.message, /^Warning: tests\/P21-employee-self-service\.json step "finance-reads-grant":/);
  assert.match(delegationWarn.message, /"patch" sets "actor\.delegation_id" to null/);
  assert.match(delegationWarn.message, /deletes the existing key \(RFC 7396 Merge Patch\)/);
  assert.match(delegationWarn.message, /Use "set": \{ "\/actor\/delegation_id": null \}/);

  const absentWarn = res.warnings.find(w => w.field_path === 'absent_key');
  assert.match(absentWarn.message, /key is not on base/);
  assert.match(absentWarn.message, /Use "set": \{ "\/absent_key": null \}/);

  const escapedWarn = res.warnings.find(w => w.field_path === 'a/b.c~d');
  assert.match(escapedWarn.message, /Use "set": \{ "\/a~1b\/c~0d": null \}/);
});

test('compileScenarioText warns on world patch, nested $use/$from/$seed patch, seed-level patch without duplicating across steps, and macro-expanded null in patch', () => {
  const raw = JSON.stringify({
    schema_version: SHORT_SCENARIO_SCHEMA,
    entry_path: 'prompts/grant.prompt.md',
    seeds: {
      base_world: {
        active_session: { token: 'tok-1', role: 'employee' },
        owner: 'emp-1',
      },
      base_actor: {
        user_id: 'emp-1',
        delegation_id: 'del-1',
      },
      guest_actor: {
        user_id: 'guest',
        delegation_id: null,
      },
      derived_actor: {
        $use: 'base_actor',
        patch: { delegation_id: null },
      },
    },
    initial_world: {
      $use: 'base_world',
      patch: { active_session: { token: null } },
    },
    steps: [
      {
        id: 'use-derived-1',
        op: 'read_grant',
        from: 'derived_actor',
        checks: { 1: [['result', '/ok', '=', true]] },
      },
      {
        id: 'use-derived-2',
        op: 'read_grant',
        from: 'derived_actor',
        checks: { 1: [['result', '/ok', '=', true]] },
      },
      {
        id: 'nested-from-in-input',
        op: 'read_grant',
        input: {
          primary: { $from: 'base_actor', patch: { delegation_id: null } },
          secondary: { $seed: 'base_actor', patch: { delegation_id: null } },
        },
        checks: { 1: [['result', '/ok', '=', true]] },
      },
      {
        id: 'macro-expanded-null-in-patch',
        op: 'read_grant',
        input: { actor: { user_id: 'emp-1', delegation_id: 'del-1' } },
        patch: { actor: { $use: 'guest_actor' } },
        checks: { 1: [['result', '/ok', '=', true]] },
      },
    ],
  });

  const res = compileScenarioText(raw, {
    path: 'tests/nested-patches.json',
    storyPath: 'user_stories/P21-employee-self-service.md',
    storySource: GRANT_STORY,
  });

  assert.equal(res.refusal, null);
  assert.equal(res.changed, true);

  // Seed warning appears once under seeds.derived_actor with step_id: null (not duplicated for step 2).
  const seedWarns = res.warnings.filter(w => w.section === 'seeds.derived_actor.patch');
  assert.equal(seedWarns.length, 1);
  assert.equal(seedWarns[0].step_id, null);
  assert.equal(seedWarns[0].step, null);
  assert.match(seedWarns[0].message, /^Warning: tests\/nested-patches\.json seeds\.derived_actor:/);

  // World patch warning reports initial_world with step_id: null.
  const worldWarns = res.warnings.filter(w => w.section === 'initial_world.patch');
  assert.equal(worldWarns.length, 1);
  assert.equal(worldWarns[0].step_id, null);
  assert.equal(worldWarns[0].pointer, '/active_session/token');
  assert.match(worldWarns[0].message, /^Warning: tests\/nested-patches\.json initial_world:/);
  assert.match(worldWarns[0].message, /Use "set": \{ "\/active_session\/token": null \}/);

  // Nested $from and $seed inside step input report step id and subpath.
  const primaryWarn = res.warnings.find(w => w.section === 'steps[2].input.primary.patch');
  assert.ok(primaryWarn);
  assert.equal(primaryWarn.step_id, 'nested-from-in-input');
  assert.match(primaryWarn.message, /step "nested-from-in-input" \(input\.primary\):/);

  const secondaryWarn = res.warnings.find(w => w.section === 'steps[2].input.secondary.patch');
  assert.ok(secondaryWarn);
  assert.equal(secondaryWarn.step_id, 'nested-from-in-input');
  assert.match(secondaryWarn.message, /step "nested-from-in-input" \(input\.secondary\):/);

  // Macro-expanded null inside step.patch is caught too.
  const expandedNullWarn = res.warnings.find(w => w.step_id === 'macro-expanded-null-in-patch');
  assert.ok(expandedNullWarn);
  assert.equal(expandedNullWarn.field_path, 'actor.delegation_id');
  assert.equal(expandedNullWarn.pointer, '/actor/delegation_id');
  assert.equal(expandedNullWarn.exists_on_target, true);
  assert.equal(Object.hasOwn(res.doc.steps[3].input.actor, 'delegation_id'), false);
});

test('Using "set" to assign explicit null produces zero warnings and preserves null properties', () => {
  const shortDoc = {
    schema_version: SHORT_SCENARIO_SCHEMA,
    entry_path: 'prompts/grant.prompt.md',
    seeds: {
      base_input: {
        actor: {
          user_id: 'emp-1',
          delegation_id: 'del-1',
          delegator_id: 'mgr-1',
        },
        'a/b': {
          'c~d': 'old',
        },
      },
      base_world: {
        active_session: { token: 'tok-1' },
      },
    },
    initial_world: {
      $use: 'base_world',
      set: {
        '/active_session/token': null,
      },
    },
    steps: [
      {
        id: 'finance-reads-grant',
        op: 'read_grant',
        from: 'base_input',
        patch: {
          actor: { user_id: 'emp-2' },
        },
        set: {
          '/actor/delegation_id': null,
          '/actor/delegator_id': null,
          '/a~1b/c~0d': null,
        },
        checks: {
          1: [['result', '/ok', '=', true]],
        },
      },
    ],
  };

  const res = compileScenario(shortDoc, {
    path: 'tests/P22-clean-set.json',
    storyPath: 'user_stories/P21-employee-self-service.md',
    storySource: GRANT_STORY,
  });

  assert.equal(res.refusal, null);
  assert.equal(res.changed, true);
  assert.deepEqual(res.warnings, []);

  assert.equal(Object.hasOwn(res.doc.initial_world.active_session, 'token'), true);
  assert.equal(res.doc.initial_world.active_session.token, null);

  const compiledInput = res.doc.steps[0].input;
  assert.equal(compiledInput.actor.user_id, 'emp-2');
  assert.equal(Object.hasOwn(compiledInput.actor, 'delegation_id'), true);
  assert.equal(compiledInput.actor.delegation_id, null);
  assert.equal(Object.hasOwn(compiledInput.actor, 'delegator_id'), true);
  assert.equal(compiledInput.actor.delegator_id, null);
  assert.equal(Object.hasOwn(compiledInput['a/b'], 'c~d'), true);
  assert.equal(compiledInput['a/b']['c~d'], null);

  // Standard V1 pass-through also returns empty warnings array.
  const v1Res = compileScenario(res.doc, {
    path: 'tests/P22-clean-set.json',
    storyPath: 'user_stories/P21-employee-self-service.md',
    storySource: GRANT_STORY,
  });
  assert.equal(v1Res.changed, false);
  assert.deepEqual(v1Res.warnings, []);
});

test('CLI subprocesses: pdd lint --local and pdd lint --emit-v1 surface patch-null warnings cleanly while keeping --emit-v1 stdout valid JSON', t => {
  const promptText = [
    '# Employee grant service',
    '',
    'Expose `read_grant({ actor })` returning `{ ok: boolean }`.',
    '',
    '## Domain decisions',
    '',
    'Accept an `actor` object with `user_id` and nullable `delegation_id` and `delegator_id` fields.',
    '',
  ].join('\n');

  const files = {
    'prompts/grant.prompt.md': promptText,
    'user_stories/P21-employee-self-service.md': GRANT_STORY,
    'tests/P21-employee-self-service.json': {
      schema_version: SHORT_SCENARIO_SCHEMA,
      entry_path: 'prompts/grant.prompt.md',
      seeds: {
        base_world: { session: { token: 'abc' } },
        base_input: {
          actor: {
            user_id: 'emp-1',
            delegation_id: 'del-1',
            delegator_id: 'mgr-1',
          },
        },
      },
      initial_world: {
        $use: 'base_world',
        patch: { session: { token: null } },
      },
      steps: [
        {
          id: 'finance-reads-grant',
          op: 'read_grant',
          from: 'base_input',
          patch: {
            actor: {
              delegation_id: null,
              delegator_id: null,
            },
          },
          checks: {
            1: [['result', '/ok', '=', true]],
          },
        },
      ],
    },
    'user_stories/P22-clean-set.md': GRANT_STORY,
    'tests/P22-clean-set.json': {
      schema_version: SHORT_SCENARIO_SCHEMA,
      entry_path: 'prompts/grant.prompt.md',
      seeds: {
        base_input: {
          actor: {
            user_id: 'emp-1',
            delegation_id: 'del-1',
            delegator_id: 'mgr-1',
          },
        },
      },
      steps: [
        {
          id: 'employee-reads-grant',
          op: 'read_grant',
          from: 'base_input',
          set: {
            '/actor/delegation_id': null,
            '/actor/delegator_id': null,
          },
          checks: {
            1: [['result', '/ok', '=', true]],
          },
        },
      ],
    },
  };

  const repo = makeTempRepo(t, files);
  const stateDir = mkdtempSync(join(tmpdir(), 'pdd-patch-null-state-'));
  const homeDir = mkdtempSync(join(tmpdir(), 'pdd-patch-null-home-'));
  t.after(() => {
    rmSync(stateDir, { recursive: true, force: true });
    rmSync(homeDir, { recursive: true, force: true });
  });

  // 1. pdd lint --local (plain text) reports P21 patch-null warnings and zero warnings for P22.
  const localText = runPddSubprocess(['lint', '--local'], repo, stateDir, homeDir);
  assert.equal(localText.status, 0, localText.stderr);
  assert.match(localText.stdout, /Warning: tests\/P21-employee-self-service\.json step "finance-reads-grant": "patch" sets "actor\.delegation_id" to null/);
  assert.match(localText.stdout, /Use "set": \{ "\/actor\/delegation_id": null \}/);
  assert.match(localText.stdout, /Warning: tests\/P21-employee-self-service\.json step "finance-reads-grant": "patch" sets "actor\.delegator_id" to null/);
  assert.match(localText.stdout, /Warning: tests\/P21-employee-self-service\.json initial_world: "patch" sets "session\.token" to null/);
  assert.doesNotMatch(localText.stdout, /P22-clean-set/);

  // 2. pdd lint --local --json includes the warnings in JSON warnings array.
  const localJson = runPddSubprocess(['lint', '--local', '--json'], repo, stateDir, homeDir);
  assert.equal(localJson.status, 0, localJson.stderr);
  const localParsed = JSON.parse(localJson.stdout);
  const patchWarnings = localParsed.warnings.filter(w => w.includes('RFC 7396 Merge Patch'));
  assert.equal(patchWarnings.length, 3, JSON.stringify(localParsed.warnings, null, 2));

  // 3. pdd lint --local P22-clean-set (Story-scoped) reports zero patch-null warnings.
  const localClean = runPddSubprocess(['lint', '--local', '--json', 'P22-clean-set'], repo, stateDir, homeDir);
  assert.equal(localClean.status, 0, localClean.stderr);
  const cleanParsed = JSON.parse(localClean.stdout);
  assert.deepEqual(cleanParsed.warnings.filter(w => w.includes('RFC 7396')), []);

  // 4. pdd lint --emit-v1 P21-employee-self-service prints pure valid V1 JSON on stdout and warnings on stderr.
  const emitPlain = runPddSubprocess(['lint', '--emit-v1', 'P21-employee-self-service'], repo, stateDir, homeDir);
  assert.equal(emitPlain.status, 0, emitPlain.stderr);
  const emittedScenario = JSON.parse(emitPlain.stdout);
  assert.equal(emittedScenario.schema_version, V1_SCENARIO_SCHEMA);
  assert.equal(Object.hasOwn(emittedScenario.steps[0].input.actor, 'delegation_id'), false);
  assert.match(emitPlain.stderr, /Warning: tests\/P21-employee-self-service\.json step "finance-reads-grant": "patch" sets "actor\.delegation_id" to null/);
  assert.match(emitPlain.stderr, /Use "set": \{ "\/actor\/delegation_id": null \}/);
  assert.match(emitPlain.stderr, /Warning: tests\/P21-employee-self-service\.json initial_world: "patch" sets "session\.token" to null/);

  // 5. pdd lint --emit-v1 P21-employee-self-service --json surfaces warnings in JSON and keeps stderr empty.
  const emitJson = runPddSubprocess(['lint', '--emit-v1', '--json', 'P21-employee-self-service'], repo, stateDir, homeDir);
  assert.equal(emitJson.status, 0, emitJson.stderr);
  assert.equal(emitJson.stderr, '');
  const emitJsonParsed = JSON.parse(emitJson.stdout);
  assert.equal(emitJsonParsed.ok, true);
  assert.equal(emitJsonParsed.warnings.length, 3);
  assert.equal(emitJsonParsed.scenarios[0].changed, true);
  assert.deepEqual(emitJsonParsed.scenarios[0].warnings, emitJsonParsed.warnings);

  // 6. pdd lint --emit-v1 P22-clean-set has zero stderr warnings and preserves null keys in stdout JSON.
  const emitClean = runPddSubprocess(['lint', '--emit-v1', 'P22-clean-set'], repo, stateDir, homeDir);
  assert.equal(emitClean.status, 0, emitClean.stderr);
  assert.equal(emitClean.stderr, '');
  const cleanEmitted = JSON.parse(emitClean.stdout);
  assert.equal(Object.hasOwn(cleanEmitted.steps[0].input.actor, 'delegation_id'), true);
  assert.equal(cleanEmitted.steps[0].input.actor.delegation_id, null);
  assert.equal(Object.hasOwn(cleanEmitted.steps[0].input.actor, 'delegator_id'), true);
  assert.equal(cleanEmitted.steps[0].input.actor.delegator_id, null);

  // 7. pdd lint --emit-v1 --write P21-employee-self-service emits warnings on stderr and writes canonical v1 cleanly.
  const emitWrite = runPddSubprocess(['lint', '--emit-v1', '--write', 'P21-employee-self-service'], repo, stateDir, homeDir);
  assert.equal(emitWrite.status, 0, emitWrite.stderr);
  assert.match(emitWrite.stdout, /Wrote tests\/P21-employee-self-service\.json \(prompt-runtime\.program-scenario\.v1\)\./);
  assert.match(emitWrite.stderr, /Warning: tests\/P21-employee-self-service\.json step "finance-reads-grant": "patch" sets "actor\.delegation_id" to null/);
  const writtenDisk = JSON.parse(readFileSync(join(repo, 'tests/P21-employee-self-service.json'), 'utf8'));
  assert.equal(writtenDisk.schema_version, V1_SCENARIO_SCHEMA);

  // 8. pdd lint --emit-v1 --write --json on a fresh repo puts warnings in JSON and keeps stderr empty.
  const repo2 = makeTempRepo(t, files);
  const emitWriteJson = runPddSubprocess(['lint', '--emit-v1', '--write', '--json', 'P21-employee-self-service'], repo2, stateDir, homeDir);
  assert.equal(emitWriteJson.status, 0, emitWriteJson.stderr);
  assert.equal(emitWriteJson.stderr, '');
  const writeJsonParsed = JSON.parse(emitWriteJson.stdout);
  assert.equal(writeJsonParsed.ok, true);
  assert.equal(writeJsonParsed.wrote, true);
  assert.equal(writeJsonParsed.warnings.length, 3);
  assert.deepEqual(writeJsonParsed.files[0].warnings, writeJsonParsed.warnings);
});
