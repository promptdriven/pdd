import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync, readdirSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, runTry } from '../../../src/runtime-seam.mjs';
import { outcomeFor, outcomeExitCode } from '../../../src/runtime-seam.mjs';
import { projectAnswer, renderJson, renderText } from '../../../src/runtime-seam.mjs';
import { captureSource } from '../../../src/runtime-seam.mjs';
import { harbor, fakeRuntime, portsFor, ordinaryCapabilities, storyTest, TOKEN, PLACE, sha } from '../runtime-fake.mjs';

export const TEST = 'tests/place-order.json';
export const BUILD = 'eae2202a68d00ab762fcbbf1eba0d8607a132a15';
export const cases = name => JSON.parse(readFileSync(new URL(`./${name}-cases.json`, import.meta.url)));
const copy = value => structuredClone(value);
const files = capture => capture.sources.map(source => ({ path: source.path, sha256: sha(source.bytes) }));
const checks = f => f.posts.filter(post => post.command === 'check');
const paid = f => f.posts.filter(post => ['check', 'try'].includes(post.command));
const completeZero = () => ({ provider_calls: 0, accounting_complete: true,
  usage: { calls: 0, known_calls: 0, unknown_calls: 0, provider_calls: 0, accounting_complete: true } });

export function mutate(report, variant) {
  const row = report.operations[0];
  if (variant === 'unsupported' || variant === 'incomplete-blocker') Object.assign(row, { feature: 'retained-mutation', verdict: 'unsupported-capability', reason_code: 'retained-mutation-unsupported' });
  if (variant === 'mode-blocker') Object.assign(row, { verdict: 'unsupported-capability', reason_code: 'runtime-mode-unsupported' });
  if (variant === 'invalid-source') Object.assign(row, { verdict: 'invalid-source', reason_code: 'source-admission-refused' });
  if (variant === 'unknown') Object.assign(row, { feature: 'uninspectable', verdict: 'unknown', reason_code: 'requirement-uninspectable' });
  if (variant === 'missing-binding') report.edges.push({ ...copy(row), binding_kind: 'missing', verdict: 'missing-binding', reason_code: 'binding-missing',
    selection: { ...copy(row.selection), edge: { edge_id: 'save-order', kind: 'resource', call_operation: 'order.save', target_node_id: '', target_path: '', target_operation: '', resource_operation: 'order.save' } } });
  if (variant === 'unknown-build') {
    report.engine_build = report.capability_version = 'unknown';
    for (const r of [...report.operations, ...report.edges]) Object.assign(r, { verdict: 'unknown', reason_code: 'engine-build-unknown' });
  }
  if (['incomplete', 'no-source'].includes(variant)) {
    report.complete = false;
    for (const r of [...report.operations, ...report.edges]) Object.assign(r, { verdict: 'unknown', reason_code: 'analysis-unavailable' });
  }
  if (variant === 'no-source') report.source = null;
  if (['incomplete','incomplete-blocker','no-source'].includes(variant)) report.diagnostics.push({ code: variant === 'no-source' ? 'analysis-unavailable' : 'analysis-incomplete', path: null, section: 'capabilities' });
  if (variant === 'incomplete-blocker') report.complete = false;
  report.verdict = variant === 'missing-binding' ? 'missing-binding' : row.verdict;
  if (variant === 'source-mismatch') report.source.files[0].sha256 = 'd'.repeat(64);
  if (variant === 'scenario-mismatch') report.source.scenario_sha256 = 'd'.repeat(64);
  if (variant === 'build-mismatch') { report.engine_build = 'b'.repeat(40); report.capability_version = `program-capabilities.v1@${report.engine_build}`; }
  if (variant === 'version-mismatch') report.capability_version = `program-capabilities.v1@${'a'.repeat(40)}`;
  if (variant === 'malformed') report.schema_version = 'unknown';
  if (variant === 'duplicate') report.operations.push(copy(row));
  return report;
}

export function pure(t, variant = 'supported', prepare) {
  const h = harbor(t, repo => {
    const path = join(repo, TEST), doc = JSON.parse(readFileSync(path)); doc.steps[0].step_id = 'place';
    writeFileSync(path, JSON.stringify(doc)); prepare?.(repo);
  }), capture = captureSource(h.repo, { tests: [TEST], appMap: null });
  const doc = JSON.parse(capture.sources.find(source => source.path === TEST).bytes), report = mutate(ordinaryCapabilities(capture.sources, TEST), variant);
  const answer = { command: 'lint', state: 'passed', engine_sha: BUILD, usage: { calls: 0 }, result: {
    capabilities: [{ path: TEST, report }], capabilities_complete: true,
    report: { lint: { complete: true, tests: [{ path: TEST, verdict: 'passed', capabilities: report }] } } } };
  return { h, capture, answer, report, options: { test: TEST, steps: doc.steps, sourceFiles: files(capture) } };
}
export const decide = p => outcomeFor(p.answer, p.options);
export const project = p => projectAnswer(p.answer, { ...p.options, secrets: [TOKEN] });
const snapshots = repo => Object.fromEntries(readdirSync(repo, { recursive: true }).filter(path => !path.startsWith('.git/') && path !== '.git' && !path.startsWith('.pdd/')).flatMap(path => {
  try { return [[path, sha(readFileSync(join(repo, path)))]]; } catch { return []; }
}));

export async function client(t, { variant = 'supported', mixed = false, legacy = false, pending = false, lost = false, job = 'passed', edit, lintEdit } = {}) {
  const h = harbor(t, repo => { if (mixed) storyTest(repo, 'second'); edit?.(repo); });
  const before = snapshots(h.repo), captures = [], state = { variant, pending, job, lost };
  const f = await fakeRuntime(t, (entry, f) => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1), post = f.posts.find(post => post.request.requestId === id);
    if (entry.command === 'lint' || post?.command === 'lint') {
      if (entry.command === 'lint' && state.lost) return { destroy: true };
      if (state.pending) return { status: 200, json: f.job(id, 'lint', 'running') };
      const answer = f.lint(id), tests = answer.result.report.lint.tests;
      for (const test of tests) mutate(test.capabilities, mixed && test.path === TEST ? 'supported' : state.variant);
      answer.result.capabilities = tests.map(test => ({ path: test.path, report: copy(test.capabilities) }));
      if (legacy) delete answer.result.capabilities;
      if (state.variant === 'absent') { delete answer.result.capabilities; for (const test of tests) delete test.capabilities; }
      if (state.variant === 'conflict') answer.result.capabilities[0].report = mutate(copy(tests[0].capabilities), 'unknown');
      lintEdit?.(answer);
      return { status: 200, json: answer };
    }
    if (entry.command === 'try') return { status: 200, json: f.tryJob(id) };
    if (entry.url.endsWith('/tests')) return { status: 200, json: { tests: [] } };
    if (state.job === 'lost') return entry.command === 'check' ? { destroy: true } : { status: 404, json: {} };
    if (state.job === 'restart') return { status: 200, json: f.job(id, 'check', 'unknown', { refusals: [{ code: 'service-restarted' }] }, 'unknown') };
    return { status: 200, json: f.check(id, state.job) };
  });
  const env = { HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin };
  let commandTime;
  async function run(mode = 'check', options = {}, words = mixed ? ['place-order', 'second'] : ['place-order'], extra = {}) {
    const p = portsFor(env, { openUrl: async () => true, captureSource(root, options) { const capture = captureSource(root, options); captures.push(capture); return capture; }, ...extra });
    p.clock.now = (commandTime ?? p.clock.now) + (state.advance ?? 0); state.advance = 0;
    const result = mode === 'try' ? await runTry({ cwd: h.repo, words, options: { '--no-open': true, '--no-wait': true, ...options } }, p.ports)
      : await runCheck({ cwd: h.repo, words, options: { '--json': true, ...(mode === 'lint' ? { '--lint': true } : {}), ...options } }, p.ports);
    commandTime = p.clock.now;
    const out = p.ports.stdout.text, err = p.ports.stderr.text;
    return { code: result, out, err, json: out.startsWith('{') ? JSON.parse(out) : null, ...p };
  }
  const saved = result => {
    const folder = join(h.state, 'batches', result.json.batch), path = join(folder, 'batch.json'), batch = JSON.parse(readFileSync(path));
    const lintPath = join(folder, `${batch.lint.request_ids.at(-1)}.json`);
    return { folder, path, batch, lintPath, answer: (() => { try { return JSON.parse(readFileSync(lintPath)); } catch (error) { if (error.code === 'ENOENT') return null; throw error; } })() };
  };
  const unchanged = () => assert.deepEqual(snapshots(h.repo), before, 'authored source, approval and behavioral evidence stay unchanged');
  const archive = () => { for (const post of f.posts) { assert.equal(post.request.source_sha256, sha(post.tar)); assert.deepEqual(post.tar, f.posts[0].tar, 'same immutable archive at every dispatch'); }
    assert.equal(new Set(captures.map(capture => capture.sha256)).size, 1, 'captures retain selected source identity'); };
  return { h, f, run, state, saved, captures, unchanged, archive, env };
}

export const viewCases = {
  async 'supported-top-and-legacy'(t) {
    for (const legacy of [false, true]) {
      const p = pure(t); if (legacy) delete p.answer.result.capabilities;
      const before = copy(p.answer), outcome = decide(p), view = project(p);
      assert.equal(outcome.state, 'passed', 'COMPAT supported matching source admits');
      assert.equal(view.compatibility.association, 'matched'); assert.equal(view.compatibility.reported.source.closure_sha256, 'c'.repeat(64));
      assert.deepEqual(p.answer, before, 'pure boundary does not mutate input');
      const c = await client(t, { legacy });
      const json = await c.run('lint'); assert.equal(json.code, 0, json.err);
      assert.equal(json.json.rows[0].compatibility.state, 'supported'); assert.equal(json.json.rows[0].compatibility.association, 'matched');
      const text = await c.run('lint', { '--json': false }); assert.equal(text.code, 0);
      for (const value of ['place-order', 'place_order', 'ordinary', 'simulated', BUILD, 'scenario_sha256', 'closure_sha256', 'Client advice']) assert.ok(text.out.includes(value), value);
      assert.equal(c.f.posts.length, 2); assert.equal(paid(c.f).length, 0); c.unchanged(); c.archive();
    }
  },
  async 'five-authoritative-states'(t) {
    for (const [variant, verdict, reason, code] of [['supported','supported','supported',0], ['unsupported','unsupported-capability','retained-mutation-unsupported',4],
      ['missing-binding','missing-binding','binding-missing',4], ['invalid-source','invalid-source','source-admission-refused',4], ['unknown','unknown','requirement-uninspectable',5]]) {
      const p = pure(t, variant), result = decide(p), view = project(p);
      assert.equal(result.compatibility.state, verdict); assert.equal(outcomeExitCode([result]), code);
      assert.ok([...view.compatibility.reported.operations, ...view.compatibility.reported.edges].some(row => row.reason_code === reason));
      if (variant === 'missing-binding') { assert.equal(view.compatibility.reported.edges[0].binding_kind, 'missing'); assert.equal(view.compatibility.reported.edges[0].selection.edge.resource_operation, 'order.save'); }
      const c = await client(t, { variant }); const lint = await c.run('lint'); assert.equal(lint.code, code, lint.err); assert.equal(paid(c.f).length, 0);
    }
  },
  async 'edge-and-step-identity'(t) {
    const child = 'prompts/child.prompt.md';
    const p = pure(t, 'supported', repo => {
      const path = join(repo, TEST), doc = JSON.parse(readFileSync(path)); doc.steps.push({ ...copy(doc.steps[0]), step_id: 'again' }); writeFileSync(path, JSON.stringify(doc));
      const parent = readFileSync(join(repo, PLACE), 'utf8'); writeFileSync(join(repo, child), parent);
      writeFileSync(join(repo, PLACE), parent.replace('"calls": []', '"calls": ' + JSON.stringify(['first-call','second-call'].map(operation => ({ operation, target: child, target_operation: 'place_order', max_calls: 1 })))));
    });
    const first = p.report.operations[0], target = copy(first); target.selection.node_id = 'child'; target.selection.prompt_path = child;
    p.report.operations = [first, target];
    for (const id of ['first-call', 'second-call']) p.report.edges.push({ ...copy(first), binding_kind: 'internal', selection: { ...copy(first.selection), edge: {
      edge_id: id, kind: 'internal', call_operation: id, target_node_id: 'child', target_path: child, target_operation: 'place_order', resource_operation: '' } } });
    for (const key of ['operations','edges']) p.report[key].push(...p.report[key].map(row => ({ ...copy(row), resource_mode: 'live', selection: { ...copy(row.selection), step_id: 'again' } })));
    const view = project(p); assert.equal(view.state, 'passed'); assert.equal(view.compatibility.reported.operations.length, 4); assert.equal(view.compatibility.reported.edges.length, 4);
    assert.deepEqual(view.compatibility.reported.edges.map(row => [row.selection.step_id, row.selection.edge.edge_id, row.resource_mode]), [
      ['place', 'first-call', 'simulated'], ['place','second-call','simulated'], ['again','first-call','live'], ['again','second-call','live']]);
    const rendered = renderJson({ repo: p.h.repo, rows: [{ ...view, story: 'place-order', test: TEST }], exitCode: 0 });
    assert.equal(rendered.rows[0].compatibility.reported.edges.length, 4);
  },
  async 'source-build-association'(t) {
    for (const variant of ['source-mismatch','scenario-mismatch','build-mismatch','version-mismatch']) {
      const p = pure(t, variant), o = decide(p); assert.equal(o.state, 'not_run'); assert.equal(o.compatibility.state, 'unknown'); assert.equal(o.compatibility.association, 'mismatch');
      assert.equal(o.compatibility.reported.verdict, 'supported'); assert.equal(o.compatibility.issue, 'capability-association-mismatch');
    }
    for (const variant of ['unknown-build','no-source','no-source-files']) {
      const p = pure(t, variant); if (variant === 'no-source-files') delete p.options.sourceFiles;
      const o = decide(p); assert.equal(o.state, 'not_run'); assert.equal(o.compatibility.association, 'unknown');
    }
    const p = pure(t); const bytes = p.capture.sources.find(source => source.path === TEST).bytes;
    p.options.sourceFiles.find(file => file.path === TEST).sha256 = sha(Buffer.concat([bytes, Buffer.from('\n')]));
    assert.equal(decide(p).compatibility.association, 'mismatch', 'one actual scenario-byte change cannot reuse report');
  },
  async 'unavailable-selected-coverage'(t) {
    for (const variant of ['absent','malformed','conflict','duplicate','incomplete','incomplete-blocker']) {
      const c = await client(t, { variant }), result = await c.run('lint');
      assert.equal(result.code, variant === 'incomplete-blocker' ? 4 : 5, result.err);
      assert.equal(result.json.rows[0].state, variant === 'incomplete-blocker' ? 'refused' : 'not run');
      assert.equal(paid(c.f).length, 0); if (variant.startsWith('incomplete')) assert.equal(result.json.rows[0].compatibility.reported.complete, false);
    }
  },
  async 'selected-versus-inventory'(t) {
    for (const ownRefusal of [false, true]) {
      const c = await client(t, { lintEdit(answer) {
        answer.result.capabilities_complete = answer.result.report.lint.complete = false;
        answer.result.report.lint.tests.push({ path: 'tests/elsewhere.json', verdict: 'not-checked' });
        answer.result.problems = [{ code: 'unrelated', path: 'prompts/elsewhere.prompt.md', message: 'Inventory gap', severity: 'error' }];
        answer.result.report.program.refused_prompts.push({ code: 'unrelated', path: 'prompts/elsewhere.prompt.md', message: 'Inventory gap' });
        if (ownRefusal) answer.result.refusals = [{ code: 'own-refusal', file: TEST, message: 'Own admission refused' }];
      } });
      const r = await c.run('lint'); assert.equal(r.code, ownRefusal ? 4 : 0); assert.equal(r.json.capabilities_complete, false);
      assert.ok(r.json.problems.some(problem => problem.code === 'unrelated')); assert.equal(r.json.rows[0].compatibility.state, 'supported');
    }
    const p = pure(t); p.answer.result.report.program = { refused_prompts: [{ path: PLACE, code: 'reached-refused' }] };
    assert.equal(decide(p).state, 'refused', 'reached refusal precedes supported capabilities');
    mutate(p.report, 'build-mismatch'); assert.equal(decide(p).state, 'refused', 'reached refusal precedes association uncertainty too');
  },
  async 'no-native-or-fixture-inference'(t) {
    const p = pure(t, 'missing-binding'); Object.assign(p.report.edges[0], { binding_kind: 'fixture', verdict: 'supported', reason_code: 'supported' }); p.report.verdict = 'supported';
    p.answer.result.accepted = true; p.answer.usage.calls = 7;
    const view = project(p); assert.equal(view.state, 'passed'); assert.equal(view.compatibility.state, 'supported');
    assert.match(view.client_advice.next_step, /proof remains unproved/);
    const wire = JSON.stringify(view.compatibility); for (const key of ['fixture_fact','logical_phase','modeled_effect','profile','attestation']) assert.ok(!wire.includes(`"${key}"`));
    assert.equal(view.calls, 7, 'reported actual accounting stays separate from capability zeros');
  },
  async 'safe-text-json-and-accounting'(t) {
    const c = await client(t, { lintEdit(answer) { for (const delivery of [answer.result.capabilities[0].report, answer.result.report.lint.tests[0].capabilities]) {
      delivery.diagnostics.push({ code: `safe ${TOKEN} ghp_aSyntheticToken1234\u001b[31m`, path: '/srv/private/source', section: 'capabilities' });
      delivery.operations[0].evaluator_mode = `default ${TOKEN}\u0001`;
    } } });
    const json = await c.run('lint'), text = await c.run('lint', { '--json': false });
    assert.equal(json.code, 0, json.err); assert.equal(text.code, 0, text.err);
    for (const out of [json.out,text.out]) { assert.doesNotMatch(out, /srv\/private|ghp_aSyntheticToken1234|\\u001b|\\u0001/); assert.ok(!out.includes(TOKEN)); assert.ok(out.includes(PLACE)); }
    assert.ok(text.out.includes(JSON.stringify(json.json.rows[0].compatibility, null, 2)), 'text and JSON carry the same cleaned selected facts');
    const p = pure(t); p.answer.command = 'check'; p.answer.usage = { calls: 'unknown', accounting_complete: false, known_calls: 2, unknown_calls: 1 };
    const v = project(p); assert.equal(v.calls, 'unknown'); assert.equal(v.known_calls, 2); assert.equal(v.criteria, null);
  },
};

export const paidCases = {
  async 'ready-public-dispatch'(t) {
    for (const mode of ['check','try']) {
      const c = await client(t), r = await c.run(mode); assert.equal(r.code, 0, r.err);
      assert.equal(paid(c.f).length, 1); assert.equal(c.f.posts[0].command, 'lint'); assert.equal(paid(c.f)[0].command, mode);
      if (mode === 'check') assert.equal(r.json.rows[0].criteria.passed, 1, 'only returned behavioral evidence supplies pass');
      c.archive(); c.unchanged();
    }
  },
  async 'concrete-blockers-no-post'(t) {
    for (const variant of ['invalid-source','unsupported','missing-binding']) for (const mode of ['lint','check','try']) {
      const c = await client(t, { variant }), r = await c.run(mode); assert.equal(r.code, 4, `${variant}/${mode}: ${r.err}`); assert.equal(paid(c.f).length, 0);
      if (r.json?.rows[0]) assert.equal(r.json.rows[0].state, 'refused');
      if (r.json?.batch) assert.deepEqual(c.saved(r).batch.rows[0].request_ids, [], 'no paid request identity allocated'); c.unchanged();
    }
  },
  async 'ended-unknown-no-post'(t) {
    for (const variant of ['absent','malformed','conflict','duplicate','incomplete','unknown','unknown-build','no-source','source-mismatch','scenario-mismatch','build-mismatch','version-mismatch'])
      for (const mode of ['check','try']) {
        const c = await client(t, { variant }), r = await c.run(mode); assert.equal(r.code, 5, `${variant}/${mode}: ${r.err}`); assert.equal(paid(c.f).length, 0);
        if (r.json?.rows[0]) { assert.equal(r.json.rows[0].state, 'not run'); assert.equal(r.json.rows[0].calls, 0); }
      }
    const c = await client(t); const r = await c.run('check', {}, ['place-order'], { captureSource(root, options) {
      const capture = captureSource(root, options); return { ...capture, sources: undefined };
    } }); assert.equal(r.code, 5); assert.equal(paid(c.f).length, 0);
  },
  async 'open-lint-same-id'(t) {
    for (const lost of [false, true]) {
      const c = await client(t, { pending: true, lost }), r = await c.run('check', { '--timeout': 0.01 });
      assert.equal(r.code, 3, r.err); assert.equal(r.json.rows[0].calls, 0); assert.equal(paid(c.f).length, 0);
      const saved = c.saved(r), id = saved.batch.lint.request_ids[0];
      const next = await c.run('check', { '--read': r.json.batch, '--timeout': 0.01 }, []);
      assert.equal(next.code, 3); assert.equal(c.f.posts.length, 1); assert.ok(c.f.gets.every(get => get.url === `/v1/runs/${id}`));
      c.unchanged();
    }
  },
  async 'mixed-scope'(t) {
    for (const variant of ['unsupported','incomplete']) {
      const c = await client(t, { mixed: true, variant, lintEdit(answer) {
        answer.result.capabilities_complete = answer.result.report.lint.complete = false;
        answer.result.refusals = [{ code: 'unrelated-inventory', file: 'tests/outside.json', message: 'Unselected gap' }];
        answer.result.report.program.refused_prompts.push({ code: 'unrelated-inventory', path: 'prompts/outside.prompt.md', message: 'Unselected gap' });
      } });
      const r = await c.run(); assert.equal(r.code, variant === 'unsupported' ? 4 : 5, r.err);
      assert.deepEqual(checks(c.f).map(post => post.request.scenario), [TEST]); assert.match(r.out + r.err, /unrelated-inventory/);
      // Check-plan capture is local; the POST assertion above covers the one upload.
      c.archive(); c.unchanged();
    }
  },
  async 'all-dispatch-doors'(t) {
    for (const variant of ['unsupported','unknown','supported']) for (const door of ['continuation','retry','restart']) {
      const c = await client(t, { pending: door === 'continuation', job: door === 'restart' ? 'running' : 'passed' });
      let first;
      if (door === 'retry') {
        // Create an authentic admitted but not-started capacity refusal, then change only saved authoritative lint input.
        first = await c.run('check', { '--timeout': 0.01 }, ['place-order'], { fetch: async (url, init) => {
          if (String(url).endsWith('/v1/check') && init?.method === 'POST') return new Response(JSON.stringify({ dispatch: 'not_started', ...completeZero(), error: { code: 'check-queue-full', details: { retryable: true, retry_after: 300 } } }), { status: 503, headers: { 'retry-after': '300', 'content-type': 'application/json' } });
          return fetch(url, init);
        } });
      } else first = await c.run('check', { '--timeout': 0.01 });
      const saved = c.saved(first);
      if (door !== 'continuation') {
        for (const item of saved.answer.result.capabilities) mutate(item.report, variant);
        for (const item of saved.answer.result.report.lint.tests) mutate(item.capabilities, variant);
        writeFileSync(saved.lintPath, JSON.stringify(saved.answer));
      }
      c.state.pending = false; c.state.variant = variant; c.state.job = door === 'restart' ? 'restart' : 'passed';
      const before = paid(c.f).length; if (door === 'retry') c.state.advance = 400_000;
      const r = await c.run('check', { [door === 'retry' ? '--retry' : '--read']: first.json.batch, '--timeout': 0.01 }, []);
      assert.equal(paid(c.f).length, before + (variant === 'supported' ? 1 : 0), `${door}/${variant} uses selected compatibility`);
      assert.equal(c.f.posts.filter(post => post.command === 'lint').length, 1);
      if (door === 'continuation') assert.equal(r.code, variant === 'supported' ? 0 : variant === 'unsupported' ? 4 : 5, r.err);
    }
    for (const guard of ['owner','source','intent','claim']) for (const door of ['continuation','retry','restart']) {
      const c = await client(t, { pending: door === 'continuation', job: door === 'restart' ? 'running' : 'passed' });
      const busyFetch = async (url, init) => {
        if (String(url).endsWith('/v1/check') && init?.method === 'POST') return new Response(JSON.stringify({ dispatch: 'not_started', ...completeZero(), error: { code: 'check-queue-full', details: { retryable: true, retry_after: 300 } } }), { status: 503, headers: { 'retry-after': '300', 'content-type': 'application/json' } });
        return fetch(url, init);
      };
      const first = await c.run('check', { '--timeout': 0.01 }, ['place-order'], door === 'retry' ? { fetch: busyFetch } : {}), saved = c.saved(first);
      c.state.pending = false; c.state.job = door === 'restart' ? 'restart' : 'passed';
      let extra = {};
      if (guard === 'owner') extra.gh = args => ({ status: 0, stdout: args[0] === 'auth' ? TOKEN : 'someone-else 7' });
      if (guard === 'source') writeFileSync(join(c.h.repo, PLACE), readFileSync(join(c.h.repo, PLACE), 'utf8') + '\nChanged.\n');
      if (guard === 'intent') { saved.batch.intent = 'try'; writeFileSync(saved.path, JSON.stringify(saved.batch)); }
      if (guard === 'claim') {
        const key = createHash('sha256').update(TEST).digest('hex');
        if (door === 'restart') writeFileSync(join(saved.folder, `${key}.restart.json`), '{}');
        else writeFileSync(join(saved.folder, `${key}.${door === 'retry' ? 1 : 0}.dispatch.json`), JSON.stringify({ id: '00000000-0000-4000-8000-000000000001' }));
      }
      const before = paid(c.f).length; if (door === 'retry') c.state.advance = 400_000;
      await c.run('check', { [door === 'retry' ? '--retry' : '--read']: first.json.batch, '--timeout': 0.01 }, [], extra);
      assert.equal(paid(c.f).length, before, `${guard}/${door} old guard remains authoritative`);
    }
    // #2840 owns standalone saved-lint read projection. The base's GET-only behavior is preserved here.
    const c = await client(t, { pending: true }); await c.run('lint', { '--timeout': 0.01 });
    const batch = readdirSync(join(c.h.state, 'batches'), { withFileTypes: true }).find(item => item.isDirectory()).name;
    c.state.pending = false;
    await c.run('check', { '--read': batch, '--timeout': 0.01 }, []);
    assert.equal(paid(c.f).length, 0, 'lint-only saved reads are GET-only');
  },
  async 'privacy-accounting-records'(t) {
    const c = await client(t, { job: 'lost', edit(repo) {
      mkdirSync(join(repo, '.pdd'), { recursive: true }); writeFileSync(join(repo, '.pdd/approvals.json'), '{"untouched":true}');
      writeFileSync(join(repo, 'evidence.json'), '{"behavior":"unproved"}');
    } });
    const approval = readFileSync(join(c.h.repo,'.pdd/approvals.json'));
    const first = await c.run('check', { '--timeout': 0.01 }); assert.equal(first.code, 3); assert.equal(first.json.rows[0].calls, 'unknown');
    const before = paid(c.f).length; const id = first.json.rows[0].request_id;
    const next = await c.run('check', { '--read': first.json.batch, '--timeout': 0.01 }, []);
    assert.equal(next.json.rows[0].request_id, id); assert.equal(next.json.rows[0].calls, 'unknown'); assert.equal(paid(c.f).length, before);
    assert.deepEqual(readFileSync(join(c.h.repo,'.pdd/approvals.json')), approval); assert.ok(c.f.gets.every(get => get.url === `/v1/runs/${id}`)); c.archive(); c.unchanged();
  },
  async 'configured-versus-installed'(t) {
    for (const variant of ['supported','build-mismatch']) {
      const c = await client(t, { variant }), r = await c.run(); assert.equal(r.code, variant === 'supported' ? 0 : 5, r.err);
      assert.equal(paid(c.f).length, variant === 'supported' ? 1 : 0);
      assert.match(r.json.rows[0].client_advice.next_step, variant === 'supported' ? /unproved/ : /deployment identity/);
    }
  },
};
