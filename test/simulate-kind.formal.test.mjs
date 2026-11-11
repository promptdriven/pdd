import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runTry } from '../src/runtime-client.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor } from './runtime-fake.mjs';

const object = properties => ({ type: 'object', properties, required: Object.keys(properties), additionalProperties: false });
const text = { type: 'string' };

// Bounded domain from simulate-program-kind's Rules to check and runtime-client's
// "Choose how to open the program": one named entry, four independent booleans.
// Keep an unrelated screen map present even when the named entry is not mapped.
test('2760 bounded named default: all 16 convention, HTTP and screen combinations', async t => {
  const covered = { shell: 0, serve: 0, screen: 0, form: 0 };
  let cases = 0;
for (const inputCli of [false, true]) for (const resultCli of [false, true]) {
  for (const http of [false, true]) for (const mapped of [false, true]) {
    const bits = `inputCli=${inputCli},resultCli=${resultCli},http=${http},mapped=${mapped}`;
    const expected = inputCli && resultCli ? 'shell' : http ? 'serve' : mapped ? 'screen' : 'form';
    await t.test(`${bits} => ${expected}`, async t => {
      cases += 1;
      covered[expected] += 1;
      const setup = harbor(t, root => {
        for (const directory of ['prompts', 'tests', 'user_stories']) {
          rmSync(join(root, directory), { recursive: true }); mkdirSync(join(root, directory));
        }
        // Superset schemas admit every convention combination without changing
        // the operation name or scenario answer to hint at the interaction kind.
        const input = object({ argv: { type: 'array', items: text } });
        if (http) input.title = 'HTTP GET /health';
        const result = object({ stdout: text, stderr: text, exit_code: { type: 'integer' }, html: text });
        const iface = { status: 'draft', prose_sha256: '', entries: [{ operation: 'main', input_schema: input, result_schema: result, errors: [] }], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 1 }, conventions: [] };
        if (inputCli) iface.conventions.push({ path: '/entries/0/input_schema', convention: 'cli' });
        if (resultCli) iface.conventions.push({ path: '/entries/0/result_schema', convention: 'cli' });
        const content = () => `# boundedtool\n\nReturn ready. Every line written to stdout or stderr ends with one newline.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\x60\x60\x60json\n${JSON.stringify(iface)}\n\x60\x60\x60\n</details>\n`;
        iface.prose_sha256 = proseSha256(content());
        for (const name of ['subject', 'other']) writeFileSync(join(root, `prompts/${name}.prompt.md`), content());
        writeFileSync(join(root, 'user_stories/subject.md'), '# Subject\n\nI can use the program.\n\n## Acceptance criteria\n\n1. Ready.\n');
        writeFileSync(join(root, 'tests/subject.json'), JSON.stringify({ schema_version: 'prompt-runtime.program-scenario.v1', story_path: 'user_stories/subject.md', criteria: [{ id: 'AC1', text: 'Ready.' }], initial_world: {}, simulation: {}, context: [], steps: [{ step_id: 'ready', entry_path: 'prompts/subject.prompt.md', operation: 'main', input: { argv: [] }, checks: [{ criterion_id: 'AC1', target: 'result', path: '/stdout', op: 'equals', value: 'ready\n' }] }] }));
        writeFileSync(join(root, 'app-map.json'), JSON.stringify({ schema_version: 'prompt-runtime.app-map.v1', name: 'Synthetic screens', initial_screen: 'view', initial_route: null, initial_state: {}, state_schema: object({}), synthetic: true, router: null, routes: [], stylesheets: [], handlers: [], screens: [{ id: 'view', source: 'operation', prompt_path: `prompts/${mapped ? 'subject' : 'other'}.prompt.md`, operation: 'main', input: { argv: [] }, format: 'html', result_pointer: '/html' }] }));
      });
      const fake = await fakeRuntime(t, (entry, f) => {
        if (entry.url.endsWith('/model')) return { status: 200, json: { entries: http ? [{ entry_path: 'prompts/subject.prompt.md', operation: 'main', input_schema: object({}), http: { method: 'GET', path: '/health' } }] : [], calls: { cap: 400, remaining: 400 }, app_map: true } };
        if (entry.command === 'lint') return { status: 200, json: f.lint(entry.request.requestId, ['subject', 'other'].map(name => ({ path: `prompts/${name}.prompt.md`, state: 'draft', admission_state: 'draft', interface: { calls: [] } }))) };
        if (entry.command === 'try') { const job = f.tryJob(entry.request.requestId); f.jobs.set(entry.request.requestId, job); return { status: 200, json: job }; }
        return { status: 200, json: f.jobs.get(entry.url.split('/').at(-1)) };
      });
      const events = [];
      const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin }, {
        shell: async () => { events.push('shell'); return 0; },
        serve: async () => { events.push('serve'); },
        openUrl: async () => { events.push('page'); return true; },
      });
      const code = await runTry({ cwd: setup.repo, words: ['subject'] }, ports);
      assert.equal(code, 0, `${bits}: ${ports.stderr.text}\n${ports.stdout.text}`);
      assert.deepEqual(events, [expected === 'screen' || expected === 'form' ? 'page' : expected], bits);
      const request = fake.posts.find(entry => entry.command === 'try')?.request;
      assert.ok(request, `${bits}: must create a session`);
      if (expected === 'screen' || expected === 'form') assert.equal(request.tab, expected === 'screen' ? 'screen' : 'call', bits);
      const explanation = "This Story's operation takes typed input, so it opens on the Form tab.";
      assert.equal((ports.stdout.text + ports.stderr.text).split('\n').filter(line => line === explanation).length, expected === 'form' ? 1 : 0, bits);
    });
  }
}
  assert.equal(cases, 16);
  assert.deepEqual(covered, { shell: 4, serve: 6, screen: 3, form: 3 });
});
