import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { DatabaseSync } from 'node:sqlite';
import { findBook } from '../examples/fakes/database.mjs';
import { readNote } from '../examples/fakes/files.mjs';
import { fingerprint } from '../examples/fakes/hash.mjs';
import { lookup } from '../examples/fakes/service.mjs';
import { decideReply, doLookup } from '../examples/fakes/decision.mjs';
import { createGreeter } from '../examples/fakes/factory.mjs';

const pointer = (object, path) => path.split('/').slice(1).reduce((value, key) => value[key.replaceAll('~1', '/').replaceAll('~0', '~')], object);

for (const name of ['database', 'files', 'hash', 'service', 'decision', 'factory']) {
  test(`replay unchanged fake-${name} scenario through native public exports`, async () => {
    const scenario = JSON.parse(readFileSync(new URL(`runtime/fake-${name}.json`, import.meta.url)));
    const world = structuredClone(scenario.initial_world);
    const results = new Map();
    const instances = new Map();
    const calls = [];
    const directory = mkdtempSync(join(tmpdir(), 'pdd-native-fakes-'));
    let sql;
    try {
      if (name === 'database') {
        sql = new DatabaseSync(':memory:');
        for (const statement of world.database.schema) sql.exec(statement);
        for (const row of world.database.rows.books) sql.prepare('INSERT INTO books (id, title) VALUES (:id, :title)').run(row);
      }
      if (name === 'files') {
        for (const [path, file] of Object.entries(world.files)) writeFileSync(join(directory, encodeURIComponent(path)), file.content, 'utf8');
      }
      const service = { lookup(args) {
        calls.push(['service.lookup', args]);
        world.requests.push(structuredClone(args));
        return structuredClone(scenario.simulation['service.lookup'].result_template);
      } };
      for (const step of scenario.steps) {
        const input = structuredClone(step.input);
        if (input.handle?.$step_result) {
          const reference = input.handle.$step_result;
          input.handle = pointer(results.get(reference.step_id), reference.path);
        }
        let result;
        switch (step.operation) {
          case 'findBook':
            result = await findBook({ find(args) {
              calls.push(['db.find', args]);
              return { rows: sql.prepare(scenario.simulation['db.find'].statement).all(args).map(row => ({ ...row })) };
            } }, input.id);
            // Read back SQLite itself; do not merely reuse the seed as the observed world.
            world.database.rows.books = sql.prepare('SELECT id, title FROM books ORDER BY id').all().map(row => ({ ...row }));
            break;
          case 'readNote':
            result = await readNote({ read(args) {
              calls.push(['files.read', args]);
              return { content: readFileSync(join(directory, encodeURIComponent(args.path)), 'utf8') };
            } }, input.path);
            break;
          case 'fingerprint':
            result = await fingerprint({ hash_utf8(args) {
              calls.push(['compute.hash_utf8', args]);
              return { value: createHash('sha256').update(args.text, 'utf8').digest('hex') };
            } }, input.text);
            break;
          case 'lookup': result = await lookup(service, input.id); break;
          case 'decideReply': {
            const before = calls.length;
            result = decideReply(input.reply);
            assert.equal(calls.length, before, 'pure decision makes no resource call');
            break;
          }
          case 'doLookup': result = await doLookup(service, input.id); break;
          case 'createGreeter': {
            const instance = createGreeter(input.prefix);
            // The replay executor owns opaque transport IDs; native callers keep the object.
            const handle = `native-instance-${instances.size}`;
            instances.set(handle, instance);
            world.instances.push({ handle, config: { prefix: input.prefix } });
            result = { handle };
            break;
          }
          case 'greet': result = instances.get(input.handle).greet(input.name); break;
          default: assert.fail(`Not replayed: ${step.operation}`);
        }
        results.set(step.step_id, result);
        for (const check of step.checks) {
          assert.equal(check.op, 'equals', 'all committed checks are replayed');
          assert.ok(['result', 'world'].includes(check.target), `Not replayed: ${check.target}`);
          assert.deepEqual(pointer(check.target === 'world' ? world : result, check.path), check.value,
            `${name}/${step.step_id}/${check.criterion_id} ${check.target}${check.path}`);
        }
      }
      if (name !== 'factory') {
        assert.equal(calls.length, 1, 'exactly one injected effect across scenario');
        const effectStep = scenario.steps.at(-1);
        assert.deepEqual(calls[0][1], effectStep.input, 'exact resource argument forwarding');
      }
    } finally {
      sql?.close();
      rmSync(directory, { recursive: true, force: true });
    }
  });
}

test('native factory closures keep independent configuration', () => {
  const first = createGreeter('Hello ');
  const second = createGreeter('Goodbye ');
  assert.notEqual(first, second);
  assert.deepEqual(first.greet('Ada'), { text: 'Hello Ada' });
  assert.deepEqual(second.greet('Ada'), { text: 'Goodbye Ada' });
  assert.deepEqual(first.greet('Lin'), { text: 'Hello Lin' });
});

test('pure decision covers both supplied Boolean facts', () => {
  assert.deepEqual(decideReply({ available: false }), { label: 'Unavailable' });
  assert.deepEqual(decideReply({ available: true }), { label: 'Available' });
});
