// Native PTY fixture. All physical writes stay in the supplied temporary root.
import assert from 'node:assert/strict';
import { mkdir } from 'node:fs/promises';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { executeLocalCommand, createLocalCommandBridge } from '../../src/runtime-seam.mjs';

const moduleUrl = process.env.PDD_CONSENT_HOST_MODULE
  ? pathToFileURL(process.env.PDD_CONSENT_HOST_MODULE).href
  : new URL('../../src/core/live-local-host.mjs', import.meta.url).href;
const { createLiveLocalHost } = await import(moduleUrl);
const [scenario, scratch] = process.argv.slice(2);
const root = join(scratch, 'workspace');
await mkdir(root);
const redaction = { redact: text => text, remember: () => {}, known: () => [] };
const make = () => createLiveLocalHost({ root, redaction, env: { PATH: '/usr/bin:/bin', PDD_STATE_DIR: join(scratch, 'state') } });
const host = make(), other = scenario === 'same' ? host : make();
assert.equal(host.terminal, true, 'Fixture must use actual TTY streams');
const listenerCounts = () => ['error', 'end', 'keypress'].map(event => process.stdin.listenerCount(event)).concat(process.stdout.listenerCount('resize'));
const initialListeners = listenerCounts(), initiallyRaw = Boolean(process.stdin.isRaw);
process.on('SIGUSR1', () => process.stdin.emit('error', new Error('Controlled terminal read failure')));
process.on('SIGUSR2', () => process.stdin.push(null));
const done = (id, result) => { console.log('\nDONE', id, JSON.stringify(result)); return result; };
const label = id => ({ binding_id: `write-${id}`, executable: 'touch', argv: ['touch', `marker-${id}`] });

const command = {
  binding_id: 'scratch-write', resource: 'scratch', operation: 'mark', executable: 'touch',
  access: 'write', argv: [{ argument: 'marker' }],
  parameters: [{ name: 'marker', type: 'string', enum: ['marker-A', 'marker-B'] }],
  stdin: { literal: '' }, cwd: '.', environment: [], timeout_ms: 1000,
  stdout_limit_bytes: 1024, stderr_limit_bytes: 1024,
};
const manifest = {
  schema_version: 'pdd.live-local-manifest.v1',
  selection: { schema_version: 'prompt-runtime.resource-selection.v2', resources: [{ resource: 'scratch', mode: 'real', location: 'local', binding_id: 'scratch-write' }] },
  commands: [command],
};
const wire = id => ({
  schema_version: 'prompt-runtime.local-command-request.v1', request_id: `request-${id}`, run_id: 'job-1',
  action_id: `action-${id}`, attempt_id: `attempt-${id}`, call_id: `call-${id}`, graph_id: 'graph', edge_id: 'edge',
  resource: command.resource, operation: command.operation, binding_id: command.binding_id, access: 'write',
  argv: ['touch', `marker-${id}`], stdin: '', cwd: '.', environment: [], timeout_ms: command.timeout_ms,
  stdout_limit_bytes: command.stdout_limit_bytes, stderr_limit_bytes: command.stderr_limit_bytes,
});

if (scenario === 'bridge') {
  const requests = new Map(['A', 'B'].map(id => [`request-${id}`, wire(id)]));
  let replies = 0;
  const registration = { schema_version: 'prompt-runtime.local-commands.v1', capability: 'execute-command-v1', client_id: 'fixture-client', registration_id: 'fixture-registration', epoch: 1 };
  const response = (id, state, permitted = false, request = null, result = null) => ({ request_id: id, state, dispatch_permitted: permitted, request, outcome: null, result });
  const bridge = await createLocalCommandBridge({ manifest, root, origin: 'http://127.0.0.1', identity: { login: 'fixture-owner' }, kind: 'check', allow_writes: true }, {
    liveLocal: { ...host, randomUUID: () => registration.client_id }, owner: () => 'fixture-owner',
    request: async ({ path, body }) => {
      let json;
      if (path === '/v1/local-commands/registrations') json = registration;
      else if (path.endsWith('/connect')) { const { registration_id, ...connected } = registration; json = connected; }
      else if (path === '/v1/runs/job-1') json = { id: 'job-1', command: 'check', state: replies === 2 ? 'passed' : 'running' };
      else if (path.includes('/pending?')) json = { request_ids: [...requests.keys()] };
      else if (path.endsWith('/events')) {
        const id = body.request_id;
        if (body.action === 'poll') json = response(id, 'claimed', false, requests.get(id));
        else if (body.action === 'started') { console.log('\nSTARTED', id); json = response(id, 'dispatched', true); }
        else if (body.action === 'reply') { replies++; done(id.slice(-1), { confirmed: body.result.status === 'completed' }); json = response(id, 'completed', false, null, body.result); }
      } else if (path.endsWith('/revoke')) json = { revoked: true };
      assert.ok(json, `Unexpected fixture request: ${path}`);
      return { status: 200, json };
    },
  });
  try { await bridge.connect('job-1'); await bridge.service(); }
  finally { await bridge.close(); }
} else if (scenario === 'execute') {
  await Promise.all(['A', 'B'].map(async (id, index) => {
    const current = index ? other : host;
    const result = await executeLocalCommand({ mode: 'live-local', manifest_json: JSON.stringify(manifest), request_json: JSON.stringify(wire(id)), allow_writes: true, terminal: current.terminal }, {
      consent: current, redaction: current,
      runner: { execute: async () => {
        console.log('\nSTARTED', `request-${id}`);
        return current.execute({ request: wire(id), resolvedExecutable: await current.resolveExecutable({ executable: 'touch' }), root, environment: {} });
      } }, delivery: { reply: async () => ({ accepted: true }) },
    });
    assert.equal(result.outcome.exit_code, 0);
    done(id, { confirmed: true });
  }));
} else {
  await Promise.all([
    host.confirm(label('A')).then(result => done('A', result)),
    other.confirm(label('B')).then(result => done('B', result)),
  ]);
}
assert.deepEqual(listenerCounts(), initialListeners, 'Settled confirmations must release terminal listeners');
assert.equal(Boolean(process.stdin.isRaw), initiallyRaw, 'Settled confirmations must restore terminal mode');
console.log('COMPLETE');
