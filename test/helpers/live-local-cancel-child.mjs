// Native PTY fixture. All physical writes stay in the supplied temporary root.
import assert from 'node:assert/strict';
import { mkdir } from 'node:fs/promises';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
const { createLocalCommandBridge } = await import(process.env.PDD_CONSENT_CLIENT_MODULE ? pathToFileURL(process.env.PDD_CONSENT_CLIENT_MODULE).href : new URL('../../src/runtime-seam.mjs', import.meta.url).href);
import { getEventListeners } from 'node:events';

const moduleUrl = process.env.PDD_CONSENT_HOST_MODULE
  ? pathToFileURL(process.env.PDD_CONSENT_HOST_MODULE).href
  : new URL('../../src/live-local-host.mjs', import.meta.url).href;
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

if (scenario.startsWith('abort-')) {
  let remoteClosed=false; const abortController=new AbortController(); let closePromise; let bridgeHandle;
  process.on('SIGUSR1',()=>{ if(scenario==='abort-remote'){remoteClosed=true;console.log('REMOTE_CANCELLED');}else if(scenario==='abort-service'){abortController.abort();console.log('SIGNAL_ABORTED');}else{console.log('CLOSE_REQUESTED');closePromise=bridgeHandle.close().then(()=>console.log('CLOSE_SETTLED'));} });
  const requests = new Map(['A', 'B'].map(id => [`request-${id}`, wire(id)]));
  let replies = 0;
  const registration = { schema_version: 'prompt-runtime.local-commands.v1', capability: 'execute-command-v1', client_id: 'fixture-client', registration_id: 'fixture-registration', epoch: 1 };
  const response = (id, state, permitted = false, request = null, result = null) => ({ request_id: id, state, dispatch_permitted: permitted, request, outcome: null, result });
  const bridge = await createLocalCommandBridge({ manifest, root, origin: 'http://127.0.0.1', identity: { login: 'fixture-owner' }, kind: 'check', allow_writes: true }, {
    liveLocal: { ...host, randomUUID: () => registration.client_id }, owner: () => 'fixture-owner',
    request: async ({ path, body }) => {
      assert.ok(!JSON.stringify(body ?? null).includes('signal'), 'AbortSignal must stay host-only');
      let json;
      if (path === '/v1/local-commands/registrations') json = registration;
      else if (path.endsWith('/connect')) { const { registration_id, ...connected } = registration; json = connected; }
      else if (path === '/v1/runs/job-1') { if(remoteClosed) console.log('REMOTE_CLOSED_READ'); json = { id: 'job-1', command: 'check', state: remoteClosed ? 'cancelled' : 'running' }; }
      else if (path.includes('/pending?')) json = { request_ids: [...requests.keys()] };
      else if (path.endsWith('/events')) {
        const id = body.request_id;
        if (body.action === 'poll') json = response(id, 'claimed', false, requests.get(id));
        else if (body.action === 'started') { console.log('\nSTARTED', id); json = response(id, 'dispatched', true); }
        else if (body.action === 'reply') { assert.equal(body.result.status, 'unavailable'); assert.equal(body.result.reason, 'policy-refused'); assert.equal(body.result.outcome, null); replies++; done(id.slice(-1), { confirmed: body.result.status === 'completed' }); json = response(id, 'completed', false, null, body.result); }
      } else if (path.endsWith('/revoke')) json = { revoked: true };
      assert.ok(json, `Unexpected fixture request: ${path}`);
      return { status: 200, json };
    },
  });
  bridgeHandle=bridge; try { await bridge.connect('job-1'); await bridge.service(abortController.signal); console.log('SERVICE_SETTLED'); }
  finally { await bridge.close(); }
}
else {
  const a = new AbortController(), b = new AbortController();
  if (scenario === 'host-before') a.abort();
  if (scenario === 'host-race') process.stdin.prependOnceListener('data', () => a.abort());
  process.on('SIGUSR1', () => {
    if (scenario === 'host-queued') b.abort();
    else if (scenario === 'host-both') { a.abort(); b.abort(); }
    else a.abort();
    console.log('ABORT_OBSERVED');
  });
  const pa = host.confirm({...label('A'), signal:a.signal}).then(result => {
    assert.equal(result.confirmed, scenario === 'host-queued'); return done('A', result);
  });
  const pb = other.confirm({...label('B'), signal:b.signal}).then(result => {
    assert.equal(result.confirmed, !['host-queued','host-both'].includes(scenario)); return done('B', result);
  });
  if (scenario === 'host-drain') setImmediate(() => {a.abort(); console.log('ABORT_OBSERVED');});
  const pc = scenario === 'host-queued' ? other.confirm(label('C')).then(result => {
    assert.equal(result.confirmed, true); return done('C', result);
  }) : Promise.resolve();
  await Promise.all([pa,pb,pc]);
  assert.equal(getEventListeners(a.signal, 'abort').length, 0, 'Abort listener must be removed');
  assert.equal(getEventListeners(b.signal, 'abort').length, 0, 'Queued abort listener must be removed');
}
assert.deepEqual(listenerCounts(), initialListeners, 'Settled confirmations must release terminal listeners');
assert.equal(Boolean(process.stdin.isRaw), initiallyRaw, 'Settled confirmations must restore terminal mode');
console.log('COMPLETE');
