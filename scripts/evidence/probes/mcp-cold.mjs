#!/usr/bin/env node
// Cold stdio JSON-RPC probe for `pdd mcp`: initialize -> tools/list -> try_open on a Short JSON Story,
// plus `pdd lint --emit-v1` Short JSON compilation check (#3660).
import { spawnSync } from 'node:child_process';

const [cmd, story = 'greet-user'] = process.argv.slice(2);
if (!cmd) { console.error('Usage: mcp-cold.mjs <pdd-cmd> [story]'); process.exit(2); }

const emit = spawnSync(cmd, ['lint', '--emit-v1', `tests/${story}.json`], { encoding: 'utf8', timeout: 30_000 });
if (emit.status !== 0) {
  console.error(`lint --emit-v1 failed (exit ${emit.status}): ${(emit.stderr || emit.stdout || '').trim()}`);
  process.exit(1);
}
let compiled;
try { compiled = JSON.parse(emit.stdout); } catch (err) {
  console.error(`lint --emit-v1 returned invalid JSON: ${err.message}`);
  process.exit(1);
}
if (compiled.schema_version !== 'prompt-runtime.program-scenario.v1' || !Array.isArray(compiled.steps) || compiled.steps.length < 1) {
  console.error(`lint --emit-v1 returned unexpected schema: ${emit.stdout.slice(0, 200)}`);
  process.exit(1);
}

const reqs = [
  { jsonrpc: '2.0', id: 1, method: 'initialize', params: { protocolVersion: '2025-06-18', capabilities: {}, clientInfo: { name: 'evidence-probe', version: '1.0' } } },
  { jsonrpc: '2.0', id: 2, method: 'tools/list', params: {} },
  { jsonrpc: '2.0', id: 3, method: 'tools/call', params: { name: 'try_open', arguments: { story } } },
];

const res = spawnSync(cmd, ['mcp'], {
  input: reqs.map(r => JSON.stringify(r)).join('\n') + '\n',
  encoding: 'utf8',
  timeout: 30_000,
});
if (res.status !== 0) {
  console.error(`pdd mcp exited ${res.status}: ${(res.stderr || '').trim()}`);
  process.exit(res.status ?? 1);
}

const msgs = (res.stdout || '').split(/\r?\n/).filter(Boolean).map(line => { try { return JSON.parse(line); } catch { return { raw: line }; } });
const byId = Object.fromEntries(msgs.filter(m => m.id != null).map(m => [m.id, m]));
const tools = (byId[2]?.result?.tools || []).map(t => t.name).sort();
if (!byId[1]?.result?.protocolVersion || !byId[1]?.result?.serverInfo?.name) {
  console.error(`MCP initialize response incomplete: ${JSON.stringify(byId[1])}`);
  process.exit(1);
}
if (!tools.includes('try_open') || !tools.includes('try_state')) {
  console.error(`MCP tools/list missing try_open/try_state: ${JSON.stringify(tools)}`);
  process.exit(1);
}
if (!byId[3]?.result) {
  console.error(`MCP try_open returned no JSON-RPC result: ${JSON.stringify(byId[3])}`);
  process.exit(1);
}
console.log(JSON.stringify({
  marker: 'MCP_COLD_OK',
  story,
  serverName: byId[1].result.serverInfo.name,
  toolsCount: tools.length,
  tryOpenResponded: true,
  compiledSchema: compiled.schema_version,
}));
