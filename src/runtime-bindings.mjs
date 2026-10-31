// Generated from prompts/cli/runtime-bindings.prompt.md (sha256: 5b44de22d54982cc69e3bb046c106a1b1b908e37ea32ef66e3db988f2c465d81).
import { lstatSync } from 'node:fs';
import { join } from 'node:path';
import { PreflightError, readPrompt, isSecretPath, sourceFilePort } from './runtime-preflight.mjs';

export function bindingCoverage({ root, found, selected }) {
  const unavailable = { available: false, bound: null, total: null, modules: [] };
  const fail = (path, why) => { throw Object.assign(new PreflightError(4, `pdd-bindings.json: ${path}: ${why}`), { bindingInventory: true }); };
  const regular = path => {
    if (typeof path !== 'string' || !path || path.includes('\\') || path.startsWith('/') || path.split('/').some(p => !p || p === '.' || p === '..')) fail(String(path), 'use an existing repository-relative regular Git-visible path');
    if (isSecretPath(path)) fail(path, 'secret-looking paths are not allowed');
    let full = root;
    for (const part of path.split('/')) {
      full = join(full, part);
      let stat; try { stat = lstatSync(full); } catch { fail(path, 'file does not exist'); }
      if (stat.isSymbolicLink()) fail(path, 'symlinks are not allowed');
    }
    if (!lstatSync(full).isFile() || !found.visible.has(path)) fail(path, 'must be a regular Git-visible file');
    return path;
  };
  try { lstatSync(join(root, 'pdd-bindings.json')); } catch (error) { if (error.code === 'ENOENT') return unavailable; throw error; }
  regular('pdd-bindings.json');
  const files = sourceFilePort(root);
  if (files.stat({path:'pdd-bindings.json'}).size > 65536) fail('inventory', 'exceeds 64 KiB');
  let inventory; try { inventory = JSON.parse(files.read({path:'pdd-bindings.json'}).content); } catch { fail('inventory', 'invalid JSON'); }
  const object = v => v !== null && typeof v === 'object' && !Array.isArray(v);
  const keys = (v, names) => object(v) && Object.keys(v).length === names.length && names.every(k => Object.hasOwn(v, k));
  if (!keys(inventory, ['schema_version', 'modules']) || inventory.schema_version !== 'pdd.bindings.v1' || !Array.isArray(inventory.modules)) fail('inventory', 'expected schema_version pdd.bindings.v1 and modules array only');
  if (inventory.modules.length > 1000) fail('inventory', 'exceeds 1000 module declarations');
  const stories = new Set(found.stories.map(s => s.path)), chosen = new Set(selected.map(t => t.storyPath)), seen = new Set(), modules = [];
  const reached = new Set(), queue = selected.flatMap(t => (Array.isArray(t.doc?.steps) ? t.doc.steps : []).map(s => s?.entry_path));
  while (queue.length) {
    const path = queue.shift(); if (typeof path !== 'string' || reached.has(path)) continue;
    reached.add(path);
    const prompt = readPrompt(root, found.visible, path);
    for (const call of Array.isArray(prompt?.interface?.calls) ? prompt.interface.calls : []) if (typeof call?.target === 'string') queue.push(call.target);
  }
  for (const item of inventory.modules) {
    const path = item?.module ?? 'module';
    if (!object(item)) fail(path, 'expected module declaration');
    const bound = Object.hasOwn(item, 'prompt');
    if (!keys(item, bound ? ['module', 'stories', 'prompt'] : ['module', 'stories', 'reason', 'port_attempt'])) fail(path, 'declare prompt or both reason and port_attempt, with no extra fields');
    regular(item.module); if (seen.has(item.module)) fail(path, 'duplicate module'); seen.add(item.module);
    if (!Array.isArray(item.stories) || !item.stories.length || new Set(item.stories).size !== item.stories.length) fail(path, 'stories must be nonempty and unique');
    for (const story of item.stories) { regular(story); if (!stories.has(story)) fail(path, `unknown Story ${story}`); }
    if (bound) regular(item.prompt);
    else for (const key of ['reason', 'port_attempt']) if (typeof item[key] !== 'string' || !item[key].trim()) fail(path, `${key} must be nonblank`);
    if (!item.stories.some(story => chosen.has(story))) continue;
    if (bound) {
      const prompt = readPrompt(root, found.visible, item.prompt);
      if (prompt.error || !reached.has(item.prompt) || !Array.isArray(prompt?.interface?.entries) || !prompt.interface.entries.length || prompt.interface.entries.some(entry => !entry || typeof entry.operation !== 'string' || !entry.operation.trim() || !object(entry.input_schema) || !object(entry.result_schema))) fail(path, `${item.prompt} must be reached and have an executable Runtime interface`);
    }
    modules.push({ path: item.module, state: bound ? 'bound' : 'unbound', ...(bound ? {} : { reason: item.reason, port_attempt: item.port_attempt }) });
  }
  return { available: true, bound: modules.filter(m => m.state === 'bound').length, total: modules.length, modules };
}
