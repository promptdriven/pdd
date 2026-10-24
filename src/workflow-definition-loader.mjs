// Generated from prompts/cli/workflow-definition-loader.prompt.md (sha256: 899a8d035ea9678c734108ede6b431dc71eaefd83cd49fda35ba1bacaa83cd12).
import { constants, lstatSync, realpathSync, openSync, fstatSync, readFileSync, closeSync, readdirSync } from 'node:fs';
import { resolve, join, relative, isAbsolute, sep } from 'node:path';
import { createHash } from 'node:crypto';

const NAME = /^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/;
const ROLES = new Set(['prompt', 'story', 'cases', 'implementation', 'tests', 'evidence', 'notes']);
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const fail = message => { throw Error(`Workflow definition: ${message}`); };
function isWorkflowName(name) { return typeof name === 'string' && name.length <= 64 && NAME.test(name); }
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
function closed(value, required, optional = []) {
  if (!object(value) || required.some(key => !Object.hasOwn(value, key))
    || Object.keys(value).some(key => !required.includes(key) && !optional.includes(key))) fail('missing or unknown fields');
}
function directory(path) {
  const stat = lstatSync(path);
  if (!stat.isDirectory() || stat.isSymbolicLink() || realpathSync(path) !== path) fail(`noncanonical directory ${path}`);
}
function exists(path) {
  try { lstatSync(path); return true; } catch (error) { if (error.code === 'ENOENT') return false; throw error; }
}
function parents(root, parts, missing = false) {
  directory(root);
  let path = root;
  for (const part of parts) {
    path = join(path, part);
    if (missing && !exists(path)) return null;
    directory(path);
  }
  return path;
}
function rootPath(value) {
  if (typeof value !== 'string' || !value.trim()) fail('project and package roots are required');
  const path = realpathSync(resolve(value)); directory(path); return path;
}
function instructionPath(value) {
  if (typeof value !== 'string' || !value.endsWith('.md') || isAbsolute(value) || value.includes('\\')
    || value.includes('\0') || value.split('/').some(p => !p || p === '.' || p === '..' || p === '.git'))
    fail('instructions must be contained Markdown paths');
  return value;
}
function unchanged(a, b) {
  return a.dev === b.dev && a.ino === b.ino && a.size === b.size && a.mtimeMs === b.mtimeMs && a.ctimeMs === b.ctimeMs;
}
function readFile(root, name) {
  const path = resolve(root, name), part = relative(root, path);
  if (!part || part === '..' || part.startsWith(`..${sep}`) || isAbsolute(part)) fail('file escaped selected recipe');
  parents(root, name.split('/').slice(0, -1));
  const before = lstatSync(path);
  if (!before.isFile() || before.isSymbolicLink() || before.nlink !== 1 || before.size > 256 * 1024)
    fail(`not an ordinary bounded recipe file: ${name}`);
  const fd = openSync(path, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
  try {
    const opened = fstatSync(fd);
    if (!unchanged(before, opened)) fail(`file changed before read: ${name}`);
    const bytes = readFileSync(fd);
    parents(root, name.split('/').slice(0, -1));
    if (!unchanged(opened, fstatSync(fd)) || !unchanged(opened, lstatSync(path))) fail(`file changed during read: ${name}`);
    const content = new TextDecoder('utf-8', { fatal: true }).decode(bytes);
    return { path: name, sha256: hash(bytes), content };
  } finally { closeSync(fd); }
}
function validate(data, name) {
  closed(data, ['version', 'name', 'overview', 'stages']);
  if (data.version !== 1 || data.name !== name) fail('name or version mismatch');
  instructionPath(data.overview);
  if (!Array.isArray(data.stages) || data.stages.length < 1 || data.stages.length > 64) fail('expected 1–64 stages');
  const seen = new Map(), merged = new Set();
  let proposal, accepted = false, verified = false;
  const stages = data.stages.map(raw => {
    closed(raw, ['id', 'kind', 'file'], ['optional', 'protocol', 'requiredRoles', 'approval', 'prStage', 'requiresMerge', 'publication']);
    const { id, kind } = raw;
    if (!isWorkflowName(id) || seen.has(id)) fail('invalid or duplicate stage ID');
    if (!['agent', 'human', 'pr', 'merge'].includes(kind)) fail(`${id}: invalid kind`);
    instructionPath(raw.file);
    if (raw.optional !== undefined && typeof raw.optional !== 'boolean') fail(`${id}: optional must be boolean`);
    if (raw.optional && !['agent', 'pr'].includes(kind)) fail(`${id}: kind cannot be optional`);
    const allowed = ['id', 'kind', 'file', 'optional', ...(kind === 'agent' ? ['protocol', 'requiredRoles', 'approval', 'requiresMerge']
      : kind === 'pr' ? ['publication', 'requiresMerge'] : kind === 'merge' ? ['prStage'] : [])];
    if (Object.keys(raw).some(key => !allowed.includes(key))) fail(`${id}: field does not apply to kind`);
    if (raw.requiresMerge !== undefined && (seen.get(raw.requiresMerge)?.kind !== 'merge'
      || kind === 'agent' && raw.protocol !== 'work')) fail(`${id}: requiresMerge must reference a prior merge for work or PR`);
    const stage = { ...raw, optional: raw.optional ?? false };
    if (kind === 'agent') {
      if (!['report', 'proposal', 'work', 'verify'].includes(raw.protocol)) fail(`${id}: invalid agent protocol`);
      const roles = raw.requiredRoles ?? [];
      if (!Array.isArray(roles) || roles.some(role => !ROLES.has(role)) || new Set(roles).size !== roles.length) fail(`${id}: invalid artifact roles`);
      stage.requiredRoles = [...roles];
      if (raw.protocol === 'proposal') {
        if (proposal || raw.optional || !roles.length || !['human', 'next-advance'].includes(raw.approval)) fail(`${id}: invalid single proposal/approval`);
        proposal = stage; accepted = raw.approval === 'next-advance';
      } else if (raw.approval !== undefined) fail(`${id}: approval belongs to proposal`);
      if (['work', 'verify'].includes(raw.protocol) && !accepted) fail(`${id}: work requires prior proposal acceptance`);
      if (raw.protocol === 'work') verified = false;
      if (raw.protocol === 'verify') {
        if (raw.optional) fail(`${id}: verify cannot be optional`);
        verified = true;
      }
    } else if (kind === 'human') {
      if (!proposal || accepted || proposal.approval !== 'human') fail(`${id}: human approval requires an unaccepted proposal`);
      accepted = true;
    } else if (kind === 'pr') {
      if (!accepted || !['proposal', 'verified'].includes(raw.publication)
        || raw.publication === 'verified' && !verified) fail(`${id}: PR requires accepted proposal or prior mandatory verification`);
    } else {
      if (seen.get(raw.prStage)?.kind !== 'pr' || merged.has(raw.prStage)) fail(`${id}: merge must reference one unmatched prior PR`);
      merged.add(raw.prStage);
    }
    seen.set(id, stage); return stage;
  });
  return stages;
}
function freeze(value) {
  if (value && typeof value === 'object') { Object.values(value).forEach(freeze); Object.freeze(value); }
  return value;
}
export function loadWorkflowDefinition({ name, cwd, packageRoot } = {}) {
  if (!isWorkflowName(name)) fail('invalid workflow name');
  const project = rootPath(cwd), bundled = rootPath(packageRoot);
  const localParent = parents(project, ['.pdd', 'workflows'], true);
  const local = localParent && join(localParent, name);
  const root = local && exists(local) ? (directory(local), local) : parents(bundled, ['.pdd', 'workflows', name]);
  const definition = readFile(root, 'workflow.json');
  let data;
  try { data = JSON.parse(definition.content); } catch { fail(`${name}: malformed workflow.json`); }
  const stages = validate(data, name);
  const names = [...new Set([data.overview, ...stages.map(stage => stage.file)])].sort();
  const files = [definition, ...names.map(path => readFile(root, path))].sort((a, b) => a.path.localeCompare(b.path, 'en'));
  if (files.reduce((size, file) => size + Buffer.byteLength(file.content), 0) > 2 * 1024 * 1024) fail('snapshot exceeds 2MiB');
  const digest = hash(JSON.stringify({ name, version: 1, stages, files: files.map(({ path, sha256 }) => ({ path, sha256 })) }));
  return freeze({ name, version: 1, root, stages, files, digest });
}
export function listWorkflowDefinitions({ cwd, packageRoot } = {}) {
  const project = rootPath(cwd), bundled = rootPath(packageRoot), names = new Set();
  for (const root of [bundled, project]) {
    const parent = parents(root, ['.pdd', 'workflows'], true);
    if (!parent) continue;
    for (const entry of readdirSync(parent, { withFileTypes: true })) {
      if (isWorkflowName(entry.name) && (entry.isDirectory() || entry.isSymbolicLink())) names.add(entry.name);
    }
  }
  return [...names].sort().map(name => {
    const definition = loadWorkflowDefinition({ name, cwd: project, packageRoot: bundled });
    return { name, source: definition.root === join(project, '.pdd', 'workflows', name) ? 'project' : 'bundled' };
  });
}
