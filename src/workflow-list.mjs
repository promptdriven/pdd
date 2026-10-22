import { lstatSync, readdirSync } from 'node:fs';
import { join, relative } from 'node:path';

const NAME = /^[a-z0-9][a-z0-9._-]{0,63}$/;

export function listLocalWorkflows({ cwd = process.cwd(), readDir = readdirSync, stat = lstatSync } = {}) {
  const metadata = join(cwd, '.pdd');
  const root = join(metadata, 'workflows');
  let entries;
  try {
    const metadataInfo = stat(metadata);
    if (!metadataInfo.isDirectory() || metadataInfo.isSymbolicLink()) return { workflows: [], default: null };
    const rootInfo = stat(root);
    if (!rootInfo.isDirectory() || rootInfo.isSymbolicLink()) return { workflows: [], default: null };
    entries = readDir(root, { withFileTypes: true });
  } catch (error) {
    if (error?.code === 'ENOENT' || error?.code === 'ENOTDIR') return { workflows: [], default: null };
    throw error;
  }

  const workflows = [];
  for (const entry of entries) {
    if (!entry.isDirectory() || !NAME.test(entry.name)) continue;
    const directory = join(root, entry.name);
    const file = join(directory, 'WORKFLOW.md');
    try {
      const fileInfo = stat(file);
      if (!fileInfo.isFile() || fileInfo.isSymbolicLink()) continue;
      workflows.push({ name: entry.name, file: relative(cwd, file) });
    } catch (error) {
      if (error?.code === 'ENOENT' || error?.code === 'ENOTDIR') continue;
      throw error;
    }
  }
  workflows.sort((left, right) => left.name.localeCompare(right.name));
  return { workflows, default: null };
}

export function formatLocalWorkflows(catalog, { json = false } = {}) {
  if (json) return JSON.stringify(catalog);
  const lines = catalog.workflows.length
    ? catalog.workflows.map(({ name, file }) => `${name}  ${file}`)
    : ['No workflows found in .pdd/workflows.'];
  lines.push('Review, commit and push workflow changes before using a workflow to start work.');
  return lines.join('\n');
}
