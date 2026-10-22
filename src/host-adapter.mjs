import { homedir } from 'node:os';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';

export function installedHostPath(home = homedir()) {
  return join(home, 'pocket', 'app', 'src', 'cli', 'pocket.mjs');
}

export async function loadInstalledHost({ home = homedir(), importer = (url) => import(url) } = {}) {
  try {
    const moduleUrl = pathToFileURL(installedHostPath(home)).href;
    const host = await importer(moduleUrl);
    return typeof host?.runCli === 'function' ? host.runCli : null;
  } catch {
    return null;
  }
}
