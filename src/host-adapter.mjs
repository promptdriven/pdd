import { homedir } from 'node:os';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';

export function installedHostPath(home = homedir()) {
  return join(home, 'pocket', 'app', 'src', 'cli', 'pocket.mjs');
}

export async function loadInstalledHost({ home = homedir(), importer = (url) => import(url), onUnavailable = () => {} } = {}) {
  const moduleUrl = pathToFileURL(installedHostPath(home)).href;
  try {
    const host = await importer(moduleUrl);
    if (typeof host?.runCli === 'function') return host.runCli;
    onUnavailable('incompatible');
    return null;
  } catch (error) {
    onUnavailable(error?.code === 'ERR_MODULE_NOT_FOUND' && error?.url === moduleUrl ? 'missing' : 'load-failed');
    return null;
  }
}
