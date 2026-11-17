import { cpSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const templates = new Map();
process.on('exit', () => {
  for (const dir of templates.values()) {
    try { rmSync(dir, { recursive: true, force: true }); } catch {}
  }
});

export function gitTemplateDir(key, build) {
  let dir = templates.get(key);
  if (!dir) {
    const safe = String(key).replace(/[^a-zA-Z0-9._-]+/g, '_').slice(0, 48);
    dir = realpathSync(mkdtempSync(join(tmpdir(), `pdd-git-tpl-${safe}-`)));
    build(dir);
    templates.set(key, dir);
  }
  return dir;
}

export function copyGitTemplate(key, target, build) {
  cpSync(gitTemplateDir(key, build), target, { recursive: true });
}

export function rewriteGitConfigUrl(configPath, fromUrl, toUrl) {
  writeFileSync(configPath, readFileSync(configPath, 'utf8').replaceAll(fromUrl, toUrl));
}
