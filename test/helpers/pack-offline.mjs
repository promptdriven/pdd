import { cpSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { execFileSync } from 'node:child_process';

export function bundleInstalledDependencies(rootDir, archivePath, tempDir) {
  const manifest = JSON.parse(readFileSync(join(rootDir, 'package.json'), 'utf8'));
  const deps = Object.keys(manifest.dependencies ?? {});
  if (deps.length === 0) return archivePath;
  const repackDir = join(tempDir, `offline-repack-${process.pid}-${Date.now()}`);
  mkdirSync(repackDir, { recursive: true });
  try {
    const tarEnv = { ...process.env, COPYFILE_DISABLE: '1' };
    execFileSync('tar', ['-xzf', archivePath, '-C', repackDir], { env: tarEnv });
    const pkgDir = join(repackDir, 'package');
    for (const dep of deps) {
      const target = join(pkgDir, 'node_modules', dep);
      mkdirSync(dirname(target), { recursive: true });
      cpSync(join(rootDir, 'node_modules', dep), target, { recursive: true, dereference: true });
    }
    const packedManifestPath = join(pkgDir, 'package.json');
    const packedManifest = JSON.parse(readFileSync(packedManifestPath, 'utf8'));
    packedManifest.bundleDependencies = deps;
    writeFileSync(packedManifestPath, `${JSON.stringify(packedManifest, null, 2)}\n`);
    execFileSync('tar', ['-czf', archivePath, '-C', repackDir, 'package'], { env: tarEnv });
    return archivePath;
  } finally {
    rmSync(repackDir, { recursive: true, force: true });
  }
}
