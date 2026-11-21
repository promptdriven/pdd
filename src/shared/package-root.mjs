// Layer-0 canonical PDD package root resolver.
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

/**
 * Absolute path to the installed `@promptdriven/pdd` package root directory.
 */
export const PACKAGE_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');

/**
 * Return the canonical installed package root directory.
 */
export function packageRoot() {
  return PACKAGE_ROOT;
}

/**
 * Resolve one or more path segments relative to the installed PDD package root.
 */
export function resolvePackagePath(...segments) {
  return join(PACKAGE_ROOT, ...segments);
}
