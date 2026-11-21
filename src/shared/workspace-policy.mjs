// Layer-0 workspace policy, prompt interface block scanning, and preflight slice helpers.
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { closeSync, constants, fstatSync, lstatSync, openSync, readFileSync, realpathSync } from 'node:fs';
import { join, parse, resolve, sep } from 'node:path';
import { gitFiles } from './git-context.mjs';
import { isSecretPath } from './safe-read.mjs';

const CONTROL = 'pdd-workspace.json';
const MAX_POLICY_BYTES = 10_485_760;

// The engine's _INTERFACE regex for embedded Runtime interface blocks.
const INTERFACE = /<details\b[^>]*>\s*<summary\b[^>]*>\s*(?:<strong\b[^>]*>\s*)?Runtime\s+interface(?:\s*:\s*[^<]+?)?\s*(?:<\/strong\s*>\s*)?(?:\s*:\s*[^<]+?)?\s*<\/summary\s*>\s*```json\b\s*([\s\S]*?)\s*```\s*<\/details\s*>/gid;

export class RuntimeWorkspaceError extends Error {
  constructor(code, message) {
    super(`${code}: ${message}`);
    this.code = code;
    this.exitCode = 4;
  }
}

const fail = (code, reason) => {
  throw new RuntimeWorkspaceError(
    code,
    `${CONTROL}: ${reason}. Correct this regular local policy file and retry.`,
  );
};

export function nativeWorkspaceFiles(root) {
  let observed;
  let canonicalRoot;
  return {
    stat({ path }) {
      try {
        canonicalRoot = realpathSync(root);
        const full = resolve(canonicalRoot, path);
        let at = parse(full).root;
        for (const part of full.slice(at.length).split(sep).filter(Boolean)) {
          at = join(at, part);
          const st = lstatSync(at);
          if (st.isSymbolicLink()) throw Error('symbolic link');
          if (at !== full && !st.isDirectory()) throw Error('non-directory ancestor');
          if (at === full) {
            if (!st.isFile()) throw Error('not regular');
            observed = st;
          }
        }
      } catch (error) {
        if (error.code === 'ENOENT') return { exists: false, is_symlink: false, size: 0 };
        throw error;
      }
      const git = spawnSync('git', ['ls-files', '-z', '-co', '--exclude-standard', '--', path], { cwd: canonicalRoot });
      if (git.status !== 0 || !git.stdout.toString().split('\0').includes(path)) throw Error('not Git-visible');
      return { exists: true, is_symlink: false, size: observed.size };
    },
    read({ path }) {
      const fd = openSync(join(canonicalRoot, path), constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_NONBLOCK);
      try {
        const st = fstatSync(fd);
        if (
          !observed
          || !st.isFile()
          || st.size > MAX_POLICY_BYTES
          || st.ino !== observed.ino
          || st.dev !== observed.dev
          || st.mtimeMs !== observed.mtimeMs
          || st.ctimeMs !== observed.ctimeMs
        ) {
          throw Error('changed');
        }
        const content = new TextDecoder('utf-8', { fatal: true }).decode(readFileSync(fd));
        const after = fstatSync(fd);
        if (after.size !== st.size || after.mtimeMs !== st.mtimeMs || after.ctimeMs !== st.ctimeMs) {
          throw Error('changed');
        }
        return { content };
      } finally {
        closeSync(fd);
      }
    },
  };
}

const validAllowedPath = value => typeof value === 'string'
  && Boolean(value)
  && !/[\\\x00-\x1f\x7f*?\[\]{}:$%]/.test(value)
  && !value.startsWith('~')
  && !value.startsWith('/')
  && !value.replace(/\/$/, '').split('/').some(p => !p || p === '.' || p === '..' || p === '.git');

export function loadRuntimeWorkspace({ root }, files = nativeWorkspaceFiles(root)) {
  let stat;
  let text;
  try {
    stat = files.stat({ path: CONTROL });
    if (!stat.exists) return Object.freeze({ configured: false, allowed_paths: Object.freeze([]) });
    if (stat.is_symlink || !Number.isInteger(stat.size) || stat.size < 0 || stat.size > MAX_POLICY_BYTES) {
      fail('workspace-config-unsafe', 'unsafe or oversized policy');
    }
    text = files.read({ path: CONTROL }).content;
  } catch (error) {
    if (error instanceof RuntimeWorkspaceError) throw error;
    fail('workspace-config-unsafe', 'cannot safely read policy');
  }
  let doc;
  try {
    doc = JSON.parse(text);
  } catch {
    fail('workspace-config-invalid', 'expected valid JSON');
  }
  if (
    !doc
    || Array.isArray(doc)
    || typeof doc !== 'object'
    || Object.keys(doc).length !== 1
    || !Array.isArray(doc.allowed_paths)
    || !doc.allowed_paths.every(validAllowedPath)
  ) {
    fail('workspace-config-invalid', 'expected only allowed_paths with safe repository-relative files or directory/ entries');
  }
  return Object.freeze({ configured: true, allowed_paths: Object.freeze([...new Set(doc.allowed_paths)]) });
}

export function allowsRuntimePath(policy, path) {
  return !policy.configured
    || (typeof path === 'string' && policy.allowed_paths.some(p => (p.endsWith('/') ? path.startsWith(p) && path.length > p.length : path === p)));
}

export function requireRuntimePath(policy, { path, from = 'Source', chain = [], role = 'source' }) {
  if (!allowsRuntimePath(policy, path)) {
    throw new RuntimeWorkspaceError(
      'workspace-path-outside',
      `${[...chain, from, path].filter(Boolean).join(' -> ')}: required ${role} is outside ${CONTROL}. Correct or move the reference, or deliberately change allowed_paths.`,
    );
  }
  return path;
}

export const workspace = Object.freeze({
  policy: loadRuntimeWorkspace,
  allows: allowsRuntimePath,
});

export function runtimeWorkspaceSlice() {
  return {
    RuntimeWorkspaceError,
    nativeWorkspaceFiles,
    loadRuntimeWorkspace,
    allowsRuntimePath,
    requireRuntimePath,
  };
}

export const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
export const interfaceBlocks = text => [...String(text ?? '').matchAll(INTERFACE)];
export const proseSha256 = text => sha256(Buffer.from(String(text ?? '').replace(INTERFACE, ''), 'utf8'));

/**
 * Layer-0 preflight slice exposing pure Git listing, secret-path checks, prompt interface
 * block scanning, and workspace policy helpers without loading `@promptdriven/runtime-client`.
 */
export function runtimePreflightSlice() {
  return {
    gitFiles,
    isSecretPath,
    interfaceBlocks,
    sha256,
    proseSha256,
    loadRuntimeWorkspace,
    allowsRuntimePath,
    requireRuntimePath,
    workspace,
  };
}
