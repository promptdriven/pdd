// Owned by prompts/cli/affected-tests.prompt.md. Pure, conservative selection.
import { posix } from 'node:path';
import { builtinModules } from 'node:module';
const builtins = new Set(builtinModules);

export const SMOKE_TESTS = ['test/cli-node-version.test.mjs', 'test/command-catalog.test.mjs'];
const entry = path => /^test\/[^/]+\.test\.mjs$/.test(path);
const code = path => /\.(?:mjs|cjs|js)$/.test(path);
const safe = path => typeof path === 'string' && path.length > 0 && !path.startsWith('/') && !path.startsWith('-') && !path.includes('\\') && !path.includes('\0') && !path.split('/').some(p => p === '..' || p === '.' || !p);
const unique = values => [...new Set(values)].sort();
const shared = path => /(?:^|\/)(?:package(?:-lock)?\.json|npm-shrinkwrap\.json|pdd\.json|\.npmrc)$/.test(path)
  || /^(?:scripts|\.github)\//.test(path) || /(?:^|\/)(?:helpers|fixtures)\//.test(path)
  || /^(?:test|tests)\//.test(path) && !entry(path) && !/^test\/runtime\/[^/]+\.json$/.test(path);

// Mark literal/comment spans so fixture program text does not become a live
// import. Template interpolation with import/require is handled as opaque below.
function codeMask(text) {
  const mask = new Uint8Array(text.length).fill(1);
  for (let i = 0; i < text.length; i++) {
    const start = i, char = text[i];
    if (char === '/' && text[i+1] === '/') { while (i < text.length && text[i] !== '\n') i++; }
    else if (char === '/' && text[i+1] === '*') { i += 2; while (i < text.length && !(text[i] === '*' && text[i+1] === '/')) i++; i++; }
    else if (["'", '"', '`'].includes(char)) {
      i++;
      while (i < text.length) { if (text[i] === '\\') i += 2; else if (text[i] === char) break; else i++; }
    } else continue;
    const span = text.slice(start, i+1);
    const interpolationImport = char === '`' && span.includes('${') && /\b(?:import|require)\s*\(/.test(span);
    mask.fill(interpolationImport ? 2 : 0, start, Math.min(i+1, text.length));
  }
  return mask;
}

export function selectAffectedTests({ files, changed, smoke = SMOKE_TESTS }) {
  const inventory = files && typeof files === 'object' && !Array.isArray(files) ? files : {};
  const paths = Object.keys(inventory), tests = paths.filter(entry).sort(), total = tests.length;
  const full = reasons => ({ mode: 'full', reasons: unique(reasons), tests, total });
  if (!paths.every(safe) || !Array.isArray(changed) || !changed.every(safe) || !Array.isArray(smoke) || !smoke.every(safe)
    || !paths.every(path => typeof inventory[path] === 'string') || !total) return full(['invalid-inventory']);
  if (smoke.some(path => !tests.includes(path))) return full(['missing-smoke']);
  const causes = changed.filter(shared);
  if (causes.length) return full(causes.map(path => `shared:${path}`));
  if (changed.some(path => !Object.hasOwn(inventory, path))) return full(['unknown-changed-path']);
  if (changed.some(path => !/\.(?:mjs|cjs|js|md|json|svg)$/.test(path))) return full(['unsupported-change']);

  const deps = new Map(paths.map(path => [path, new Set()]));
  const opaque = new Set();
  const byBase = new Map();
  for (const path of paths) {
    const name = posix.basename(path);
    if (!byBase.has(name)) byBase.set(name, []);
    byBase.get(name).push(path);
  }
  const resolve = (from, ref) => {
    const path = posix.normalize(posix.join(posix.dirname(from), ref.split(/[?#]/)[0]));
    return [path, `${path}.mjs`, `${path}.js`, `${path}/index.mjs`, `${path}/index.js`].find(p => Object.hasOwn(inventory, p));
  };
  const errors = [];
  for (const path of paths) {
    const text = inventory[path], edges = deps.get(path);
    const mask = code(path) ? codeMask(text) : null;
    if (code(path)) {
      // Computed access is an explicit overapproximation, including reads made by
      // a helper or a spawned CLI. Its reverse consumers inherit the dependency.
      if (mask.includes(2) || /\b(?:getBuiltinModule|createRequire|eval|Function|binding)\b/.test(text) || /['"](?:node:)?(?:fs(?:\/promises)?|child_process)['"]/.test(text) || /\b(?:readFile(?:Sync)?|readdir(?:Sync)?|opendir(?:Sync)?|spawn(?:Sync)?|execFile(?:Sync)?|execSync)\b/.test(text)
        || /\b(?:import|require)\s*\(\s*(?!['"])/.test(text)) opaque.add(path);
      const imports = /\b(?:import\s+(?:[^;'"]*?\s+from\s*)?|export\s+[^;'"]*?\s+from\s*|(?:import|require)\s*\(\s*)['"]([^'"\n]+)['"]/g;
      for (const match of text.matchAll(imports)) {
        if (!mask[match.index]) continue;
        const ref = match[1];
        if (ref.startsWith('.')) {
          const target = resolve(path, ref);
          if (target) edges.add(target); else errors.push(`unresolved:${path}:${ref}`);
        } else if (!ref.startsWith('node:') && !builtins.has(ref)) errors.push(`external:${path}:${ref}`);
      }
    }
    // Literal references cover new URL(), scenario entry_path/story_path and
    // Markdown links. Basename lookup deliberately includes ambiguous matches.
    for (const match of text.matchAll(/[\w@.+/-]+\.(?:mjs|cjs|js|prompt\.md|md|json|svg)\b/g)) {
      const ref = match[0];
      if (Object.hasOwn(inventory, ref)) edges.add(ref);
      const target = resolve(path, ref);
      if (target) edges.add(target);
      for (const candidate of byBase.get(posix.basename(ref)) ?? []) edges.add(candidate);
    }
  }
  // Only unresolved imports in a dependency chain that can reach a native test
  // make selection unsafe. Fixture programs are not test runner dependencies.
  const reachable = new Set(), visit = path => {
    if (reachable.has(path)) return;
    reachable.add(path);
    for (const dep of deps.get(path) ?? []) visit(dep);
  };
  tests.forEach(visit);
  const relevantErrors = errors.filter(error => [...reachable].some(path => (!opaque.has(path) && error.startsWith(`unresolved:${path}:`)) || error.startsWith(`external:${path}:`)));
  if (relevantErrors.length) return full(relevantErrors);

  const impacted = new Set(changed);
  for (const path of changed) {
    if (path.endsWith('.prompt.md')) {
      const owner = path.replace(/^prompts\/cli\//, 'src/').replace(/\.prompt\.md$/, '.mjs');
      const scenarios = paths.filter(p => /^test\/runtime\/.*\.json$/.test(p) && inventory[p].includes(path));
      if (!Object.hasOwn(inventory, owner) && !scenarios.length) return full([`unmapped-prompt:${path}`]);
      if (Object.hasOwn(inventory, owner)) impacted.add(owner);
      scenarios.forEach(p => impacted.add(p));
    }
    const stem = posix.basename(path).replace(/\.(?:prompt\.md|mjs|cjs|js|md|json|svg)$/, '');
    tests.filter(test => posix.basename(test).startsWith(`${stem}.`)).forEach(test => impacted.add(test));
  }
  if (changed.length) opaque.forEach(path => impacted.add(path));
  let grew = true;
  while (grew) {
    grew = false;
    for (const [path, edges] of deps) if (!impacted.has(path) && [...edges].some(dep => impacted.has(dep))) { impacted.add(path); grew = true; }
  }
  return { mode: 'affected', reasons: unique(changed), tests: unique([...tests.filter(path => impacted.has(path)), ...smoke]), total };
}
