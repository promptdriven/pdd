// Owned by prompts/cli/affected-tests.prompt.md. Pure, conservative selection.
import { posix } from 'node:path';
import { builtinModules } from 'node:module';
import { Script } from 'node:vm';
const builtins = new Set(builtinModules);

export const SMOKE_TESTS = ['test/cli-node-version.test.mjs', 'test/command-catalog.test.mjs'];
const entry = path => /^test\/[^/]+\.test\.mjs$/.test(path);
const code = path => /\.(?:mjs|cjs|js)$/.test(path);
const safe = path => typeof path === 'string' && path.length > 0 && !path.startsWith('/') && !path.startsWith('-') && !path.includes('\\') && !path.includes('\0') && !path.split('/').some(p => p === '..' || p === '.' || !p);
const unique = values => [...new Set(values)].sort();
const shared = path => /(?:^|\/)(?:package(?:-lock)?\.json|npm-shrinkwrap\.json|pdd\.json|\.npmrc)$/.test(path)
  || /^(?:scripts|\.github)\//.test(path) || /(?:^|\/)(?:helpers|fixtures)\//.test(path)
  || /^(?:test|tests)\//.test(path) && !entry(path) && !/^test\/runtime\/[^/]+\.json$/.test(path);

// Positive proof, not a list of loader spellings. Only a completely consumed
// declaration subset can establish omission. All other JavaScript is opaque.
// Strings are single tokens: comments/semicolons inside them stay literal.
function staticDependencies(text) {
  const token = /\s+|\/\/[^\r\n\u2028\u2029]*|\/\*[\s\S]*?\*\/|'[^'\\\r\n]*'|"[^"\\\r\n]*"|[A-Za-z_$][\w$]*|\d+(?:\.\d+)?|[{}*,;=+-]/y;
  const statements = [[]];
  for (let offset = 0; offset < text.length;) {
    token.lastIndex = offset;
    const match = token.exec(text);
    if (!match) return null;
    const value = match[0];
    offset = token.lastIndex;
    if (/^(?:\s|\/)/.test(value)) continue;
    if (/^(?:require|createRequire|eval|Function|await)$/.test(value)) return null;
    if (value === ';') statements.push([]);
    else statements.at(-1).push(value);
  }
  const id = '[A-Za-z_$][\\w$]*';
  const named = `${id}(?:\\s+as\\s+${id})?`;
  const names = `\\{\\s*(?:${named}(?:\\s*,\\s*${named})*\\s*,?)?\\s*\\}`;
  const star = `\\*\\s+as\\s+${id}`;
  const clause = `(?:${id}(?:\\s*,\\s*(?:${star}|${names}))?|${star}|${names})`;
  const literal = "(?:'[^'\\\\\\r\\n]*'|\"[^\"\\\\\\r\\n]*\")";
  const scalar = `(?:${literal}|[+-]?\\s*\\d+(?:\\.\\d+)?|true|false|null)`;
  const imports = new RegExp(`^import\\s+(?:(${clause})\\s+from\\s+)?(${literal})$`);
  const reexports = new RegExp(`^export\\s+(\\*(?:\\s+as\\s+${id})?|${names})\\s+from\\s+(${literal})$`);
  const declaration = new RegExp(`^(export\\s+)?((?:const|let|var)\\s+(${id})\\s*=\\s*${scalar})$`);
  const defaultExport = new RegExp(`^export\\s+default\\s+(${scalar})$`);
  const refs = [], body = [], exported = new Set();
  const addExport = name => {
    if (exported.has(name)) return false;
    exported.add(name);
    return true;
  };
  const bindings = value => {
    const locals = [];
    const first = value.match(new RegExp(`^(${id})(?:\\s*,\\s*|$)`));
    if (first) { locals.push(first[1]); value = value.slice(first[0].length); }
    if (value.startsWith('*')) locals.push(value.split(/\s+/).at(-1));
    else if (value) for (const name of value.slice(1, -1).split(',').filter(name => name.trim())) locals.push(name.trim().split(/\s+as\s+/).at(-1));
    return locals;
  };
  for (const tokens of statements) {
    if (!tokens.length) continue;
    const source = tokens.join(' ');
    let match;
    if ((match = imports.exec(source))) {
      refs.push(match[2].slice(1, -1));
      if (match[1]) for (const local of bindings(match[1])) body.push(`const ${local} = undefined;`);
    } else if ((match = reexports.exec(source))) {
      refs.push(match[2].slice(1, -1));
      const spec = match[1];
      const names = spec.startsWith('{') ? bindings(spec) : spec === '*' ? [] : [spec.split(/\s+/).at(-1)];
      if (!names.every(addExport)) return null;
    } else if ((match = declaration.exec(source))) {
      if (match[1] && !addExport(match[3])) return null;
      body.push(`${match[2]};`);
    } else if ((match = defaultExport.exec(source))) {
      if (!addExport('default')) return null;
      body.push(`void ${match[1]};`);
    } else return null;
  }
  // Validate reserved words, duplicate bindings and literal syntax. This only
  // compiles the proven subset; it never runs repository code or a loader.
  try { new Script(`"use strict";\n${body.join('\n')}`); } catch { return null; }
  return refs;
}

// Mark literal/comment spans so fixture program text does not become a live
// import. Template interpolation with import/require is handled as opaque below.
function codeMask(text) {
  const mask = new Uint8Array(text.length).fill(1);
  const source = text.split('');
  let uncertainTemplate = false, uncertainSlash = false;
  for (let i = 0; i < text.length; i++) {
    const start = i, char = text[i];
    let comment = false;
    if (char === '/' && text[i+1] === '/') { comment = true; while (i < text.length && !/[\r\n\u2028\u2029]/.test(text[i])) i++; }
    else if (char === '/' && text[i+1] === '*') { comment = true; i += 2; while (i < text.length && !(text[i] === '*' && text[i+1] === '/')) i++; i++; }
    else if (["'", '"', '`'].includes(char)) {
      i++;
      while (i < text.length) { if (text[i] === '\\') i += 2; else if (text[i] === char) break; else i++; }
    } else if (char === '/') {
      // Regex and division need expression context. Stop before their contents
      // can be mistaken for strings/comments and conceal executable imports.
      uncertainSlash = true;
      mask.fill(0, start);
      break;
    } else continue;
    const span = text.slice(start, i+1);
    const interpolationImport = char === '`' && span.includes('${') && /\b(?:import|require)\s*(?:\(|\/[/*])/.test(span);
    // Interpolation bodies are not parsed here. Comment-bearing dependency
    // syntax in them must not evade external-import fallback.
    // The first span ends at a nested backtick, so it cannot classify the
    // remainder of an interpolation. Fall back before masking any such span.
    uncertainTemplate ||= char === '`' && span.includes('${');
    mask.fill(interpolationImport ? 2 : 0, start, Math.min(i+1, text.length));
    // Keep offsets and newlines, and leave literal contents intact. Dependency
    // matching then treats real comments exactly like whitespace.
    if (comment) for (let j = start; j <= i && j < text.length; j++) {
      if (!/[\r\n\u2028\u2029]/.test(source[j])) source[j] = ' ';
    }
  }
  return { mask, source: source.join(''), uncertainTemplate, uncertainSlash };
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
  const localPaths = (from, ref) => unique([ref, ref.split(/[?#]/)[0]]
    .map(value => posix.normalize(posix.join(posix.dirname(from), value))));
  // Keep the union across loaders. Choosing one candidate can discard the file
  // actually loaded by require (which prefers .js over the ESM alternatives).
  const resolve = (from, ref) => unique(localPaths(from, ref).flatMap(path =>
    [path, ...['.mjs', '.js', '.cjs', '.json', '.node'].flatMap(ext => [`${path}${ext}`, `${path}/index${ext}`])])
    .filter(path => Object.hasOwn(inventory, path)));
  const errors = [];
  for (const path of paths) {
    const text = inventory[path], edges = deps.get(path);
    if (code(path)) {
      const proven = path.endsWith('.mjs') ? staticDependencies(text) : null;
      if (proven === null) opaque.add(path);
      else for (const ref of proven) {
        const target = posix.normalize(posix.join(posix.dirname(path), ref));
        // Node builtins, extension guesses, URL decoding and non-JS loaders do
        // not prove a closed relative ESM graph. Conservative edges below may
        // add consumers, but cannot turn these into a proof.
        if (!/^(?:\.\/|\.\.\/)/.test(ref) || /[\u0000-\u0020\u007f?#%]/.test(ref)
          || !/\.(?:mjs|js)$/.test(target) || !Object.hasOwn(inventory, target)) opaque.add(path);
        else edges.add(target);
      }
      const { mask, source, uncertainTemplate, uncertainSlash } = codeMask(text);
      if (uncertainTemplate) errors.push(`unsupported-template-dependency:${path}`);
      if (uncertainSlash) errors.push(`unsupported-slash-syntax:${path}`);
      const computedImport = [...source.matchAll(/\b(?:import|require)\s*\(/g)].some(match =>
        mask[match.index] && !/^\s*(?:'[^'\\\r\n]*'|"[^"\\\r\n]*")\s*(?:\)|,)/.test(source.slice(match.index + match[0].length)));
      // A loader can escape the direct-call matcher through an alias or a
      // Unicode identifier escape. Their consumers still depend on any change.
      const indirectLoader = [...source.matchAll(/\brequire\b/g)].some(match =>
        mask[match.index] && !/^\s*\(/.test(source.slice(match.index + match[0].length)));
      const escapedIdentifier = [...source.matchAll(/\\u/g)].some(match => mask[match.index]);
      // Computed access is an explicit overapproximation, including reads made by
      // a helper or a spawned CLI. Its reverse consumers inherit the dependency.
      if (mask.includes(2) || /\b(?:getBuiltinModule|createRequire|eval|Function|binding)\b/.test(text) || /['"](?:node:)?(?:fs(?:\/promises)?|child_process)['"]/.test(text) || /\b(?:readFile(?:Sync)?|readdir(?:Sync)?|opendir(?:Sync)?|spawn(?:Sync)?|execFile(?:Sync)?|execSync)\b/.test(text)
        || /\b(?:import|require)\s*\(\s*(?!['"])/.test(text) || computedImport || indirectLoader || escapedIdentifier) opaque.add(path);
      const imports = /\b(?:import\s+(?:[^;'"]*?\s+from\s*)?|export\s+[^;'"]*?\s+from\s*|(?:import|require)\s*\(\s*)['"]([^'"\n]+)['"]/g;
      for (const match of source.matchAll(imports)) {
        if (!mask[match.index]) continue;
        const ref = match[1];
        if (ref.startsWith('.')) {
          const targets = resolve(path, ref);
          if (targets.length) targets.forEach(target => edges.add(target)); else errors.push(`unresolved:${path}:${ref}`);
          if (localPaths(path, ref).some(target => Object.hasOwn(inventory, `${target}/package.json`)))
            errors.push(`unsupported-directory-dependency:${path}`);
        } else if (!ref.startsWith('node:') && !builtins.has(ref)) errors.push(`external:${path}:${ref}`);
      }
    } else opaque.add(path);
    // Literal references cover new URL(), scenario entry_path/story_path and
    // Markdown links. Basename lookup deliberately includes ambiguous matches.
    for (const match of text.matchAll(/[\w@.+/-]+\.(?:mjs|cjs|js|prompt\.md|md|json|svg)\b/g)) {
      const ref = match[0];
      if (Object.hasOwn(inventory, ref)) edges.add(ref);
      resolve(path, ref).forEach(target => edges.add(target));
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
  const relevantErrors = errors.filter(error => [...reachable].some(path => error.startsWith(`unresolved:${path}:`) || error.startsWith(`external:${path}:`) || error === `unsupported-template-dependency:${path}` || error === `unsupported-slash-syntax:${path}` || error === `unsupported-directory-dependency:${path}`));
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
  opaque.forEach(path => impacted.add(path));
  let grew = true;
  while (grew) {
    grew = false;
    for (const [path, edges] of deps) if (!impacted.has(path) && [...edges].some(dep => impacted.has(dep))) { impacted.add(path); grew = true; }
  }
  return { mode: 'affected', reasons: unique(changed), tests: unique([...tests.filter(path => impacted.has(path)), ...smoke]), total };
}
