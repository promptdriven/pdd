// Prompt: prompts/cli/prove-mutation.prompt.md

// Opt-in `pdd prove --mutation-check` engine: deterministic AST/lexer guard mutations in an isolated disposable sandbox.
import { spawnSync } from 'node:child_process';
import {
  cpSync,
  existsSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  realpathSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { dirname, join, relative, sep } from 'node:path';
import { canonicalRepoPath, formatTeachingDetail, readSafeUtf8, scrubChildEnv } from './lint/diagnostics.mjs';
import {
  detectSignalInterruption,
  discoverFormalScope,
  isProductionCodeFile,
  lexCStyleSource,
  resolvePythonBinary,
  runIsolatedFormalFile,
  runIsolatedFormalFileAsync,
} from './formal-verify.mjs';
import {
  collectDiffLines,
  collectFormalLineCoverage,
  collectFormalLineCoverageAsync,
  withSignalSafeTempDir,
  withSignalSafeTempDirAsync,
} from './prove-coverage.mjs';

const JS_FILE_RE = /\.(?:mjs|cjs|js|ts|tsx|jsx)$/i;
const JS_CHECKABLE_RE = /\.(?:mjs|cjs|js)$/i;
const PY_FILE_RE = /\.py$/i;
const GO_FILE_RE = /\.go$/i;

const KIND_PRIORITY = Object.freeze({
  'comparison-flip': 0,
  'boolean-op-flip': 1,
  'guard-negate': 2,
  'return-flip': 3,
});

const roundPct = (num, den) => (den > 0 ? Math.round((num * 1000) / den) / 10 : null);

function clampMaxMutations(maxMutations) {
  const n = Number.isInteger(maxMutations) ? maxMutations : 3;
  return Math.max(1, Math.min(3, n));
}

function isValidJsSyntax(filePath, content) {
  if (!JS_CHECKABLE_RE.test(filePath)) return true;
  const inputType = /\.cjs$/i.test(filePath) ? 'commonjs' : 'module';
  const res = spawnSync(process.execPath, [`--input-type=${inputType}`, '--check'], {
    input: content,
    encoding: 'utf8',
    timeout: 5000,
    stdio: ['pipe', 'pipe', 'pipe'],
  });
  return res.status === 0;
}

function buildLineStarts(text) {
  const starts = [0];
  for (let i = 0; i < text.length; i += 1) if (text[i] === '\n') starts.push(i + 1);
  return starts;
}

function findMatchingParen(code, openIdx, maxEnd) {
  let depth = 0;
  for (let i = openIdx; i < maxEnd; i += 1) {
    if (code[i] === '(') depth += 1;
    else if (code[i] === ')') {
      depth -= 1;
      if (depth === 0) return i;
    }
  }
  return -1;
}

const JS_COMP_FLIPS = [
  { from: '===', to: '!==' },
  { from: '!==', to: '===' },
  { from: '==', to: '!=' },
  { from: '!=', to: '==' },
  { from: '<=', to: '>' },
  { from: '>=', to: '<' },
  { from: '<', to: '>=' },
  { from: '>', to: '<=' },
];

function findComparisonFlipOnLine(rawLine, maskedLine) {
  for (const { from, to } of JS_COMP_FLIPS) {
    let idx = maskedLine.indexOf(from);
    while (idx >= 0) {
      const prev = idx > 0 ? maskedLine[idx - 1] : '';
      const next = maskedLine[idx + from.length] ?? '';
      let valid = true;
      if (from === '==' && (prev === '=' || prev === '!' || next === '=')) valid = false;
      if (from === '!=' && next === '=') valid = false;
      if (from === '<' && (prev === '<' || next === '<' || next === '=' || /[A-Za-z_/]/.test(next))) valid = false;
      if (from === '>' && (prev === '=' || prev === '>' || prev === '-' || next === '>' || next === '=')) valid = false;
      if (valid) {
        return {
          kind: 'comparison-flip',
          from,
          to,
          mutatedLine: `${rawLine.slice(0, idx)}${to}${rawLine.slice(idx + from.length)}`,
        };
      }
      idx = maskedLine.indexOf(from, idx + from.length);
    }
  }
  return null;
}

function findBoolOpFlipOnLine(rawLine, maskedLine) {
  for (const [from, to] of [['&&', '||'], ['||', '&&']]) {
    const idx = maskedLine.indexOf(from);
    if (idx >= 0) {
      const next = maskedLine[idx + 2] ?? '';
      const prev = idx > 0 ? maskedLine[idx - 1] : '';
      if (next === '=' || prev === from[0]) continue;
      return {
        kind: 'boolean-op-flip',
        from,
        to,
        mutatedLine: `${rawLine.slice(0, idx)}${to}${rawLine.slice(idx + 2)}`,
      };
    }
  }
  return null;
}

function findEnclosingGuardHeader(maskedLines, idx) {
  let neededOpen = 0;
  const minIdx = Math.max(0, idx - 20);
  for (let j = idx - 1; j >= minIdx; j -= 1) {
    const line = maskedLines[j] ?? '';
    for (let c = line.length - 1; c >= 0; c -= 1) {
      const ch = line[c];
      if (ch === ')') neededOpen += 1;
      else if (ch === '(') {
        if (neededOpen === 0) {
          const prefix = line.slice(0, c);
          if (/\b(?:if|while)\s*$/.test(prefix)) return { kind: 'if-while', headerLine: j + 1, openCol: c };
          if (/\breturn\b/.test(prefix)) return { kind: 'return', headerLine: j + 1, openCol: c };
          // Continue scanning outward for nested parens inside `if ((...) || ...)`
        } else {
          neededOpen -= 1;
        }
      } else if (neededOpen === 0 && (ch === ';' || ch === '{' || ch === '}')) {
        return null;
      }
    }
    if (neededOpen === 0 && /^\s*return\b/.test(line) && !line.includes(';')) {
      return { kind: 'return', headerLine: j + 1, openCol: null };
    }
  }
  return null;
}

function generateJsGuardMutations(filePath, sourceText, changedLines) {
  const src = String(sourceText ?? '');
  const rawLines = src.split('\n');
  const masked = lexCStyleSource(src).codeOnly;
  const maskedLines = masked.split('\n');
  const lineStarts = buildLineStarts(src);
  const candidates = [];

  for (const lineNo of changedLines) {
    const idx = lineNo - 1;
    if (idx < 0 || idx >= rawLines.length) continue;
    const rawLine = rawLines[idx];
    const mLine = maskedLines[idx] ?? '';
    if (!mLine.trim()) continue;

    const enclosing = findEnclosingGuardHeader(maskedLines, idx);
    const statementLine = enclosing ? enclosing.headerLine : lineNo;

    const tryEmit = (kind, description, mutatedLine) => {
      if (mutatedLine === rawLine) return false;
      const nextLines = [...rawLines];
      nextLines[idx] = mutatedLine;
      const mutatedContent = nextLines.join('\n');
      if (!isValidJsSyntax(filePath, mutatedContent)) return false;
      candidates.push({
        file: filePath,
        line: lineNo,
        statementLine,
        kind,
        description,
        original: rawLine.trim(),
        mutated: mutatedLine.trim(),
        mutatedContent,
      });
      return true;
    };

    // 1. Comparison / boolean flip on single-line OR multiline continuation conditional/return/ternary line
    const isGuardContext = Boolean(enclosing) || /\b(?:if|while|return)\b/.test(mLine) || mLine.includes('?') || /=>/.test(mLine);
    if (isGuardContext) {
      const comp = findComparisonFlipOnLine(rawLine, mLine);
      if (comp && tryEmit('comparison-flip', `Flip \`${comp.from}\` to \`${comp.to}\` at ${filePath}:${lineNo}`, comp.mutatedLine)) {
        continue;
      }
      const boolOp = findBoolOpFlipOnLine(rawLine, mLine);
      if (boolOp && tryEmit('boolean-op-flip', `Flip \`${boolOp.from}\` to \`${boolOp.to}\` at ${filePath}:${lineNo}`, boolOp.mutatedLine)) {
        continue;
      }
    }

    // 2. `if (<cond>)` negation (single-line, multiline header, or multiline continuation line)
    const ifMatch = /\bif\s*\(/.exec(mLine);
    if (ifMatch) {
      const openPos = ifMatch.index + ifMatch[0].length - 1;
      const closePos = findMatchingParen(mLine, openPos, mLine.length);
      if (closePos > openPos + 1) {
        const inner = rawLine.slice(openPos + 1, closePos);
        const mutatedLine = `${rawLine.slice(0, openPos + 1)}!(${inner})${rawLine.slice(closePos)}`;
        if (tryEmit('guard-negate', `Negate \`if\` guard condition at ${filePath}:${lineNo}`, mutatedLine)) {
          continue;
        }
      } else {
        const absOpen = lineStarts[idx] + openPos;
        const absClose = findMatchingParen(masked, absOpen, Math.min(masked.length, absOpen + 400));
        if (absClose > absOpen + 1) {
          const mutatedContent = `${src.slice(0, absOpen + 1)}!(${src.slice(absOpen + 1, absClose)})${src.slice(absClose)}`;
          if (isValidJsSyntax(filePath, mutatedContent)) {
            candidates.push({
              file: filePath,
              line: lineNo,
              statementLine,
              kind: 'guard-negate',
              description: `Negate multiline \`if\` guard condition at ${filePath}:${lineNo}`,
              original: rawLine.trim(),
              mutated: `${rawLine.slice(0, openPos + 1)}!(${rawLine.slice(openPos + 1)}`.trim(),
              mutatedContent,
            });
            continue;
          }
        }
      }
    } else if (enclosing?.kind === 'if-while' && Number.isInteger(enclosing.openCol)) {
      const headerIdx = enclosing.headerLine - 1;
      const absOpen = lineStarts[headerIdx] + enclosing.openCol;
      const absClose = findMatchingParen(masked, absOpen, Math.min(masked.length, absOpen + 400));
      if (absClose > absOpen + 1) {
        const mutatedContent = `${src.slice(0, absOpen + 1)}!(${src.slice(absOpen + 1, absClose)})${src.slice(absClose)}`;
        if (isValidJsSyntax(filePath, mutatedContent)) {
          candidates.push({
            file: filePath,
            line: lineNo,
            statementLine: enclosing.headerLine,
            kind: 'guard-negate',
            description: `Negate multiline \`if\` guard condition covering ${filePath}:${lineNo}`,
            original: rawLine.trim(),
            mutated: `!(...) /* enclosing line ${enclosing.headerLine} */`,
            mutatedContent,
          });
          continue;
        }
      }
    }

    // 3. Boolean / null return guard flip
    const retBool = /\breturn\s+(true|false)\b/.exec(mLine);
    if (retBool) {
      const flipped = retBool[1] === 'true' ? 'false' : 'true';
      const valStart = retBool.index + retBool[0].lastIndexOf(retBool[1]);
      const mutatedLine = `${rawLine.slice(0, valStart)}${flipped}${rawLine.slice(valStart + retBool[1].length)}`;
      if (tryEmit('return-flip', `Flip \`return ${retBool[1]}\` to \`return ${flipped}\` at ${filePath}:${lineNo}`, mutatedLine)) {
        continue;
      }
    }
    const retNull = /\breturn\s+null\b/.exec(mLine);
    if (retNull) {
      const valStart = retNull.index + retNull[0].lastIndexOf('null');
      const mutatedLine = `${rawLine.slice(0, valStart)}{}${rawLine.slice(valStart + 4)}`;
      tryEmit('return-flip', `Mutate \`return null\` to \`return {}\` at ${filePath}:${lineNo}`, mutatedLine);
    }
  }

  return candidates;
}

const PY_AST_MUTATOR_SCRIPT = `
import ast, copy, json, sys

payload = json.loads(sys.stdin.read())
src = payload['source']
file_path = payload['file']
changed = set(payload['changedLines'])

try:
    tree = ast.parse(src, filename=file_path)
except SyntaxError:
    print('[]')
    sys.exit(0)

lines = src.splitlines(keepends=True)
line_byte_starts = [0]
raw_bytes = src.encode('utf-8')
for ln in lines:
    line_byte_starts.append(line_byte_starts[-1] + len(ln.encode('utf-8')))

def node_changed_lines(node):
    lo = getattr(node, 'lineno', None)
    hi = getattr(node, 'end_lineno', None) or lo
    if lo is None:
        return []
    return [ln for ln in range(lo, hi + 1) if ln in changed]

def replace_span(node, replacement, display_line=None):
    start = line_byte_starts[node.lineno - 1] + node.col_offset
    end = line_byte_starts[node.end_lineno - 1] + node.end_col_offset
    mutated = (raw_bytes[:start] + replacement.encode('utf-8') + raw_bytes[end:]).decode('utf-8')
    try:
        ast.parse(mutated, filename=file_path)
    except SyntaxError:
        return None
    dln = display_line or node.lineno
    orig_line = lines[dln - 1].rstrip('\\r\\n').strip() if 0 <= dln - 1 < len(lines) else replacement
    mut_lines = mutated.splitlines()
    if node.end_lineno != node.lineno:
        mut_line = replacement.strip()
    else:
        mut_line = mut_lines[dln - 1].strip() if 0 <= dln - 1 < len(mut_lines) else replacement
    return mutated, orig_line, mut_line

COMP_FLIP = {
    ast.Lt: (ast.GtE, '<', '>='),
    ast.LtE: (ast.Gt, '<=', '>'),
    ast.Gt: (ast.LtE, '>', '<='),
    ast.GtE: (ast.Lt, '>=', '<'),
    ast.Eq: (ast.NotEq, '==', '!='),
    ast.NotEq: (ast.Eq, '!=', '=='),
    ast.Is: (ast.IsNot, 'is', 'is not'),
    ast.IsNot: (ast.Is, 'is not', 'is'),
    ast.In: (ast.NotIn, 'in', 'not in'),
    ast.NotIn: (ast.In, 'not in', 'in'),
}

candidates = []
seen_lines = set()

def emit(line_no, kind, desc, res, statement_line=None):
    if res is None or line_no in seen_lines:
        return False
    mutated, orig_line, mut_line = res
    if mutated == src:
        return False
    seen_lines.add(line_no)
    candidates.append({
        'file': file_path,
        'line': line_no,
        'statementLine': statement_line if statement_line is not None else line_no,
        'kind': kind,
        'description': desc,
        'original': orig_line,
        'mutated': mut_line,
        'mutatedContent': mutated,
    })
    return True

def collect_cond_exprs(expr):
    out = []
    def walk(n):
        if isinstance(n, (ast.Lambda, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
            return
        if isinstance(n, (ast.Compare, ast.BoolOp)):
            out.append(n)
        for child in ast.iter_child_nodes(n):
            walk(child)
    walk(expr)
    return out

def mutate_cond_expr(expr, target_line, statement_line):
    if isinstance(expr, ast.Compare) and len(expr.ops) >= 1:
        op_cls = type(expr.ops[0])
        if op_cls in COMP_FLIP:
            new_cls, old_sym, new_sym = COMP_FLIP[op_cls]
            cloned = copy.deepcopy(expr)
            cloned.ops[0] = new_cls()
            res = replace_span(expr, ast.unparse(cloned), target_line)
            if emit(target_line, 'comparison-flip', f'Flip \`{old_sym}\` to \`{new_sym}\` at {file_path}:{target_line}', res, statement_line):
                return True
    if isinstance(expr, ast.BoolOp):
        cloned = copy.deepcopy(expr)
        if isinstance(expr.op, ast.And):
            cloned.op = ast.Or()
            old_sym, new_sym = 'and', 'or'
        else:
            cloned.op = ast.And()
            old_sym, new_sym = 'or', 'and'
        res = replace_span(expr, ast.unparse(cloned), target_line)
        if emit(target_line, 'boolean-op-flip', f'Flip \`{old_sym}\` to \`{new_sym}\` at {file_path}:{target_line}', res, statement_line):
            return True
    return False

def inspect_cond_tree(test_expr, stmt_line, header_hit):
    sub_exprs = collect_cond_exprs(test_expr)
    matching = []
    for e in sub_exprs:
        hits = node_changed_lines(e)
        if hits:
            span = (getattr(e, 'end_lineno', e.lineno) or e.lineno) - e.lineno
            prio = 0 if isinstance(e, ast.Compare) else 1
            matching.append((span, prio, e.lineno, hits[0], e))
        elif header_hit:
            span = (getattr(e, 'end_lineno', e.lineno) or e.lineno) - e.lineno
            prio = 0 if isinstance(e, ast.Compare) else 1
            matching.append((span + 1000, prio, e.lineno, stmt_line, e))
    matching.sort(key=lambda t: (t[0], t[1], t[2]))
    emitted_any = False
    for _, _, _, target_ln, expr in matching:
        if target_ln in seen_lines:
            continue
        if mutate_cond_expr(expr, target_ln, stmt_line):
            emitted_any = True
    return emitted_any

for node in ast.walk(tree):
    if isinstance(node, (ast.If, ast.While, ast.IfExp)):
        stmt_ln = node.lineno
        header_hit = stmt_ln in changed
        test_hits = node_changed_lines(node.test)
        if not header_hit and not test_hits:
            continue
        if inspect_cond_tree(node.test, stmt_ln, header_hit):
            continue
        target_ln = test_hits[0] if test_hits else stmt_ln
        neg = f'not ({ast.unparse(node.test)})'
        res = replace_span(node.test, neg, target_ln)
        emit(target_ln, 'guard-negate', f'Negate guard condition at {file_path}:{target_ln}', res, stmt_ln)
    elif isinstance(node, ast.Return) and node.value is not None:
        ret_hits = node_changed_lines(node)
        if not ret_hits:
            continue
        stmt_ln = node.lineno
        if inspect_cond_tree(node.value, stmt_ln, stmt_ln in changed):
            continue
        val_hits = node_changed_lines(node.value)
        target_ln = val_hits[0] if val_hits else ret_hits[0]
        if isinstance(node.value, ast.Constant):
            if node.value.value is True:
                emit(target_ln, 'return-flip', f'Flip \`return True\` to \`return False\` at {file_path}:{target_ln}', replace_span(node.value, 'False', target_ln), stmt_ln)
            elif node.value.value is False:
                emit(target_ln, 'return-flip', f'Flip \`return False\` to \`return True\` at {file_path}:{target_ln}', replace_span(node.value, 'True', target_ln), stmt_ln)
            elif node.value.value is None:
                emit(target_ln, 'return-flip', f'Mutate \`return None\` to \`return 0\` at {file_path}:{target_ln}', replace_span(node.value, '0', target_ln), stmt_ln)

candidates.sort(key=lambda c: (c['line'], c['kind']))
print(json.dumps(candidates))
`;

function generatePythonGuardMutations(root, filePath, sourceText, changedLines, env = process.env) {
  const pythonBin = resolvePythonBinary(root);
  const proc = spawnSync(pythonBin, ['-c', PY_AST_MUTATOR_SCRIPT], {
    input: JSON.stringify({ file: filePath, source: sourceText, changedLines }),
    env: { ...scrubChildEnv(env), PYTHONDONTWRITEBYTECODE: '1' },
    encoding: 'utf8',
    timeout: 15_000,
    maxBuffer: 8 * 1024 * 1024,
    stdio: ['pipe', 'pipe', 'pipe'],
  });
  if (proc.status !== 0 || !proc.stdout?.trim()) return [];
  try {
    const parsed = JSON.parse(proc.stdout);
    return Array.isArray(parsed) ? parsed : [];
  } catch {
    return [];
  }
}

function generateGoGuardMutations(filePath, sourceText, changedLines) {
  const src = String(sourceText ?? '');
  const rawLines = src.split('\n');
  const maskedLines = lexCStyleSource(src, { go: true }).codeOnly.split('\n');
  const candidates = [];

  for (const lineNo of changedLines) {
    const idx = lineNo - 1;
    if (idx < 0 || idx >= rawLines.length) continue;
    const rawLine = rawLines[idx];
    const mLine = maskedLines[idx] ?? '';
    if (!mLine.trim()) continue;

    const emit = (kind, description, mutatedLine) => {
      if (mutatedLine === rawLine) return false;
      const next = [...rawLines];
      next[idx] = mutatedLine;
      candidates.push({
        file: filePath,
        line: lineNo,
        kind,
        description,
        original: rawLine.trim(),
        mutated: mutatedLine.trim(),
        mutatedContent: next.join('\n'),
      });
      return true;
    };

    if (/\b(?:if|for|return)\b/.test(mLine)) {
      const comp = findComparisonFlipOnLine(rawLine, mLine);
      if (comp && emit('comparison-flip', `Flip \`${comp.from}\` to \`${comp.to}\` at ${filePath}:${lineNo}`, comp.mutatedLine)) continue;
      const boolOp = findBoolOpFlipOnLine(rawLine, mLine);
      if (boolOp && emit('boolean-op-flip', `Flip \`${boolOp.from}\` to \`${boolOp.to}\` at ${filePath}:${lineNo}`, boolOp.mutatedLine)) continue;
    }
    const ifM = /^(\s*if\s+)([^;{]+)(\s*\{.*)$/.exec(mLine);
    if (ifM && !ifM[2].includes(':=')) {
      const condStart = ifM[1].length;
      const condEnd = condStart + ifM[2].length;
      const origCond = rawLine.slice(condStart, condEnd).trim();
      const mutatedLine = `${rawLine.slice(0, condStart)}!(${origCond})${rawLine.slice(condEnd)}`;
      if (emit('guard-negate', `Negate \`if\` guard condition at ${filePath}:${lineNo}`, mutatedLine)) continue;
    }
    const retBool = /\breturn\s+(true|false)\b/.exec(mLine);
    if (retBool) {
      const flipped = retBool[1] === 'true' ? 'false' : 'true';
      const pos = retBool.index + retBool[0].lastIndexOf(retBool[1]);
      emit('return-flip', `Flip \`return ${retBool[1]}\` to \`return ${flipped}\` at ${filePath}:${lineNo}`, `${rawLine.slice(0, pos)}${flipped}${rawLine.slice(pos + retBool[1].length)}`);
    }
  }
  return candidates;
}

/**
 * Pure deterministic selection of 1..3 guard mutations:
 * prioritizes formal-covered guards, ranks by kind priority, spreads round-robin across distinct files, max 1 per (file, line).
 */
export function selectGuardMutations({ candidates = [], formalCoveredLines = null, maxMutations = 3 } = {}) {
  const limit = clampMaxMutations(maxMutations);
  const hasCoverageMap = formalCoveredLines !== null && formalCoveredLines !== undefined && typeof formalCoveredLines === 'object';
  const covSets = new Map();
  if (hasCoverageMap) {
    for (const [file, lines] of Object.entries(formalCoveredLines)) {
      covSets.set(file, new Set(Array.isArray(lines) ? lines : []));
    }
  }

  const normalized = [];
  const seenFileLine = new Set();
  const sortCmp = (a, b) => (
    (KIND_PRIORITY[a.kind] ?? 9) - (KIND_PRIORITY[b.kind] ?? 9)
    || a.file.localeCompare(b.file)
    || a.line - b.line
  );

  for (const raw of Array.isArray(candidates) ? candidates : []) {
    if (!raw || typeof raw.file !== 'string' || !Number.isInteger(raw.line)) continue;
    const fileCov = covSets.get(raw.file);
    const isCovered = fileCov
      ? (fileCov.has(raw.line) || (Number.isInteger(raw.statementLine) && fileCov.has(raw.statementLine)))
      : false;
    const formalCovered = typeof raw.formalCovered === 'boolean'
      ? raw.formalCovered
      : (hasCoverageMap ? isCovered : true);
    normalized.push({ ...raw, formalCovered });
  }
  normalized.sort(sortCmp);

  const deduped = [];
  for (const item of normalized) {
    const key = `${item.file}:${item.line}`;
    if (seenFileLine.has(key)) continue;
    seenFileLine.add(key);
    deduped.push(item);
  }

  const pickRoundRobin = pool => {
    const byFile = new Map();
    for (const item of pool) {
      let arr = byFile.get(item.file);
      if (!arr) { arr = []; byFile.set(item.file, arr); }
      arr.push(item);
    }
    const fileKeys = [...byFile.keys()].sort();
    const out = [];
    let round = 0;
    while (out.length < limit) {
      let added = false;
      for (const fk of fileKeys) {
        const arr = byFile.get(fk);
        if (round < arr.length) {
          out.push(arr[round]);
          added = true;
          if (out.length >= limit) break;
        }
      }
      if (!added) break;
      round += 1;
    }
    return out;
  };

  const coveredPool = deduped.filter(c => c.formalCovered);
  const uncoveredPool = deduped.filter(c => !c.formalCovered);
  const picked = pickRoundRobin(coveredPool);
  if (picked.length < limit && !hasCoverageMap) {
    for (const item of pickRoundRobin(uncoveredPool)) {
      if (picked.length >= limit) break;
      picked.push(item);
    }
  }
  // If formal coverage map was provided but 0 changed guards were covered by the formal suite at all,
  // still pick up to `limit` uncovered changed guards from formal-bound files so sham imports cannot pass silently.
  if (picked.length === 0 && uncoveredPool.length > 0) {
    for (const item of pickRoundRobin(uncoveredPool)) {
      if (picked.length >= limit) break;
      picked.push(item);
    }
  }

  const selected = picked.map((item, idx) => ({
    id: item.id || `M${idx + 1}`,
    file: item.file,
    line: item.line,
    kind: item.kind,
    description: item.description,
    original: item.original,
    mutated: item.mutated,
    mutatedContent: item.mutatedContent,
    formalCovered: item.formalCovered,
  }));
  return { selected };
}

/**
 * Pure classification and kill-rate aggregation for executed guard mutations.
 */
export function evaluateMutationOutcome({ results = [], formalFiles = [] } = {}) {
  const list = Array.isArray(results) ? results : [];
  const formalLabel = Array.isArray(formalFiles) && formalFiles.length > 0 ? formalFiles.join(', ') : '<formal suite>';

  let killed = 0;
  let survived = 0;
  let syntaxErrors = 0;
  let errorsCount = 0;
  const mutations = [];
  const notProvedReasons = [];

  for (let i = 0; i < list.length; i += 1) {
    const r = list[i];
    const id = r.id || `M${i + 1}`;
    const formalCovered = r.formalCovered !== false;
    let outcome;
    if (r.timedOut === true || r.missingRunner === true || r.executed === false) {
      outcome = 'error';
      errorsCount += 1;
      notProvedReasons.push(`${r.file}:${r.line} [mutation-runner-error] Mutation ${id} (${r.description}) could not be evaluated: ${r.summary || 'runner error or timeout'}.`);
    } else if (r.syntaxOnlyCrash === true) {
      outcome = 'syntax-error';
      syntaxErrors += 1;
    } else if (r.failedOnMutation === true) {
      outcome = 'killed';
      killed += 1;
    } else {
      outcome = 'survived';
      survived += 1;
      if (formalCovered) {
        const detail = formatTeachingDetail({
          invariant: `Formal-covered guard mutation (${r.description}) survived formal suite (${formalLabel}) with 0 assertion failures`,
          fix: `Strengthen the formal test assertions to cover the guard at ${r.file}:${r.line}`,
          rerun: 'pdd prove --mutation-check',
        });
        notProvedReasons.push(`${r.file}:${r.line} [mutation-survived] ${detail}`);
      } else {
        const detail = formatTeachingDetail({
          invariant: `Changed guard mutation (${r.description}) in formal-bound module was not executed or killed by formal suite (${formalLabel})`,
          fix: `Add formal test inputs and assertions exercising ${r.file}:${r.line}`,
          rerun: 'pdd prove --mutation-check',
        });
        notProvedReasons.push(`${r.file}:${r.line} [mutation-uncovered-guard] ${detail}`);
      }
    }

    mutations.push({
      id,
      file: r.file,
      line: r.line,
      kind: r.kind,
      description: r.description,
      original: r.original,
      mutated: r.mutated,
      formalCovered,
      outcome,
      exitCode: r.exitCode ?? null,
      failedFile: r.failedFile ?? null,
      summary: r.summary ?? '',
    });
  }

  const attempted = list.length;
  const effectiveAttempted = killed + survived;
  const killRate = roundPct(killed, effectiveAttempted);

  if (attempted > 0 && effectiveAttempted === 0 && syntaxErrors > 0 && notProvedReasons.length === 0) {
    notProvedReasons.push(`Mutation check produced only syntax/import crashes (${syntaxErrors}/${attempted}) and 0 real assertion evaluations.`);
  }

  let status;
  if (attempted === 0) status = 'not-applicable';
  else if (notProvedReasons.length > 0 || errorsCount > 0) status = 'not-proved';
  else status = 'proved';

  const ok = status === 'proved' || status === 'not-applicable';
  const summary = status === 'not-applicable'
    ? 'Mutation check: not-applicable (0 mutable guards on changed lines)'
    : `Mutation check: ${killed}/${effectiveAttempted} killed (${killRate !== null ? `${killRate.toFixed(1)}%` : 'n/a'})${survived ? `, ${survived} survived` : ''}${syntaxErrors ? `, ${syntaxErrors} syntax ignored` : ''}`;

  return {
    status,
    ok,
    isolated: true,
    workingTreeMutated: false,
    attempted,
    killed,
    survived,
    syntaxErrors,
    errorsCount,
    killRate,
    mutations,
    notProvedReasons,
    summary,
  };
}

export function generateGuardMutations({ root, diffLinesByFile = {}, targetFiles = [], formalCoveredLines = null, maxMutations = 3, env = process.env } = {}) {
  let realRoot;
  try { realRoot = realpathSync(root); } catch { return { candidates: [], selected: [] }; }
  const files = [...new Set((Array.isArray(targetFiles) ? targetFiles : []).filter(isProductionCodeFile))].sort();
  const candidates = [];

  for (const rel of files) {
    const changedLines = Array.isArray(diffLinesByFile?.[rel]) ? diffLinesByFile[rel] : [];
    if (changedLines.length === 0) continue;
    const src = readSafeUtf8(realRoot, rel);
    if (typeof src !== 'string') continue;

    if (PY_FILE_RE.test(rel)) {
      candidates.push(...generatePythonGuardMutations(realRoot, rel, src, changedLines, env));
    } else if (JS_FILE_RE.test(rel)) {
      candidates.push(...generateJsGuardMutations(rel, src, changedLines));
    } else if (GO_FILE_RE.test(rel)) {
      candidates.push(...generateGoGuardMutations(rel, src, changedLines));
    }
  }

  const { selected } = selectGuardMutations({ candidates, formalCoveredLines, maxMutations });
  return { candidates, selected };
}

function copySafeSandbox(realRoot, workDir) {
  mkdirSync(workDir, { mode: 0o700 });
  cpSync(realRoot, workDir, {
    recursive: true,
    dereference: false,
    verbatimSymlinks: true,
    filter: src => {
      const rel = relative(realRoot, src).split(sep).join('/');
      if (rel === '.git' || rel.startsWith('.git/')) return false;
      if (rel === 'node_modules' || rel.startsWith('node_modules/')) return false;
      if (rel === '.venv' || rel.startsWith('.venv/') || rel === 'venv' || rel.startsWith('venv/')) return false;
      const segs = rel.split('/');
      if (segs.some(seg => seg === '__pycache__' || seg === '.pytest_cache' || seg === '.mypy_cache' || seg === '.ruff_cache')) return false;
      if (/\.py[co]$/i.test(rel)) return false;
      return true;
    },
  });
  const nodeModulesSrc = join(realRoot, 'node_modules');
  try {
    const st = lstatSync(nodeModulesSrc);
    if (st.isDirectory() && !st.isSymbolicLink() && !existsSync(join(workDir, 'node_modules'))) {
      symlinkSync(nodeModulesSrc, join(workDir, 'node_modules'), 'dir');
    }
  } catch {}
}

function verifyTargetIsRegularInRoot(realRoot, relPath) {
  if (!canonicalRepoPath(relPath) || !isProductionCodeFile(relPath)) return false;
  const parts = relPath.split('/');
  let cur = realRoot;
  for (let i = 0; i < parts.length; i += 1) {
    cur = join(cur, parts[i]);
    try {
      const st = lstatSync(cur);
      if (st.isSymbolicLink()) return false;
      if (i === parts.length - 1 && !st.isFile()) return false;
    } catch { return false; }
  }
  return true;
}

function classifyMutationRuns(mut, runs, externalSignal = null) {
  const interruptedSig = externalSignal ?? runs.map(detectSignalInterruption).find(Boolean) ?? null;
  if (interruptedSig) {
    return {
      interruptedSig,
      record: {
        ...mut,
        executed: false,
        failedOnMutation: false,
        syntaxOnlyCrash: false,
        timedOut: false,
        missingRunner: false,
        exitCode: null,
        failedFile: null,
        summary: `Formal suite interrupted by signal ${interruptedSig} during mutation check.`,
      },
    };
  }
  const timedOut = runs.some(r => r.timedOut);
  const missingRunner = runs.some(r => r.missingRunner);
  if (timedOut || missingRunner) {
    return {
      interruptedSig: null,
      record: {
        ...mut,
        executed: false,
        failedOnMutation: false,
        syntaxOnlyCrash: false,
        timedOut,
        missingRunner,
        exitCode: null,
        failedFile: null,
        summary: timedOut ? 'Formal suite timed out during mutation check.' : 'Formal runner unavailable during mutation check.',
      },
    };
  }
  const fatalSigRun = runs.find(r => !r.timedOut && r.signal);
  if (fatalSigRun) {
    return {
      interruptedSig: null,
      record: {
        ...mut,
        executed: false,
        failedOnMutation: false,
        syntaxOnlyCrash: false,
        timedOut: false,
        missingRunner: false,
        exitCode: null,
        failedFile: null,
        summary: `Formal suite terminated abnormally by signal ${fatalSigRun.signal} during mutation check.`,
      },
    };
  }
  const realFail = runs.find(r => !r.ok && !r.syntaxOnlyCrash && (r.failed > 0 || (r.exitCode !== null && r.exitCode !== 0)));
  const syntaxOnly = !realFail && runs.some(r => r.syntaxOnlyCrash);
  const firstNonZero = runs.find(r => r.exitCode !== null && r.exitCode !== 0);
  return {
    interruptedSig: null,
    record: {
      ...mut,
      executed: true,
      failedOnMutation: Boolean(realFail && !syntaxOnly),
      syntaxOnlyCrash: syntaxOnly,
      exitCode: (realFail ?? firstNonZero ?? runs[0])?.exitCode ?? 0,
      failedFile: realFail?.file ?? null,
      summary: realFail
        ? `Killed by ${realFail.file} (${realFail.summary}).`
        : (syntaxOnly ? `Syntax-only crash ignored on ${mut.file}:${mut.line}.` : `Survived: formal suite passed on mutated ${mut.file}:${mut.line}.`),
    },
  };
}

function makeSkippedMutationResult(status, summary) {
  return {
    status,
    ok: status === 'not-applicable' || status === 'skipped',
    isolated: true,
    workingTreeMutated: false,
    attempted: 0,
    killed: 0,
    survived: 0,
    syntaxErrors: 0,
    errorsCount: 0,
    killRate: null,
    mutations: [],
    notProvedReasons: [],
    summary,
  };
}

function prepareMutationContext({
  root,
  baseSha,
  touchedFiles = [],
  diffLinesByFile = null,
  formalResult = null,
  baseVerify = null,
}) {
  if (formalResult && !formalResult.applicable) {
    return { earlyResult: makeSkippedMutationResult('not-applicable', 'Mutation check: not-applicable (formal verification not applicable)') };
  }
  if (formalResult && (formalResult.state === 'failed' || (formalResult.errors?.length ?? 0) > 0)) {
    return { earlyResult: makeSkippedMutationResult('skipped', 'Mutation check: skipped (formal suite failed on unmutated code)') };
  }
  if (formalResult && formalResult.tier === 'proved_spec_model') {
    return { earlyResult: makeSkippedMutationResult('skipped', 'Mutation check: skipped (formal suite is not code-bound)') };
  }

  let realRoot;
  try { realRoot = realpathSync(root); } catch {
    return {
      earlyResult: {
        ...makeSkippedMutationResult('unavailable', 'Mutation check: unavailable (root unreadable)'),
        ok: false,
        notProvedReasons: ['Mutation check failed: repository root is unreadable.'],
      },
    };
  }

  const formalCommand = typeof baseVerify?.formalCommand === 'string' && baseVerify.formalCommand.trim() ? baseVerify.formalCommand.trim() : null;
  const scope = discoverFormalScope({ root: realRoot, touchedFiles, formalCommand });
  const formalFiles = Array.isArray(formalResult?.files) && formalResult.files.length > 0
    ? formalResult.files.map(f => f.file).filter(f => f && f !== '<formal_command>')
    : scope.formalFiles;

  if (formalFiles.length === 0 && !formalCommand) {
    return { earlyResult: makeSkippedMutationResult('not-applicable', 'Mutation check: not-applicable (0 formal test files)') };
  }

  const boundModules = new Set();
  for (const fRec of formalResult?.files ?? []) {
    for (const m of fRec.importedProductionModules ?? []) boundModules.add(m);
  }
  const effectiveDiffLines = diffLinesByFile ?? collectDiffLines({ root: realRoot, baseSha, touchedFiles }).diffLinesByFile;
  const touchedProd = Object.keys(effectiveDiffLines).filter(isProductionCodeFile);
  const targetFiles = formalCommand && boundModules.size === 0
    ? touchedProd
    : touchedProd.filter(f => boundModules.size === 0 || boundModules.has(f));

  if (targetFiles.length === 0) {
    return { earlyResult: makeSkippedMutationResult('not-applicable', 'Mutation check: not-applicable (0 touched formal-bound production files)') };
  }

  return { earlyResult: null, realRoot, formalCommand, formalFiles, effectiveDiffLines, targetFiles };
}

function buildFormalCovMap(covSource) {
  if (!covSource || typeof covSource !== 'object') return null;
  const formalCovMap = {};
  for (const [rel, rec] of Object.entries(covSource)) {
    if (Array.isArray(rec?.executedLines)) formalCovMap[rel] = rec.executedLines;
  }
  return formalCovMap;
}

/**
 * Execute opt-in `pdd prove --mutation-check` strictly inside an isolated temp copy outside `root`.
 * NEVER mutates any file inside `root`, even on crash or SIGINT/SIGTERM/SIGHUP.
 */
export function runProveMutationCheck(
  {
    root,
    baseSha,
    touchedFiles = [],
    diffLinesByFile = null,
    formalResult = null,
    formalCoverageFiles = null,
    baseVerify = null,
    maxMutations = 3,
    timeoutMs = 120_000,
    env = process.env,
  } = {},
  ports = {},
) {
  const ctx = prepareMutationContext({ root, baseSha, touchedFiles, diffLinesByFile, formalResult, baseVerify });
  if (ctx.earlyResult) return ctx.earlyResult;
  const { realRoot, formalCommand, formalFiles, effectiveDiffLines, targetFiles } = ctx;

  const covSource = formalCoverageFiles ?? (formalFiles.length > 0 ? collectFormalLineCoverage({ root: realRoot, formalFiles, timeoutMs, env }, ports) : null);
  const { selected } = generateGuardMutations({
    root: realRoot,
    diffLinesByFile: effectiveDiffLines,
    targetFiles,
    formalCoveredLines: buildFormalCovMap(covSource),
    maxMutations,
    env,
  });

  if (selected.length === 0) {
    return makeSkippedMutationResult('not-applicable', 'Mutation check: not-applicable (0 mutable conditional/return guards on changed lines)');
  }

  return withSignalSafeTempDir('pdd-prove-mut-', tempDir => {
    const workDir = join(tempDir, 'work');
    copySafeSandbox(realRoot, workDir);
    const realWork = realpathSync(workDir);
    const runResults = [];

    for (const mut of selected) {
      if (!verifyTargetIsRegularInRoot(realRoot, mut.file)) {
        runResults.push({ ...mut, executed: false, failedOnMutation: false, syntaxOnlyCrash: false, exitCode: null, summary: `Refused unsafe or symlinked mutation target "${mut.file}".` });
        continue;
      }
      const targetFull = join(workDir, mut.file);
      const targetRealDir = realpathSync(dirname(targetFull));
      if (targetRealDir !== realWork && !targetRealDir.startsWith(`${realWork}${sep}`)) {
        runResults.push({ ...mut, executed: false, failedOnMutation: false, syntaxOnlyCrash: false, exitCode: null, summary: `Refused escaping mutation path "${mut.file}".` });
        continue;
      }

      const originalBytes = readFileSync(targetFull);
      let aborted = false;
      try {
        writeFileSync(targetFull, mut.mutatedContent, 'utf8');
        const targets = formalFiles.length > 0 ? formalFiles : [null];
        const runs = [];
        for (const f of targets) {
          const r = runIsolatedFormalFile({ root: workDir, runnerRoot: realRoot, filePath: f, formalCommand, timeoutMs, env }, ports);
          runs.push(r);
          if (detectSignalInterruption(r)) break;
        }
        const classified = classifyMutationRuns(mut, runs);
        runResults.push(classified.record);
        if (classified.interruptedSig) aborted = true;
      } finally {
        writeFileSync(targetFull, originalBytes);
      }
      if (aborted) break;
    }

    return evaluateMutationOutcome({ results: runResults, formalFiles: formalFiles.length > 0 ? formalFiles : ['<formal_command>'] });
  });
}

export async function runProveMutationCheckAsync(
  {
    root,
    baseSha,
    touchedFiles = [],
    diffLinesByFile = null,
    formalResult = null,
    formalCoverageFiles = null,
    baseVerify = null,
    maxMutations = 3,
    timeoutMs = 120_000,
    env = process.env,
  } = {},
  ports = {},
  signalCtrl = null,
) {
  const ctx = prepareMutationContext({ root, baseSha, touchedFiles, diffLinesByFile, formalResult, baseVerify });
  if (ctx.earlyResult) return ctx.earlyResult;
  const { realRoot, formalCommand, formalFiles, effectiveDiffLines, targetFiles } = ctx;

  const covSource = formalCoverageFiles ?? (formalFiles.length > 0 ? await collectFormalLineCoverageAsync({ root: realRoot, formalFiles, timeoutMs, env }, ports, signalCtrl) : null);
  if (signalCtrl?.signal) {
    return {
      ...makeSkippedMutationResult('not-proved', `Mutation check: interrupted by signal ${signalCtrl.signal}`),
      ok: false,
      notProvedReasons: [`Mutation check interrupted by signal ${signalCtrl.signal}.`],
    };
  }

  const { selected } = generateGuardMutations({
    root: realRoot,
    diffLinesByFile: effectiveDiffLines,
    targetFiles,
    formalCoveredLines: buildFormalCovMap(covSource),
    maxMutations,
    env,
  });

  if (selected.length === 0) {
    return makeSkippedMutationResult('not-applicable', 'Mutation check: not-applicable (0 mutable conditional/return guards on changed lines)');
  }

  return withSignalSafeTempDirAsync('pdd-prove-mut-', async (tempDir, ctrl) => {
    const workDir = join(tempDir, 'work');
    copySafeSandbox(realRoot, workDir);
    await new Promise(resolve => setImmediate(resolve));
    const realWork = realpathSync(workDir);
    const runResults = [];

    for (const mut of selected) {
      if (ctrl.signal) break;
      if (!verifyTargetIsRegularInRoot(realRoot, mut.file)) {
        runResults.push({ ...mut, executed: false, failedOnMutation: false, syntaxOnlyCrash: false, exitCode: null, summary: `Refused unsafe or symlinked mutation target "${mut.file}".` });
        continue;
      }
      const targetFull = join(workDir, mut.file);
      const targetRealDir = realpathSync(dirname(targetFull));
      if (targetRealDir !== realWork && !targetRealDir.startsWith(`${realWork}${sep}`)) {
        runResults.push({ ...mut, executed: false, failedOnMutation: false, syntaxOnlyCrash: false, exitCode: null, summary: `Refused escaping mutation path "${mut.file}".` });
        continue;
      }

      const originalBytes = readFileSync(targetFull);
      let aborted = false;
      try {
        writeFileSync(targetFull, mut.mutatedContent, 'utf8');
        const targets = formalFiles.length > 0 ? formalFiles : [null];
        const runs = [];
        for (const f of targets) {
          if (ctrl.signal) break;
          const r = await runIsolatedFormalFileAsync({ root: workDir, runnerRoot: realRoot, filePath: f, formalCommand, timeoutMs, env }, ports, ctrl);
          runs.push(r);
          if (ctrl.signal || detectSignalInterruption(r)) break;
        }
        const classified = classifyMutationRuns(mut, runs, ctrl.signal);
        runResults.push(classified.record);
        if (ctrl.signal || classified.interruptedSig) aborted = true;
      } finally {
        try { writeFileSync(targetFull, originalBytes); } catch {}
      }
      if (aborted) break;
    }

    return evaluateMutationOutcome({ results: runResults, formalFiles: formalFiles.length > 0 ? formalFiles : ['<formal_command>'] });
  }, signalCtrl);
}
