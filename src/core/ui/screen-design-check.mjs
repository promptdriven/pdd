// Generated from prompts/cli/screen-design-check.prompt.md.

const escaped = text => text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
const hex = ([r, g, b]) => `#${[r, g, b].map(channel => Math.round(channel).toString(16).padStart(2, '0')).join('')}`;
const rgbDistance = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);

function cssClasses(content) {
  const stripped = content
    .replace(/"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\/\*[\s\S]*?\*\//g, ' ')
    .replace(/\{[^{}]*\}/g, ' ');
  return [...new Set([...stripped.matchAll(/\.([A-Za-z_-][A-Za-z0-9_-]*)/g)].map(match => match[1]))].sort();
}

export function lintScreenDesign({ appMaps, stylesheets, prompts }) {
  const byPrompt = new Map(prompts.map(prompt => [prompt.path, prompt]));
  const bySheet = new Map(stylesheets.map(sheet => [sheet.path, sheet]));
  const warnings = [];
  for (const appMap of appMaps) {
    for (const screen of appMap.screens) {
      if (screen.source !== 'operation' || screen.format !== 'html') continue;
      const prompt = byPrompt.get(screen.prompt_path);
      if (!prompt || !prompt.drawings.length) continue;
      const firstDrawing = [...prompt.drawings].sort()[0];
      const effectiveStylesheets = [...new Set([...appMap.stylesheets, ...screen.stylesheets])];
      if (!effectiveStylesheets.length) {
        warnings.push(`Warning: SVG layout ${appMap.path} -> ${prompt.path}: stylesheets: HTML screen "${screen.id}" links ${firstDrawing} with no stylesheet in "stylesheets".`);
        continue;
      }
      let readable = true;
      const resolvedSheets = [];
      for (const cssPath of effectiveStylesheets) {
        const sheet = bySheet.get(cssPath);
        if (!sheet || sheet.error !== null || sheet.content === null) {
          readable = false;
          warnings.push(`Warning: SVG layout ${appMap.path} -> ${cssPath}: stylesheet: ${sheet?.error || 'stylesheet is missing or unreadable'}.`);
        } else {
          resolvedSheets.push({ path: cssPath, classes: cssClasses(sheet.content) });
        }
      }
      if (!readable) continue;
      const firstSheet = resolvedSheets.find(sheet => sheet.classes.length > 0);
      if (!firstSheet) continue;
      const allClasses = [...new Set(resolvedSheets.flatMap(sheet => sheet.classes))];
      const inlineStyled = /\bstyle\s*=|<\s*style\b/i.test(prompt.prose);
      const named = inlineStyled || allClasses.some(name => new RegExp(`(?<![A-Za-z0-9_-])\\.?${escaped(name)}(?![A-Za-z0-9_-])`).test(prompt.prose));
      if (!named) {
        warnings.push(`Warning: SVG layout ${prompt.path} -> ${firstSheet.path}: stylesheet classes: HTML screen "${screen.id}" links ${firstDrawing} and names no CSS class from its stylesheet (for example .${firstSheet.classes[0]}).`);
      }
    }
  }
  return { warnings: [...new Set(warnings)].sort() };
}

const ACTIVE_STATE_VALUE_RE = /^(?:active|selected|current|checked|pressed|on)$/i;
const ACTIVE_CLASS_TOKEN_RE = /^(?:is-)?(?:active|selected|current)$/i;
const ACTIVE_PSEUDO_RE = /^:?(?:active|selected|current|checked|pressed)$/i;

function isTruthyAttr(value) {
  return value === true || (typeof value === 'string' && value.trim().toLowerCase() === 'true');
}

function isAriaCurrentActive(value) {
  if (value === true) return true;
  if (typeof value !== 'string') return false;
  const norm = value.trim().toLowerCase();
  return norm.length > 0 && norm !== 'false';
}

function isActiveInteractiveState(hit) {
  if (!hit || typeof hit !== 'object') return false;
  if (hit.activeState === true || hit.active === true || hit.selected === true || hit.interactiveState === true) return true;
  if (typeof hit.state === 'string' && ACTIVE_STATE_VALUE_RE.test(hit.state.trim())) return true;
  const attrs = hit.attributes && typeof hit.attributes === 'object'
    ? hit.attributes
    : (hit.attrs && typeof hit.attrs === 'object' ? hit.attrs : null);
  for (const bag of [hit, attrs]) {
    if (!bag) continue;
    if (isAriaCurrentActive(bag['aria-current']) || isAriaCurrentActive(bag.ariaCurrent)) return true;
    if (isTruthyAttr(bag['aria-selected']) || isTruthyAttr(bag.ariaSelected)) return true;
    if (isTruthyAttr(bag['aria-pressed']) || isTruthyAttr(bag.ariaPressed)) return true;
    if (isTruthyAttr(bag['aria-checked']) || isTruthyAttr(bag.ariaChecked)) return true;
    if (isTruthyAttr(bag['data-active']) || isTruthyAttr(bag.dataActive)) return true;
    if (isTruthyAttr(bag['data-selected']) || isTruthyAttr(bag.dataSelected)) return true;
    const dataState = bag['data-state'] ?? bag.dataState;
    if (typeof dataState === 'string' && ACTIVE_STATE_VALUE_RE.test(dataState.trim())) return true;
  }
  const pseudoList = Array.isArray(hit.pseudoStates) ? hit.pseudoStates : (Array.isArray(hit.states) ? hit.states : []);
  if (pseudoList.some(item => typeof item === 'string' && ACTIVE_PSEUDO_RE.test(item.trim()))) return true;
  const rawClasses = Array.isArray(hit.classes)
    ? hit.classes
    : Array.isArray(hit.classList)
      ? hit.classList
      : typeof hit.className === 'string'
        ? hit.className.split(/\s+/)
        : typeof hit.class === 'string'
          ? hit.class.split(/\s+/)
          : [];
  if (rawClasses.some(tok => typeof tok === 'string' && ACTIVE_CLASS_TOKEN_RE.test(tok.trim()))) return true;
  return false;
}

export function evaluateScreenLook({ viewport, reference, actual }) {
  void viewport;
  const rows = [];
  if (reference.canvasColor !== null) {
    const expected = `canvas ${hex(reference.canvasColor)}`;
    const pass = actual.canvasColor !== null && rgbDistance(reference.canvasColor, actual.canvasColor) <= 80;
    rows.push({
      part: 'canvas',
      kind: 'look',
      expected,
      actual: actual.canvasColor ? `canvas ${hex(actual.canvasColor)}` : 'absent',
      status: pass ? 'pass' : 'look',
    });
  }
  for (let index = 0; index < reference.boxes.length; index++) {
    const ref = reference.boxes[index];
    let spacing = null;
    for (const prev of reference.boxes.slice(0, index)) {
      const overlapX = Math.min(ref.box.x + ref.box.width, prev.box.x + prev.box.width) - Math.max(ref.box.x, prev.box.x);
      const gapY = ref.box.y - (prev.box.y + prev.box.height);
      if (overlapX > 0 && gapY >= 6 && (spacing === null || gapY < spacing.gap)) spacing = { axis: 'y', prevId: prev.id, gap: gapY };
    }
    if (spacing === null) {
      for (const prev of reference.boxes.slice(0, index)) {
        const overlapY = Math.min(ref.box.y + ref.box.height, prev.box.y + prev.box.height) - Math.max(ref.box.y, prev.box.y);
        const gapX = ref.box.x - (prev.box.x + prev.box.width);
        if (overlapY > 0 && gapX >= 6 && (spacing === null || gapX < spacing.gap)) spacing = { axis: 'x', prevId: prev.id, gap: gapX };
      }
    }
    const expected = `painted ${Math.round(ref.box.width)}×${Math.round(ref.box.height)}${ref.fill ? ` ${hex(ref.fill)}` : ''}${spacing ? `, gap ${Math.round(spacing.gap)}px` : ''}`;
    const hits = actual.boxes.filter(box => box.id === ref.id);
    if (hits.length === 0) {
      rows.push({ part: `#${ref.id} look`, kind: 'look', expected, actual: 'absent', status: 'look' });
      continue;
    }
    if (hits.length > 1) {
      rows.push({ part: `#${ref.id} look`, kind: 'look', expected, actual: 'duplicate id', status: 'look' });
      continue;
    }
    const hit = hits[0];
    if (!hit.visible) {
      rows.push({ part: `#${ref.id} look`, kind: 'look', expected, actual: 'hidden/outside', status: 'look' });
      continue;
    }
    const failures = [];
    if (!hit.painted) failures.push('unpainted box');
    const activeInteractive = Boolean(hit.painted) && isActiveInteractiveState(hit);
    if (!activeInteractive && ref.fill !== null && (reference.canvasColor === null || rgbDistance(ref.fill, reference.canvasColor) > 12)) {
      if (hit.fill !== null && rgbDistance(ref.fill, hit.fill) > 90) failures.push(`color ${hex(hit.fill)}`);
      else if (hit.fill === null && ref.stroke === null && (reference.canvasColor === null || rgbDistance(ref.fill, reference.canvasColor) > 40)) failures.push('missing fill');
    }
    const minW = Math.max(12, ref.box.width * 0.5 - 12), maxW = ref.box.width * 1.8 + 24;
    const minH = Math.max(12, ref.box.height * 0.5 - 12), maxH = ref.box.height * 1.8 + 24;
    if (hit.box.width < minW || hit.box.width > maxW || hit.box.height < minH || hit.box.height > maxH) {
      failures.push(`size ${Math.round(hit.box.width)}×${Math.round(hit.box.height)}`);
    }
    let actualGap;
    if (spacing !== null) {
      const prevHits = actual.boxes.filter(box => box.id === spacing.prevId);
      if (prevHits.length === 1 && prevHits[0].visible) {
        const prevHit = prevHits[0];
        actualGap = spacing.axis === 'y' ? hit.box.y - (prevHit.box.y + prevHit.box.height) : hit.box.x - (prevHit.box.x + prevHit.box.width);
        if (actualGap < Math.min(2, spacing.gap * 0.25) || actualGap > Math.max(spacing.gap * 3 + 24, 48)) {
          failures.push(`gap ${Math.round(actualGap)}px`);
        }
      }
    }
    rows.push({
      part: `#${ref.id} look`,
      kind: 'look',
      expected,
      actual: failures.length ? failures.join('; ') : `painted ${Math.round(hit.box.width)}×${Math.round(hit.box.height)}${hit.fill ? ` ${hex(hit.fill)}` : ''}${actualGap !== undefined ? `, gap ${Math.round(actualGap)}px` : ''}`,
      status: failures.length ? 'look' : 'pass',
    });
  }
  return { rows, passed: rows.every(row => row.status === 'pass') };
}
