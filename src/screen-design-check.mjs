// Generated from prompts/cli/screen-design-check.prompt.md (sha256: e079c38dc45c2fb401d18cdf19a0789388d7d20894d54cf49f8c824d1ef665ce).

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
    if (ref.fill !== null && (reference.canvasColor === null || rgbDistance(ref.fill, reference.canvasColor) > 12)) {
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
