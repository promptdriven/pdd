// Generated from prompts/cli/screen-compare.prompt.md.
// Self-contained browser DOM/SVG snapshot evaluator serialized via snapshot.toString() into CDP Runtime.evaluate.

export function snapshot(reference, scope = globalThis.document, referenceViewport, selected, captureLook = false) {
  const document = scope.ownerDocument || scope, win = document.defaultView;
  const getComputedStyle = element => win.getComputedStyle(element);
  const host = selected?.host, shadow = scope.nodeType === Node.DOCUMENT_FRAGMENT_NODE;
  const hostBox = shadow ? host.getBoundingClientRect() : null;
  const sx = shadow ? hostBox.width / host.offsetWidth : 1, sy = shadow ? hostBox.height / host.offsetHeight : 1;
  const left = shadow ? hostBox.left + host.clientLeft * sx : 0, top = shadow ? hostBox.top + host.clientTop * sy : 0;
  const width = selected?.width || win.innerWidth, height = selected?.height || win.innerHeight;
  const right = left + width * sx, bottom = top + height * sy;
  const normalize = text => text.replace(/\s+/g, ' ').trim();
  const elements = [...scope.querySelectorAll('*')], indexes = new Map(elements.map((el, i) => [el, i])), parts = [];
  const walker = document.createTreeWalker(scope.documentElement || scope, NodeFilter.SHOW_TEXT | NodeFilter.SHOW_CDATA_SECTION), textNodes = [], tokenIds = new Map();
  while (walker.nextNode()) { tokenIds.set(walker.currentNode, `text:${textNodes.length}`); textNodes.push(walker.currentNode); }
  const excluded = el => !!el.closest('title,desc,defs,metadata,script,style,noscript,template,symbol,marker,pattern,clipPath,mask,linearGradient,radialGradient,stop,filter');
  const svgPaint = new Set(['text', 'tspan', 'textPath', 'rect', 'circle', 'ellipse', 'path', 'polygon', 'polyline', 'line']);
  const svgContainer = new Set(['svg', 'g', 'a', 'switch']);
  const transparent = color => color === 'none' || color === 'transparent' || /^rgba\([^,]+,[^,]+,[^,]+,\s*0(?:\.0+)?\s*\)$/.test(color) || /\/\s*0(?:\.0+)?\s*\)$/.test(color);
  const emptyInset = value => {
    const match = /^inset\(([^)]+)\)(?:\s+(?:border|padding|content|margin)-box)?$/.exec(value);
    if (!match) return false;
    const [offsets, ...radii] = match[1].trim().split(/\s+round\s+/);
    if (radii.length > 1 || radii.length === 1 && !radii[0]) return false;
    const tokens = offsets.split(/\s+/);
    if (tokens.length < 1 || tokens.length > 4 || !tokens.every(token => /^(?:\d+(?:\.\d+)?|\.\d+)(?:%|px)$/.test(token))) return false;
    const pct = token => token.endsWith('%') ? Number(token.slice(0, -1)) : 0;
    const [t, r = t, b = t, l = r] = tokens.map(pct);
    return t + b >= 100 || l + r >= 100;
  };
  const emptyRect = value => {
    const match = /^rect\(([^,]+),\s*([^,]+),\s*([^,]+),\s*([^)]+)\)$/.exec(value);
    if (!match) return false;
    const coords = match.slice(1).map(part => {
      const token = part.trim();
      if (token === 'auto') return null;
      return /^[+-]?(?:\d+(?:\.\d+)?|\.\d+)px$/.test(token) ? Number(token.slice(0, -2)) : NaN;
    });
    if (coords.some(Number.isNaN)) return false;
    const [t, r, b, l] = coords;
    return t !== null && b !== null && b <= t || l !== null && r !== null && r <= l;
  };
  const collapsedClip = parent => {
    if (parent.namespaceURI !== 'http://www.w3.org/1999/xhtml' || parent.getRootNode() !== scope) return false;
    const effect = parent.ownerDocument.defaultView.getComputedStyle(parent);
    if (effect.maskImage !== 'none' || effect.filter !== 'none') return false;
    return emptyInset(effect.clipPath) || ['absolute', 'fixed'].includes(effect.position) && emptyRect(effect.clip) && (effect.clipPath === 'none' || emptyInset(effect.clipPath));
  };
  let unsupported;
  const painted = (color, opacity) => {
    if (transparent(color) || Number(opacity) === 0) return false;
    if (!color.startsWith('url(')) return true;
    const fragment = /^url\(["']?#([^"')]+)["']?\)$/.exec(color), paint = fragment && scope.getElementById(fragment[1]);
    if (paint && ['linearGradient', 'radialGradient'].includes(paint.localName)) {
      if (paint.hasAttribute('href') || paint.hasAttribute('xlink:href')) { unsupported = 'Unsupported SVG paint inheritance; visible paint cannot be established.'; return false; }
      return [...paint.querySelectorAll('stop')].some(stop => { const style = getComputedStyle(stop); return !transparent(style.stopColor) && Number(style.stopOpacity) > 0; });
    }
    unsupported = 'Unsupported SVG paint resource; visible paint cannot be established.';
    return false;
  };
  const textPaint = style => {
    if (style.webkitTextSecurity && style.webkitTextSecurity !== 'none' || parseFloat(style.webkitTextStrokeWidth) > 0 || style.textShadow !== 'none') {
      unsupported = 'Unsupported text masking, stroke or shadow; literal visible text cannot be established.';
      return false;
    }
    return !transparent(style.webkitTextFillColor || style.color);
  };
  // Read values only for controls whose value is literally rendered as text.
  const controlValue = el => {
    if (el.localName === 'textarea') return el.value;
    if (el.localName === 'select') return el.selectedOptions[0]?.label || '';
    if (el.localName !== 'input') return '';
    if (['date', 'month', 'week', 'time', 'datetime-local'].includes(el.type)) {
      if (visible(el, el.getBoundingClientRect(), 'surface')) unsupported = 'Unsupported native control formatting; literal visible text cannot be established.';
      return '';
    }
    return ['text', 'search', 'tel', 'url', 'email', 'number', 'button', 'submit', 'reset'].includes(el.type) ? el.value : '';
  };
  const htmlPaint = el => {
    const style = getComputedStyle(el);
    return !transparent(style.backgroundColor) || ['Top', 'Right', 'Bottom', 'Left'].some(side => !['none', 'hidden'].includes(style[`border${side}Style`]) && parseFloat(style[`border${side}Width`]) > 0 && !transparent(style[`border${side}Color`]))
      || !['none', 'hidden'].includes(style.outlineStyle) && parseFloat(style.outlineWidth) > 0 && !transparent(style.outlineColor)
      || ['input', 'textarea', 'select'].includes(el.localName) && (style.appearance !== 'none' || !!controlValue(el) && textPaint(style));
  };
  const visible = (el, box, kind) => {
    const effects = [];
    if (selected && !shadow) for (let outer = host; outer; outer = outer.parentElement) {
      const style = outer.ownerDocument.defaultView.getComputedStyle(outer);
      if (style.display === 'none' || ['hidden', 'collapse'].includes(style.visibility) || Number(style.opacity) === 0 || style.contentVisibility === 'hidden') return false;
      if (style.clipPath !== 'none' || !['auto', 'rect(auto, auto, auto, auto)'].includes(style.clip) || style.maskImage !== 'none' || style.filter !== 'none') effects.push(outer);
    }
    const style = getComputedStyle(el), svg = el.namespaceURI === 'http://www.w3.org/2000/svg';
    const degenerate = svg && svgPaint.has(el.localName) && !(box.width > 0 && box.height > 0);
    // SVG geometric bounds omit the stroke. Probe its possible extent only to
    // decide whether unsupported zero-area geometry needs an explicit error.
    const matrix = degenerate && el.getScreenCTM?.();
    const stroke = degenerate ? parseFloat(style.strokeWidth) * Math.max(1, parseFloat(style.strokeMiterlimit) || 1) : 0;
    const margin = matrix ? stroke * Math.max(1, Math.abs(matrix.a) + Math.abs(matrix.c), Math.abs(matrix.b) + Math.abs(matrix.d)) : stroke;
    const probe = degenerate ? { left: box.left - margin, right: box.right + margin, top: box.top - margin, bottom: box.bottom + margin, width: box.width + 2 * margin, height: box.height + 2 * margin } : box;
    if (!(probe.width > 0 && probe.height > 0 && probe.right > left && probe.bottom > top && probe.left < right && probe.top < bottom)) return false;
    const intersection = { left: Math.max(left, probe.left), top: Math.max(top, probe.top), right: Math.min(right, probe.right), bottom: Math.min(bottom, probe.bottom) };
    for (let parent = el; parent; parent = parent.parentElement || (shadow && parent.getRootNode() === scope ? host : null)) {
      const style = getComputedStyle(parent);
      if (style.display === 'none' || ['hidden', 'collapse'].includes(style.visibility) || Number(style.opacity) === 0 || style.contentVisibility === 'hidden') return false;
      if (style.clipPath !== 'none' || !['auto', 'rect(auto, auto, auto, auto)'].includes(style.clip) || style.maskImage !== 'none' || style.filter !== 'none') effects.push(parent);
      if (parent !== el && (!shadow || parent === host || scope.contains(parent)) && /(hidden|clip|scroll|auto)/.test(`${style.overflowX} ${style.overflowY}`)) {
        const clip = parent.getBoundingClientRect();
        const scaleX = clip.width / (parent.offsetWidth || parent.clientWidth || clip.width), scaleY = clip.height / (parent.offsetHeight || parent.clientHeight || clip.height);
        if (/(hidden|clip|scroll|auto)/.test(style.overflowX)) { intersection.left = Math.max(intersection.left, clip.left + parent.clientLeft * scaleX); intersection.right = Math.min(intersection.right, clip.left + (parent.clientLeft + parent.clientWidth) * scaleX); }
        if (/(hidden|clip|scroll|auto)/.test(style.overflowY)) { intersection.top = Math.max(intersection.top, clip.top + parent.clientTop * scaleY); intersection.bottom = Math.min(intersection.bottom, clip.top + (parent.clientTop + parent.clientHeight) * scaleY); }
        if (intersection.right <= intersection.left || intersection.bottom <= intersection.top) return false;
      }
    }
    if (degenerate && !(parseFloat(style.strokeWidth) > 0 && painted(style.stroke, style.strokeOpacity))) return false;
    if (effects.length) {
      if (!reference && effects.every(collapsedClip)) return false;
      unsupported = 'Unsupported applied clip-path, clip, mask or filter; visible parts cannot be established.';
      return false;
    }
    if ((kind === 'text' || ['text', 'tspan', 'textPath'].includes(el.localName)) && !textPaint(style)) return false;
    if (svg) {
      if (svgPaint.has(el.localName)) {
        const strokePaint = parseFloat(style.strokeWidth) > 0 && painted(style.stroke, style.strokeOpacity);
        if (degenerate) {
          if (strokePaint) unsupported = `Unsupported SVG stroke geometry for ${el.localName}; visible bounds cannot be established.`;
          return false;
        }
        if (!(el.localName !== 'line' && painted(style.fill, style.fillOpacity)) && !strokePaint) return false;
      } else if (svgContainer.has(el.localName)) {
        // A transparent group is a usable region only through its rendered children.
        return [...el.querySelectorAll('*')].some(child => !excluded(child) && visible(child, child.getBoundingClientRect(), child.localName === 'text' ? 'text' : 'id'));
      } else {
        if (painted(style.fill, style.fillOpacity) || parseFloat(style.strokeWidth) > 0 && painted(style.stroke, style.strokeOpacity)) unsupported = `Unsupported SVG element: ${el.localName}; visible paint cannot be established.`;
        return false;
      }
    } else if (kind === 'id') {
      if (htmlPaint(el)) return true;
      const intersects = child => child.right > box.left && child.left < box.right && child.bottom > box.top && child.top < box.bottom;
      for (const node of textNodes) {
        if (!el.contains(node) || !normalize(node.textContent) || excluded(node.parentElement)) continue;
        const range = document.createRange(); range.selectNodeContents(node); const bounds = range.getBoundingClientRect();
        if (intersects(bounds) && visible(node.parentElement, bounds, 'text')) return true;
      }
      for (const child of el.querySelectorAll('*')) {
        if (excluded(child)) continue;
        const bounds = child.getBoundingClientRect();
        if (intersects(bounds) && (child.namespaceURI === 'http://www.w3.org/2000/svg' ? visible(child, bounds, 'id') : htmlPaint(child) && visible(child, bounds, 'surface'))) return true;
      }
      if (style.backgroundImage !== 'none' || style.boxShadow !== 'none' || ['img', 'canvas', 'video'].includes(el.localName)) unsupported = 'Unsupported HTML image or shadow paint; visible parts cannot be established.';
      return false;
    }
    return true;
  };
  const item = (el, kind, value, bounds) => {
    const box = bounds || el.getBoundingClientRect(), ancestors = [];
    for (let parent = el.parentElement; parent; parent = parent.parentElement) ancestors.push(indexes.get(parent));
    const region = el.parentElement?.closest('[id]')?.id || null;
    return { kind, value, node: indexes.get(el), ancestors, region, visible: visible(el, box, kind), box: referenceViewport ? {
        x: (box.x - left) / sx * referenceViewport.width / width,
        y: (box.y - top) / sy * referenceViewport.height / height,
        width: box.width / sx * referenceViewport.width / width,
        height: box.height / sy * referenceViewport.height / height,
      } : { x: box.x, y: box.y, width: box.width, height: box.height },
      tokens: textNodes.filter(node => el.contains(node) && normalize(node.textContent)).map(node => tokenIds.get(node)) };
  };
  const textInfo = new Map(textNodes.map(node => {
    const el = node.parentElement, range = document.createRange(); range.selectNodeContents(node);
    return [node, { value: normalize(node.textContent), box: range.getBoundingClientRect(), visible: !!el && !excluded(el) && !el.closest('textarea,select,option') && !(reference && el.closest('[data-context-only="true"],.context-only')) && visible(el, range.getBoundingClientRect(), 'text') }];
  }));
  const renderedText = node => {
    if (node.nodeType === Node.TEXT_NODE || node.nodeType === Node.CDATA_SECTION_NODE) return textInfo.get(node)?.visible ? node.textContent : '';
    if (node.nodeType !== Node.ELEMENT_NODE || excluded(node) || ['textarea', 'select', 'option'].includes(node.localName)) return '';
    if (node.localName === 'br') return '\n';
    const text = [...node.childNodes].map(renderedText).join('');
    return node.namespaceURI !== 'http://www.w3.org/2000/svg' && /^(block|flex|grid|table|list-item)/.test(getComputedStyle(node).display) ? `\n${text}\n` : text;
  };
  const referenceIds = new Set();
  for (const el of elements) {
    const metadata = excluded(el);
    if (reference && (metadata || el.closest('[data-context-only="true"],.context-only'))) continue;
    // Even an unlabelled painted child can be its enclosing id's only paint.
    if (!metadata && el.namespaceURI === 'http://www.w3.org/2000/svg' && !svgContainer.has(el.localName)) visible(el, el.getBoundingClientRect(), 'id');
    if (el.id) {
      const part = metadata ? { kind: 'id', value: el.id, node: indexes.get(el), visible: false, box: { x: 0, y: 0, width: 0, height: 0 }, ancestors: [], region: null } : item(el, 'id', el.id);
      if (!reference || part.visible) {
        if (reference && referenceIds.has(el.id)) return { error: `Duplicate reference id: ${el.id}.` };
        referenceIds.add(el.id); parts.push(part);
      }
    }
    if (metadata) continue;
    if (reference && el.localName !== 'text') continue;
    const content = textNodes.filter(node => el.contains(node) && textInfo.get(node).value);
    const rendered = content.filter(node => textInfo.get(node).visible);
    const control = ['input', 'textarea', 'select'].includes(el.localName);
    const value = normalize(control ? controlValue(el) : renderedText(el));
    if (!value) continue;
    const boxes = rendered.map(node => textInfo.get(node).box);
    const bounds = boxes.length ? { left: Math.min(...boxes.map(box => box.left)), top: Math.min(...boxes.map(box => box.top)), right: Math.max(...boxes.map(box => box.right)), bottom: Math.max(...boxes.map(box => box.bottom)) } : null;
    if (bounds) Object.assign(bounds, { x: bounds.left, y: bounds.top, width: bounds.right - bounds.left, height: bounds.bottom - bounds.top });
    const part = item(el, 'text', value, control ? undefined : bounds);
    if (control) part.tokens = [`control:${part.node}`];
    else part.tokens = rendered.map(node => tokenIds.get(node));
    if (!reference || part.visible) parts.push(part);
  }
  if (!reference) for (const node of textNodes) {
    const el = node.parentElement, value = normalize(node.textContent);
    if (!value || !el || excluded(el) || el.closest('textarea,select,option')) continue;
    const part = item(el, 'text', value, textInfo.get(node).box);
    part.ancestors = [part.node, ...part.ancestors]; part.node = tokenIds.get(node); part.tokens = [part.node]; part.region = el.closest('[id]')?.id || null;
    parts.push(part);
  }
  if (unsupported) return { error: unsupported };
  const filteredParts = parts.filter(part => reference || part.kind !== 'text' || !parts.some(other => other !== part && other.kind === 'text' && other.value === part.value && (!part.visible || other.visible) && other.ancestors.includes(part.node)));
  if (!captureLook) return { parts: filteredParts };
  const probeVisible = (el, box, kind) => {
    const saved = unsupported;
    const ok = visible(el, box, kind);
    unsupported = saved;
    return ok;
  };
  const scaleBox = box => referenceViewport ? {
    x: (box.x - left) / sx * referenceViewport.width / width,
    y: (box.y - top) / sy * referenceViewport.height / height,
    width: box.width / sx * referenceViewport.width / width,
    height: box.height / sy * referenceViewport.height / height,
  } : { x: box.x, y: box.y, width: box.width, height: box.height };
  const parseRgb = (color, opacity = 1) => {
    if (!color || transparent(color) || !(Number(opacity) > 0)) return null;
    if (color.startsWith('url(')) {
      const fragment = /^url\(["']?#([^"')]+)["']?\)$/.exec(color), paint = fragment && scope.getElementById(fragment[1]);
      if (paint && ['linearGradient', 'radialGradient'].includes(paint.localName)) {
        for (const stop of paint.querySelectorAll('stop')) {
          const st = getComputedStyle(stop), rgb = parseRgb(st.stopColor, st.stopOpacity);
          if (rgb) return rgb;
        }
      }
      return null;
    }
    const match = /^rgba?\(\s*([\d.]+)[\s,]+([\d.]+)[\s,]+([\d.]+)(?:[\s,/]+([\d.]+))?\s*\)$/i.exec(color);
    if (!match) return null;
    const alpha = (match[4] === undefined ? 1 : Number(match[4])) * Number(opacity);
    return alpha > 0 ? [Math.round(Number(match[1])), Math.round(Number(match[2])), Math.round(Number(match[3]))] : null;
  };
  const rgbDist = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);
  const vw = referenceViewport ? referenceViewport.width : width, vh = referenceViewport ? referenceViewport.height : height;
  const shapeTag = el => svgPaint.has(el.localName) && !['text', 'tspan', 'textPath', 'line'].includes(el.localName);
  let canvasColor = null;
  const lookBoxes = [];
  if (reference) {
    const rootSvg = scope.querySelector('svg');
    if (rootSvg) {
      const rootStyle = getComputedStyle(rootSvg);
      canvasColor = parseRgb(rootStyle.backgroundColor, rootStyle.opacity);
    }
    for (const el of elements) {
      if (excluded(el) || el.closest('[data-context-only="true"],.context-only') || !shapeTag(el)) continue;
      const raw = el.getBoundingClientRect();
      if (!probeVisible(el, raw, 'id')) continue;
      const b = scaleBox(raw);
      if (b.width >= 0.85 * vw && b.height >= 0.85 * vh) {
        const st = getComputedStyle(el), fill = parseRgb(st.fill, st.fillOpacity);
        if (fill) { canvasColor = fill; break; }
      }
    }
    for (const part of parts) {
      if (part.kind !== 'id' || !part.visible) continue;
      const el = elements[part.node], b = part.box;
      if (!el || b.width < 24 || b.height < 16 || (b.width >= 0.85 * vw && b.height >= 0.85 * vh)) continue;
      const shape = shapeTag(el) ? el : svgContainer.has(el.localName) ? [...el.querySelectorAll('*')].find(child => !excluded(child) && !child.closest('[data-context-only="true"],.context-only') && shapeTag(child) && probeVisible(child, child.getBoundingClientRect(), 'id') && scaleBox(child.getBoundingClientRect()).width >= 0.7 * b.width && scaleBox(child.getBoundingClientRect()).height >= 0.7 * b.height) : null;
      if (!shape) continue;
      const st = getComputedStyle(shape), fill = parseRgb(st.fill, st.fillOpacity), stroke = parseFloat(st.strokeWidth) > 0 ? parseRgb(st.stroke, st.strokeOpacity) : null;
      if ((fill && (!canvasColor || rgbDist(fill, canvasColor) > 12)) || stroke !== null) lookBoxes.push({ id: part.value, box: b, fill, stroke });
    }
  } else {
    let bg = null;
    for (const rootEl of shadow ? [host] : [scope.documentElement, scope.body].filter(Boolean)) {
      const st = getComputedStyle(rootEl), c = parseRgb(st.backgroundColor, st.opacity);
      if (c) bg = c;
    }
    const container = shadow ? scope : (scope.body || scope.documentElement);
    const topChildren = container ? [...container.children].filter(child => !excluded(child) && probeVisible(child, child.getBoundingClientRect(), 'surface')) : [];
    if (topChildren.length === 1) {
      const mainEl = topChildren[0], mb = scaleBox(mainEl.getBoundingClientRect()), mst = getComputedStyle(mainEl);
      if (mainEl.namespaceURI === 'http://www.w3.org/2000/svg' && mb.width >= 0.85 * vw && mb.height >= 0.85 * vh) {
        const mc = parseRgb(mst.backgroundColor, mst.opacity);
        if (mc) bg = mc;
        const backdrop = [...mainEl.querySelectorAll('*')].find(child => !excluded(child) && shapeTag(child) && probeVisible(child, child.getBoundingClientRect(), 'id') && scaleBox(child.getBoundingClientRect()).width >= 0.85 * vw && scaleBox(child.getBoundingClientRect()).height >= 0.85 * vh);
        if (backdrop) {
          const bst = getComputedStyle(backdrop), bf = parseRgb(bst.fill, bst.fillOpacity);
          if (bf) bg = bf;
        }
      } else if (mb.width >= 0.85 * vw && mb.height >= 0.85 * vh) {
        const mc = parseRgb(mst.backgroundColor, mst.opacity);
        if (mc) bg = mc;
      }
    }
    canvasColor = bg || [255, 255, 255];
    const surfacePaint = target => {
      if (target.namespaceURI === 'http://www.w3.org/2000/svg') {
        const tb = scaleBox(target.getBoundingClientRect());
        const shape = shapeTag(target) ? target : svgContainer.has(target.localName) ? [...target.querySelectorAll('*')].find(child => !excluded(child) && shapeTag(child) && probeVisible(child, child.getBoundingClientRect(), 'id') && scaleBox(child.getBoundingClientRect()).width >= 0.7 * tb.width && scaleBox(child.getBoundingClientRect()).height >= 0.7 * tb.height) : null;
        if (!shape) return { fill: null, stroke: null, painted: false };
        const st = getComputedStyle(shape), fill = parseRgb(st.fill, st.fillOpacity), stroke = parseFloat(st.strokeWidth) > 0 ? parseRgb(st.stroke, st.strokeOpacity) : null;
        return { fill, stroke, painted: Boolean((fill && rgbDist(fill, canvasColor) > 12) || stroke !== null) };
      }
      const st = getComputedStyle(target), fill = parseRgb(st.backgroundColor, st.opacity);
      let stroke = null;
      for (const side of ['Top', 'Right', 'Bottom', 'Left']) {
        if (!['none', 'hidden'].includes(st[`border${side}Style`]) && parseFloat(st[`border${side}Width`]) > 0) {
          const bc = parseRgb(st[`border${side}Color`], st.opacity);
          if (bc) { stroke = bc; break; }
        }
      }
      if (!stroke && !['none', 'hidden'].includes(st.outlineStyle) && parseFloat(st.outlineWidth) > 0) stroke = parseRgb(st.outlineColor, st.opacity);
      return { fill, stroke, painted: Boolean((fill && rgbDist(fill, canvasColor) > 12) || stroke !== null) };
    };
    for (const part of parts) {
      if (part.kind !== 'id') continue;
      const el = elements[part.node];
      if (!el || !part.visible) {
        lookBoxes.push({ id: part.value, visible: Boolean(part.visible), painted: false, box: part.box, fill: null, stroke: null });
        continue;
      }
      let own = surfacePaint(el);
      if (!own.painted && own.fill === null && own.stroke === null) {
        const visChildren = [...el.children].filter(child => !excluded(child) && probeVisible(child, child.getBoundingClientRect(), 'surface'));
        if (visChildren.length === 1) {
          const cb = scaleBox(visChildren[0].getBoundingClientRect());
          if (cb.width >= 0.8 * part.box.width && cb.height >= 0.8 * part.box.height) own = surfacePaint(visChildren[0]);
        }
      }
      lookBoxes.push({ id: part.value, visible: true, painted: own.painted, box: part.box, fill: own.fill, stroke: own.stroke });
    }
  }
  return {
    parts: filteredParts,
    look: { canvasColor, boxes: lookBoxes },
  };
}
