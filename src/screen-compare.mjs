// Generated from prompts/cli/screen-compare.prompt.md (sha256: 5f7b0e511a246cb4678c9553d66ed893c3e1c19cf6d967bf7fc5395400dc1ada).
import { spawn } from 'node:child_process';
import { accessSync, constants, lstatSync, mkdtempSync, readFileSync } from 'node:fs';
import { rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { delimiter, join, resolve } from 'node:path';

const failure = (message, exitCode = 2) => Object.assign(new Error(message), { exitCode });
const normalize = text => text.replace(/\s+/g, ' ').trim();
function executable(explicit, env) {
  const chosen = explicit || env.PDD_CHROME_PATH;
  const candidates = chosen ? [chosen] : [
    ...['google-chrome', 'google-chrome-stable', 'chromium', 'chromium-browser'].flatMap(name => (env.PATH || '').split(delimiter).map(dir => join(dir, name))),
    '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
  ];
  for (const path of candidates) { try { accessSync(path, constants.X_OK); if (lstatSync(path).isFile() || lstatSync(path).isSymbolicLink()) return path; } catch { /* next installed browser */ } }
  throw failure('No installed Chrome/Chromium executable found. Set PDD_CHROME_PATH to its executable path.', 5);
}

// CDP's local pipe requires no package, TCP listener or downloaded browser.
async function browserRun({ source, url, chromePath, env }) {
  const profile = mkdtempSync(join(tmpdir(), 'pdd-screen-'));
  let child, session, timeout, closed = false, serial = 0, pending = new Map(), events = new Map(), documentStatus = 0;
  const stop = error => { for (const { reject, timer } of pending.values()) { clearTimeout(timer); reject(error); } pending.clear(); };
  const send = (method, params = {}, sessionId = session) => new Promise((resolve, reject) => {
    if (closed) { reject(failure('Chrome closed unexpectedly.', 5)); return; }
    const id = ++serial, timer = setTimeout(() => { pending.delete(id); reject(failure(`Chrome timed out during ${method}.`, 5)); }, 20_000);
    pending.set(id, { resolve, reject, timer });
    child.stdio[3].write(`${JSON.stringify({ id, method, params, ...(sessionId ? { sessionId } : {}) })}\0`, error => {
      if (error) { clearTimeout(timer); pending.delete(id); reject(failure('Chrome command pipe failed.', 5)); }
    });
  });
  const evaluate = async expression => {
    const reply = await send('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true });
    if (reply.exceptionDetails) throw failure(reply.exceptionDetails.exception?.description || reply.exceptionDetails.text, 5);
    return reply.result?.value;
  };
  try {
    child = spawn(executable(chromePath, env), ['--headless=new', '--no-sandbox', '--disable-gpu', '--disable-dev-shm-usage', '--no-first-run', '--no-default-browser-check', '--disable-background-networking', '--disable-extensions', '--remote-debugging-pipe', `--user-data-dir=${profile}`, 'about:blank'], { env, detached: process.platform !== 'win32', stdio: ['ignore', 'ignore', 'pipe', 'pipe', 'pipe'] });
    child.on('error', error => { closed = true; stop(failure(`Chrome could not start: ${error.message}`, 5)); });
    child.on('exit', () => { closed = true; stop(failure('Chrome closed before the comparison finished.', 5)); });
    child.stderr.resume();
    let buffer = '';
    child.stdio[4].on('data', bytes => {
      buffer += bytes.toString();
      let end;
      while ((end = buffer.indexOf('\0')) >= 0) {
        const message = buffer.slice(0, end); buffer = buffer.slice(end + 1);
        let reply; try { reply = JSON.parse(message); } catch { continue; }
        if (reply.method === 'Network.responseReceived' && reply.params?.type === 'Document') documentStatus = reply.params.response.status;
        if (events.has(reply.method)) events.get(reply.method)(reply.params);
        const request = pending.get(reply.id);
        if (!request) continue;
        pending.delete(reply.id); clearTimeout(request.timer);
        if (reply.error) request.reject(failure(`Chrome: ${reply.error.message}`, 5)); else request.resolve(reply.result);
      }
    });
    timeout = setTimeout(() => { stop(failure('Screen comparison exceeded its 60 second browser limit.', 5)); child.kill('SIGKILL'); }, 60_000);
    const target = await send('Target.createTarget', { url: 'about:blank' }, null);
    session = (await send('Target.attachToTarget', { targetId: target.targetId, flatten: true }, null)).sessionId;
    await send('Page.enable'); await send('Runtime.enable'); await send('Network.enable');
    const reference = await evaluate(`(${prepareReference.toString()})(${JSON.stringify(source)})`);
    if (reference.error) throw failure(reference.error);
    const viewport = reference.viewport;
    await send('Emulation.setDeviceMetricsOverride', { width: Math.ceil(viewport.width), height: Math.ceil(viewport.height), deviceScaleFactor: 1, mobile: false });
    await evaluate('document.fonts.ready');
    const expected = await evaluate(`(${snapshot.toString()})(true)`);
    if (expected.error) throw failure(expected.error);
    if (!expected.parts.length) throw failure('The SVG drawing has no visible required ids or text.');
    const load = new Promise(done => { events.set('Page.loadEventFired', done); });
    const navigation = await send('Page.navigate', { url });
    if (navigation.errorText || navigation.isDownload) throw failure(`Page navigation failed: ${navigation.errorText || 'URL is a download'}`, 5);
    let loadTimer;
    try { await Promise.race([load, new Promise((_, reject) => { loadTimer = setTimeout(() => reject(failure('Page load timed out.', 5)), 15000); })]); }
    finally { clearTimeout(loadTimer); events.delete('Page.loadEventFired'); }
    if (documentStatus >= 400) throw failure(`Page navigation failed: HTTP ${documentStatus}.`, 5);
    await evaluate(`new Promise((resolve, reject) => {
      const deadline = setTimeout(() => reject(Error('Page load timed out')), 15000);
      const ready = async () => { try { await document.fonts.ready; await new Promise(r => requestAnimationFrame(() => requestAnimationFrame(r))); clearTimeout(deadline); resolve(true); } catch (error) { reject(error); } };
      if (document.readyState === 'complete') ready(); else addEventListener('load', ready, {once:true});
    })`);
    const actual = await evaluate(`(${snapshot.toString()})(false)`);
    if (!actual || actual.error) throw failure(actual?.error || 'Could not inspect the page.', 5);
    return { viewport, reference: expected.parts, actual: actual.parts };
  } finally {
    clearTimeout(timeout);
    if (child && !closed) { try { await send('Browser.close', {}, null); } catch { /* already exited or failed */ } }
    closed = true; stop(failure('Comparison finished.', 5));
    if (child && child.exitCode === null && child.signalCode === null) {
      const exited = new Promise(done => child.once('exit', done)); child.kill('SIGKILL');
      await Promise.race([exited, new Promise(done => { const timer = setTimeout(done, 2000); timer.unref(); })]);
    }
    // Chrome subprocesses can briefly outlive the browser parent. End this
    // isolated process group before deleting the profile they may still write.
    if (child?.pid && process.platform !== 'win32') { try { process.kill(-child.pid, 'SIGKILL'); } catch { /* group has exited */ } }
    await rm(profile, { recursive: true, force: true, maxRetries: 5, retryDelay: 100 });
  }
}

// Runs in an initially blank browser document. Parse first, reject executable or
// external content, then render under a CSP. DOMParser never executes the SVG.
function prepareReference(source) {
  const doc = new DOMParser().parseFromString(source, 'image/svg+xml'), svg = doc.documentElement;
  if (doc.querySelector('parsererror') || svg.localName !== 'svg' || svg.namespaceURI !== 'http://www.w3.org/2000/svg') return { error: 'Malformed SVG drawing.' };
  if (doc.doctype || [...doc.childNodes].some(node => node.nodeType === 7)) return { error: 'Unsafe SVG document declarations.' };
  for (const element of doc.querySelectorAll('*')) {
    if (['script', 'foreignObject', 'iframe', 'object', 'embed', 'image', 'use', 'animate', 'animateMotion', 'animateTransform', 'set'].includes(element.localName)) return { error: `Unsafe or unsupported SVG element: ${element.localName}.` };
    for (const attr of element.attributes) {
      if (/^on/i.test(attr.name) || /^(?:href|src)$/i.test(attr.localName) && !attr.value.startsWith('#')) return { error: 'Executable or external SVG resources are not allowed.' };
    }
    const css = `${[...element.attributes].map(attr => attr.value).join(' ')} ${element.localName === 'style' ? element.textContent : ''}`;
    const withoutLocalUrls = css.replace(/url\(\s*(['"]?)#[^)'"\s]+\1\s*\)/gi, '');
    if (/\\|@import|@font-face|url\s*\(/i.test(withoutLocalUrls)) return { error: 'External or unsupported SVG CSS resources are not allowed.' };
  }
  let width, height;
  if (svg.hasAttribute('viewBox')) {
    const values = svg.getAttribute('viewBox').trim().split(/[\s,]+/).map(Number);
    if (values.length !== 4 || !values.every(Number.isFinite)) return { error: 'Invalid SVG viewBox.' };
    [, , width, height] = values;
  } else {
    const dimension = name => { const value = (svg.getAttribute(name) || '').trim(); return /^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?(?:px)?$/i.test(value) ? parseFloat(value) : NaN; };
    width = dimension('width'); height = dimension('height');
  }
  if (!(Number.isFinite(width) && Number.isFinite(height) && width > 0 && height > 0)) return { error: 'SVG needs a positive viewBox or numeric width/height viewport.' };
  document.head.innerHTML = '<meta http-equiv="Content-Security-Policy" content="default-src \'none\'; style-src \'unsafe-inline\'">';
  document.body.style.cssText = 'margin:0;padding:0;overflow:hidden';
  svg.setAttribute('width', width); svg.setAttribute('height', height);
  svg.style.width = `${width}px`; svg.style.height = `${height}px`; svg.style.display = 'block';
  document.body.append(document.importNode(svg, true));
  return { viewport: { width, height } };
}

function snapshot(reference) {
  const normalize = text => text.replace(/\s+/g, ' ').trim();
  const elements = [...document.querySelectorAll('*')], indexes = new Map(elements.map((el, i) => [el, i])), parts = [];
  const walker = document.createTreeWalker(document.documentElement, NodeFilter.SHOW_TEXT), textNodes = [], tokenIds = new Map();
  while (walker.nextNode()) { tokenIds.set(walker.currentNode, `text:${textNodes.length}`); textNodes.push(walker.currentNode); }
  const excluded = el => !!el.closest('title,desc,defs,metadata,script,style,noscript,template');
  const transparent = color => color === 'none' || color === 'transparent' || /^rgba\([^,]+,[^,]+,[^,]+,\s*0(?:\.0+)?\s*\)$/.test(color) || /\/\s*0(?:\.0+)?\s*\)$/.test(color);
  let unsupported;
  const painted = (color, opacity) => {
    if (transparent(color) || Number(opacity) === 0) return false;
    if (!color.startsWith('url(')) return true;
    const fragment = /^url\(["']?#([^"')]+)["']?\)$/.exec(color), paint = fragment && document.getElementById(fragment[1]);
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
    if (!(box.width > 0 && box.height > 0 && box.right > 0 && box.bottom > 0 && box.left < innerWidth && box.top < innerHeight)) return false;
    const intersection = { left: Math.max(0, box.left), top: Math.max(0, box.top), right: Math.min(innerWidth, box.right), bottom: Math.min(innerHeight, box.bottom) }, effects = [];
    for (let parent = el; parent; parent = parent.parentElement) {
      const style = getComputedStyle(parent);
      if (style.display === 'none' || ['hidden', 'collapse'].includes(style.visibility) || Number(style.opacity) === 0 || style.contentVisibility === 'hidden') return false;
      if (style.clipPath !== 'none' || !['auto', 'rect(auto, auto, auto, auto)'].includes(style.clip) || style.maskImage !== 'none' || style.filter !== 'none') effects.push(parent);
      if (parent !== el && /(hidden|clip|scroll|auto)/.test(`${style.overflowX} ${style.overflowY}`)) {
        const clip = parent.getBoundingClientRect();
        if (/(hidden|clip|scroll|auto)/.test(style.overflowX)) { intersection.left = Math.max(intersection.left, clip.left + parent.clientLeft); intersection.right = Math.min(intersection.right, clip.left + parent.clientLeft + parent.clientWidth); }
        if (/(hidden|clip|scroll|auto)/.test(style.overflowY)) { intersection.top = Math.max(intersection.top, clip.top + parent.clientTop); intersection.bottom = Math.min(intersection.bottom, clip.top + parent.clientTop + parent.clientHeight); }
        if (intersection.right <= intersection.left || intersection.bottom <= intersection.top) return false;
      }
    }
    if (effects.length) { unsupported = 'Unsupported applied clip-path, clip, mask or filter; visible parts cannot be established.'; return false; }
    const style = getComputedStyle(el);
    if ((kind === 'text' || ['text', 'tspan'].includes(el.localName)) && !textPaint(style)) return false;
    if (el.namespaceURI === 'http://www.w3.org/2000/svg') {
      if (kind === 'text' || ['text', 'tspan', 'rect', 'circle', 'ellipse', 'path', 'polygon', 'polyline', 'line'].includes(el.localName)) {
        if (!(el.localName !== 'line' && painted(style.fill, style.fillOpacity)) && !(parseFloat(style.strokeWidth) > 0 && painted(style.stroke, style.strokeOpacity))) return false;
      } else {
        // A transparent group is a usable region only through its rendered children.
        return [...el.querySelectorAll('text,rect,circle,ellipse,path,polygon,polyline,line')].some(child => !excluded(child) && visible(child, child.getBoundingClientRect(), child.localName === 'text' ? 'text' : 'id'));
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
    return { kind, value, node: indexes.get(el), ancestors, region, visible: visible(el, box, kind), box: { x: box.x, y: box.y, width: box.width, height: box.height },
      tokens: textNodes.filter(node => el.contains(node) && normalize(node.textContent)).map(node => tokenIds.get(node)) };
  };
  const textInfo = new Map(textNodes.map(node => {
    const el = node.parentElement, range = document.createRange(); range.selectNodeContents(node);
    return [node, { value: normalize(node.textContent), box: range.getBoundingClientRect(), visible: !!el && !excluded(el) && !el.closest('textarea,select,option') && !(reference && el.closest('[data-context-only="true"],.context-only')) && visible(el, range.getBoundingClientRect(), 'text') }];
  }));
  const renderedText = node => {
    if (node.nodeType === Node.TEXT_NODE) return textInfo.get(node)?.visible ? node.textContent : '';
    if (node.nodeType !== Node.ELEMENT_NODE || excluded(node) || ['textarea', 'select', 'option'].includes(node.localName)) return '';
    if (node.localName === 'br') return '\n';
    const text = [...node.childNodes].map(renderedText).join('');
    return node.namespaceURI !== 'http://www.w3.org/2000/svg' && /^(block|flex|grid|table|list-item)/.test(getComputedStyle(node).display) ? `\n${text}\n` : text;
  };
  const referenceIds = new Set();
  for (const el of elements) {
    const metadata = excluded(el);
    if (reference && (metadata || el.closest('[data-context-only="true"],.context-only'))) continue;
    if (el.id) {
      const part = item(el, 'id', el.id);
      if (metadata) part.visible = false;
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
  return { parts: parts.filter(part => reference || part.kind !== 'text' || !parts.some(other => other !== part && other.kind === 'text' && other.value === part.value && (!part.visible || other.visible) && other.ancestors.includes(part.node))) };
}

const center = box => [box.x + box.width / 2, box.y + box.height / 2];
const location = part => part ? `${part.visible ? 'visible' : 'hidden/outside'} at (${center(part.box).map(n => Math.round(n)).join(', ')})` : 'absent';
function compareParts(reference, actual, viewport) {
  const used = new Set(), matched = [], idMatches = new Map();
  // Resolve regions before labels, regardless of the SVG's document order.
  for (const ref of reference.filter(part => part.kind === 'id')) {
    const hits = actual.filter(part => part.kind === 'id' && part.value === ref.value);
    if (hits.length === 1) idMatches.set(ref.value, hits[0]);
  }
  const rows = reference.map(ref => {
    let hits = actual.filter(part => part.kind === ref.kind && part.value === ref.value && (ref.kind === 'id' || !(part.tokens || [part.node]).some(token => used.has(token))));
    const duplicate = ref.kind === 'id' && hits.length > 1;
    if (ref.kind === 'text') {
      const enclosing = idMatches.get(ref.region);
      const scoped = enclosing ? hits.filter(part => part.ancestors.includes(enclosing.node) || part.node === enclosing.node) : [];
      if (scoped.length) hits = scoped;
      const [x, y] = center(ref.box);
      hits.sort((a, b) => Number(b.visible) - Number(a.visible) || Math.hypot(...center(a.box).map((v, i) => (v - [x, y][i]) / [viewport.width, viewport.height][i])) - Math.hypot(...center(b.box).map((v, i) => (v - [x, y][i]) / [viewport.width, viewport.height][i])));
    }
    const found = hits[0]; if (found && ref.kind === 'text') for (const token of found.tokens || [found.node]) used.add(token);
    let status = duplicate || !found ? 'missing' : !found.visible ? 'hidden' : 'pass';
    if (status === 'pass' && center(ref.box).some((v, axis) => Math.abs(v - center(found.box)[axis]) / [viewport.width, viewport.height][axis] > 0.15)) status = 'region';
    matched.push(found);
    return { part: ref.kind === 'id' ? `#${ref.value}` : `“${ref.value}”`, kind: ref.kind, expected: location(ref), actual: duplicate ? `duplicate id (${hits.length} elements)` : location(found), status };
  });
  for (let i = 0; i < reference.length; i++) for (let j = i + 1; j < reference.length; j++) {
    const a = reference[i], b = reference[j], aa = matched[i], bb = matched[j];
    if (!aa?.visible || !bb?.visible || a.node === b.node || a.ancestors.includes(b.node) || b.ancestors.includes(a.node)) continue;
    const inverted = ['x', 'y'].some((axis, index) => {
      const size = index ? 'height' : 'width';
      const before = a.box[axis] + a.box[size] + 2 < b.box[axis], after = b.box[axis] + b.box[size] + 2 < a.box[axis];
      return before && center(aa.box)[index] > center(bb.box)[index] || after && center(aa.box)[index] < center(bb.box)[index];
    });
    if (inverted) for (const [index, other] of [[i, j], [j, i]]) if (rows[index].status === 'pass') { rows[index].status = 'order'; rows[index].actual += `; order inverted with ${rows[other].part}`; }
  }
  return rows;
}

export async function compareScreen({ url, drawingPath, cwd = process.cwd(), chromePath }, ports = {}) {
  let target; try { target = new URL(url); } catch { throw failure('Screen URL must be an http/https URL without credentials.'); }
  if (!['http:', 'https:'].includes(target.protocol) || target.username || target.password) throw failure('Screen URL must be an http/https URL without credentials.');
  if (typeof drawingPath !== 'string' || !drawingPath.endsWith('.ui.svg')) throw failure('Drawing must be a readable regular .ui.svg file.');
  const drawing = resolve(cwd, drawingPath);
  let source; try { if (!lstatSync(drawing).isFile()) throw Error(); source = readFileSync(drawing, 'utf8'); } catch { throw failure(`Cannot read SVG drawing: ${drawingPath}.`); }
  // Reject obvious active content before even starting Chrome. Remaining XML/CSS
  // validation runs in the browser's inert parser before attaching the document.
  const active = source.replace(/<!--[\s\S]*?-->|<!\[CDATA\[[\s\S]*?\]\]>/g, '');
  if (!source.trim() || /<!DOCTYPE|<!ENTITY|<\s*(?:script|foreignObject)\b|\son\w+\s*=/i.test(active)) throw failure('Empty or unsafe SVG drawing.');
  const rendered = await (ports.browser ?? browserRun)({ source, url: target.href, chromePath, env: ports.env ?? process.env });
  if (!rendered?.reference?.length || !rendered.actual || !(rendered.viewport?.width > 0 && rendered.viewport?.height > 0)) throw failure('Browser returned no valid reference parts.', 5);
  const rows = compareParts(rendered.reference, rendered.actual, rendered.viewport);
  return { drawing, url: target.href, viewport: rendered.viewport, rows, passed: rows.every(row => row.status === 'pass') };
}

export function formatScreenComparison(report) {
  const escape = value => String(value).replace(/\|/g, '\\|').replace(/[\r\n]+/g, ' ');
  return [`Screen vs drawing (${escape(report.drawing)}, ${report.viewport.width} × ${report.viewport.height})`, '', '| Part | Kind | Expected | Actual | Status |', '| --- | --- | --- | --- | --- |',
    ...report.rows.map(row => `| ${[row.part, row.kind, row.expected, row.actual, row.status].map(escape).join(' | ')} |`), '',
    `Screen vs drawing: ${report.passed ? 'PASS' : 'FAIL'} (${report.rows.filter(row => row.status === 'pass').length} of ${report.rows.length} parts pass). Parts, text, regions and order; colors, typography and pixel equivalence require their separate comparator.`].join('\n');
}
