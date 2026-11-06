// Generated from prompts/cli/issue-dependency-graph-view.prompt.md.
// This file also runs in the bundled browser. Domain decisions belong to the model.
const escape = value => String(value ?? '').replace(/[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f-\u009f]/g, '\ufffd')
  .replace(/[&<>"']/g, character => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[character]);
const issueParts = key => /^https:\/\/github\.com\/([A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*)\/issues\/([1-9][0-9]*)$/.exec(key ?? '');
function githubLink(value, owner) {
  try {
    const url = new URL(value);
    if (url.protocol !== 'https:' || url.host !== 'github.com' || url.username || url.password || url.search) return '';
    const issue = /^(https:\/\/github\.com\/[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*\/(?:issues|pull)\/[1-9][0-9]*)(#issuecomment-[1-9][0-9]*)?$/.exec(value);
    if (issue) return issue[2] && owner && issue[1] !== owner ? '' : value;
    if (!/^\/[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*\/blob\/.+/.test(url.pathname)
      || (url.hash && !/^#L[1-9][0-9]*(?:-L[1-9][0-9]*)?$/.test(url.hash))) return '';
    const decoded = decodeURIComponent(url.pathname);
    if (/[\s\u0000-\u001f\u007f\\<>"']/.test(decoded) || decoded.split('/').some(part => part === '.' || part === '..')) return '';
    return value;
  } catch { return ''; }
}
const link = (url, label = url, owner) => {
  const safe = githubLink(url, owner);
  return safe ? `<a href="${escape(safe)}" target="_blank" rel="noopener noreferrer">${escape(label)}</a>` : `<span>${escape(label)}</span>`;
};
const label = node => {
  const parts = issueParts(node.key);
  return parts ? `#${parts[2]} ${node.title}` : `${node.key} ${node.title}`;
};
const filters = ['all', 'waiting', 'ready', 'running', 'unknown'];
const capital = text => text[0].toUpperCase() + text.slice(1);
const matchesFilter = (node, filter) => filter === 'all'
  || filter === 'ready' && node.eligible
  || filter === 'running' && node.executionState === 'running'
  || filter === 'waiting' && (['waiting', 'cycle'].includes(node.dependencyState) || ['question', 'pending'].includes(node.reviewState))
  || filter === 'unknown' && (node.dependencyState === 'unknown' || ['unchecked', 'stale', 'unverified', 'conflict'].includes(node.reviewState));
const nodeStatus = node => `${node.dependencyState} · review ${node.reviewState} · ${node.executionState}`;

const style = `<style>
*{box-sizing:border-box}body{margin:0;background:#f5f7fb;color:#182536;font:15px/1.5 system-ui,sans-serif}main{padding:16px;max-width:1480px;margin:auto}#graph-header{width:max-content;max-width:100%}h1{font-size:22px;line-height:1.3;margin:0 0 4px}h2{font-size:17px;margin:0 0 12px}h3{font-size:15px;margin:16px 0 4px}p{margin:4px 0 12px}a{color:#245ba8;overflow-wrap:anywhere}button,input{font:inherit}button{color:inherit;cursor:pointer;border:1px solid #8192a8;border-radius:6px;background:white;padding:6px 10px}button[aria-pressed=true]{background:#e9eff9;border-color:#245ba8;font-weight:650}button:focus-visible,input:focus-visible,summary:focus-visible,#graph-canvas:focus-visible{outline:3px solid #245ba8;outline-offset:3px}#search{margin:12px 0 10px;display:flex;gap:8px}#search input{min-width:0;flex:1;padding:7px 12px;background:white;border:1px solid #8192a8;border-radius:6px}#filters{width:max-content;max-width:100%;display:flex;flex-wrap:wrap;gap:6px}#filters button{border-color:transparent;background:transparent;padding:3px 9px}#filters button[aria-pressed=true]{background:#e9eff9;border-color:#8192a8}.sync-row{display:flex;align-items:center;justify-content:space-between;gap:12px;margin:9px 0 16px}.sync-row p{margin:0;max-width:75%;width:max-content}#refresh-graph{flex-shrink:0}.layout{display:grid;grid-template-columns:minmax(0,1.85fr) minmax(292px,1fr);gap:32px;align-items:start}.graph-panel{min-width:0}.canvas-shell{position:relative;border:1px solid #c5cfdd;border-radius:8px;background:white;overflow:hidden}.viewport-controls{position:absolute;bottom:14px;left:14px;right:14px;z-index:2;display:flex;flex-wrap:wrap;gap:6px;background:#ffffffed;padding:4px;border-radius:6px}.viewport-controls button{font-size:14px;padding:4px 8px}#graph-canvas{height:420px;overflow:hidden;position:relative;touch-action:none;cursor:grab}#graph-canvas:active{cursor:grabbing}.graph-scene{position:relative;transform-origin:0 0;width:100%}.graph-scene svg{position:absolute;inset:0;overflow:visible;pointer-events:none}.graph-nodes{list-style:none;margin:0;padding:0}.graph-nodes li{position:absolute;left:35px;width:calc(100% - 70px)}.node{display:block;width:100%;min-height:64px;text-align:left;padding:9px 13px;border-color:#7088a4;background:#e9eff9}.node.waiting{background:#fff1d6;border-color:#ad7718}.node.context{opacity:.58}.node[aria-pressed=true]{box-shadow:0 0 0 2px #245ba8}.node-title{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-weight:600}.node-state{display:block;font-size:13px}.node small{display:block;font-size:12px}.counts,.hint{font-size:13px;color:#465b71}.counts{margin:8px 0}.hint{margin-top:8px}#issue-details{height:250px;overflow:auto;padding:16px;background:white;border:1px solid #c5cfdd;border-radius:8px;min-width:0;overflow-wrap:anywhere}#issue-details ul{padding-left:20px}#issue-details li{margin-bottom:8px}.states{font-size:14px}.fact{border-left:3px solid #8192a8;padding-left:10px;white-space:normal}.fact-text{white-space:pre-wrap}.input-list{font-size:12px}.empty{padding:36px 20px}.issue-list{margin-top:12px}#issue-details p{margin:2px 0 5px}#issue-details h3{margin:8px 0 3px}.issue-list ul{padding-left:22px}.issue-list li{margin:8px 0}.issue-list button{max-width:100%;text-align:left;overflow-wrap:anywhere}.sr-only{position:absolute;width:1px;height:1px;overflow:hidden;white-space:nowrap}@media(max-width:760px){.layout{grid-template-columns:minmax(0,1fr);gap:28px}.graph-panel{display:contents}.canvas-shell{grid-row:1}#issue-details{grid-row:2}#graph-canvas{height:390px}#filters{gap:2px}#filters button{padding:3px 7px}.sync-row{align-items:flex-start}.sync-row p{max-width:75%}main{padding:16px}.viewport-controls{left:10px;right:10px}#issue-details{width:100%}}@media(prefers-reduced-motion:reduce){*{scroll-behavior:auto}}
</style>`;

/** Render the supplied model without changing its states or evidence. */
export function renderIssueGraph({ graph, repository = '', query = '', filter = 'all', selected = '', sync = 'empty', lastSync = '', warnings = [] }) {
  const nodes = graph?.nodes ?? [], edges = graph?.edges ?? [];
  const chosen = nodes.find(node => node.key === selected);
  const needle = query.toLocaleLowerCase();
  const visible = nodes.filter(node => matchesFilter(node, filter) && `${node.key} ${node.title}`.toLocaleLowerCase().includes(needle)).map(node => node.key);
  const retained = new Set(visible), pending = [...visible];
  while (pending.length) {
    const key = pending.pop();
    const blockers = [...(nodes.find(node => node.key === key)?.blockers ?? []), ...edges.filter(edge => edge.dependent === key).map(edge => edge.blocker)];
    for (const blocker of blockers) if (!retained.has(blocker)) { retained.add(blocker); pending.push(blocker); }
  }
  const context = nodes.filter(node => retained.has(node.key) && !visible.includes(node.key)).map(node => node.key);
  const shown = nodes.filter(node => retained.has(node.key));
  const selectedEdges = chosen ? edges.filter(edge => edge.dependent === chosen.key) : [];
  const reasons = chosen ? [...new Set([...chosen.reasons, ...selectedEdges.map(edge => edge.reason)])] : [];
  const facts = chosen?.facts ?? [];
  const emptyMessage = graph === null ? 'No saved graph' : '';
  const nodeIndex = new Map(shown.map((node, index) => [node.key, index]));
  const sceneHeight = Math.max(340, shown.length * 135 + 40);
  const partial = graph !== null && graph.complete === false && !lastSync;
  const status = partial ? 'Partial observations; no successful sync' : graph === null && !lastSync ? 'No saved sync' : `${capital(sync)} · Last sync ${lastSync || 'not available'}`;
  const edgeMarkup = edges.filter(edge => nodeIndex.has(edge.dependent) && nodeIndex.has(edge.blocker)).map(edge => {
    const from = nodeIndex.get(edge.dependent), to = nodeIndex.get(edge.blocker);
    const downward = to > from, start = 38 + from * 135 + (downward ? 64 : 0), end = 38 + to * 135 + (downward ? 0 : 64);
    return `<g data-from="${from}" data-to="${to}"><rect x="176.5" y="${Math.min(start, end)}" width="3" height="${Math.abs(end - start)}" fill="#59728e"/><polyline points="${downward ? `174,${end - 8} 178,${end} 182,${end - 8}` : `174,${end + 8} 178,${end} 182,${end + 8}`}" fill="none" stroke="#59728e" stroke-width="3"/><title>${escape(`${edge.dependent} waits for ${edge.blocker}: ${edge.reason}`)}</title></g>`;
  }).join('');
  const nodeMarkup = shown.map((node, index) => {
    const parts = issueParts(node.key), id = parts ? `issue-${parts[1].replaceAll('-', '--').replace('/', '-')}-${parts[2]}` : `issue-${index}`;
    const classes = ['node', node.dependencyState === 'waiting' || node.dependencyState === 'cycle' ? 'waiting' : '', context.includes(node.key) ? 'context' : ''].filter(Boolean).join(' ');
    return `<li id="${escape(id)}" style="top:${38 + index * 135}px"><button class="${classes}" type="button" value="${escape(node.key)}" data-select="${escape(node.key)}" title="${escape(label(node))}" aria-label="${escape(`${node.key} ${node.title}; ${nodeStatus(node)}`)}" aria-pressed="${node.key === chosen?.key}"><span class="node-title">${escape(label(node))}</span><span class="node-state">${node.nativeState === 'open' && edges.some(edge => edge.blocker === node.key) && node.key !== chosen?.key ? 'Open prerequisite' : escape(`${capital(node.dependencyState)}${node.key === chosen?.key ? ' · selected' : ''}`)}</span>${context.includes(node.key) ? '<small>Prerequisite context</small>' : ''}</button></li>`;
  }).join('');
  const details = !chosen ? '<p>No issue selected</p>' : `<h2>${escape(label(chosen))}</h2><p class="states">Review: ${escape(chosen.reviewState)} · Execution: ${escape(chosen.executionState)}</p>${selectedEdges.map(edge => `<p>Waits for ${link(edge.blocker, label(nodes.find(node => node.key === edge.blocker) ?? { key: edge.blocker, title: '' }))}</p><p>${escape(edge.reason || 'GitHub dependency; no saved reason')}</p>${edge.evidence.length ? `<p>${link(edge.evidence[0], 'Issue and review evidence')}</p>` : ''}`).join('')}<p>Source: ${escape(graph.repository)}<br>Captured: ${escape(graph.capturedAt)}</p><p>${link(chosen.key)}</p><p>Dependencies: ${escape(chosen.dependencyState)} · Native issue: ${escape(chosen.nativeState)}</p><p>${chosen.eligible ? 'Eligible by observed dependency facts.' : 'Not eligible by observed dependency facts.'} Room and automatic start are not proved.</p>
    <h3>Reasons</h3>${reasons.length ? `<ul>${reasons.map(reason => `<li>${escape(reason)}</li>`).join('')}</ul>` : '<p>No recorded open blocker. Review and execution states still apply.</p>'}
    ${selectedEdges.map(edge => `<section><h3>Prerequisite</h3><p>${link(edge.blocker, label(nodes.find(node => node.key === edge.blocker) ?? { key: edge.blocker, title: '' }))}</p><p>${escape(edge.reason || 'GitHub dependency; no saved reason')}</p>${edge.evidence.length ? `<ul>${edge.evidence.map(url => `<li>${link(url)}</li>`).join('')}</ul>` : '<p>No saved evidence.</p>'}</section>`).join('')}
    ${facts.map(fact => `<section class="fact"><h3>${escape(capital(fact.kind))}</h3><p class="fact-text">${escape(fact.text)}</p><p>Owning issue: ${link(fact.issue)}<br>Native state: ${escape(nodes.find(node => node.key === fact.issue)?.nativeState ?? 'unknown')}<br>Source: ${link(fact.source, fact.source, fact.issue)}</p>${fact.inputs.length ? `<details class="input-list"><summary>Examined inputs</summary><ul>${fact.inputs.map(input => `<li>${link(input.key)} · ${escape(input.revision)}</li>`).join('')}</ul></details>` : ''}</section>`).join('')}`;
  const html = `${style}<main id="dependency-app"><header id="graph-header"><h1>Dependency graph</h1><p>${escape(graph?.repository || repository || 'Repository graph')} · GitHub native links</p></header>
    <form id="search" role="search"><label for="issue-query" class="sr-only">Search issues</label><input id="issue-query" name="query" type="search" placeholder="Search issues" aria-label="Search issues" value="${escape(query)}"><button type="submit">Search</button></form>
    <nav id="filters" aria-label="Issue status">${filters.map(value => `<button type="button" id="filter-${value}" value="filter-${value}" data-filter="${value}" aria-pressed="${filter === value}">${capital(value)}</button>`).join('')}</nav>
    <div class="sync-row"><p role="status" aria-live="polite"><span id="sync-status">${escape(status)}</span>${sync === 'offline' ? partial ? ' · Offline; current facts are unknown.' : ' · Offline; saved facts kept. Current facts are unknown.' : ''}${warnings.length ? ` · ${warnings.map(escape).join(' · ')}` : ''}</p><button type="button" id="refresh-graph" value="refresh-graph">Refresh</button></div>
    <div class="layout"><section class="graph-panel" aria-label="Graph and issue list"><div class="canvas-shell"><div class="viewport-controls" aria-label="Graph viewport"><button id="zoom-in" type="button">Zoom in</button><button id="zoom-out" type="button">Zoom out</button><button id="fit-graph" type="button">Fit graph</button></div>
      <div id="graph-canvas" role="region" tabindex="0" aria-label="Dependency graph. Arrow keys pan; plus and minus zoom; Escape clears selection.">${graph === null ? `<div class="empty"><h2><span id="empty-message">No saved graph</span></h2><p>Dependency analysis is a separate coordinator intake action.</p><button type="button" id="prepare-dependencies">Prepare dependencies</button><p id="prepare-instruction" hidden>Run <code>pdd dependencies prepare</code> in your repository.</p></div>` : shown.length ? `<div class="graph-scene" style="height:${sceneHeight}px"><svg width="100%" height="${sceneHeight}" viewBox="0 0 360 ${sceneHeight}" preserveAspectRatio="none" aria-hidden="true">${edgeMarkup}</svg><ol class="graph-nodes">${nodeMarkup}</ol></div>` : '<p class="empty">No matching issues.</p>'}</div></div>
      <p class="counts">${visible.length} matches · ${context.length} prerequisite context</p><p class="hint">Arrows point from dependent to prerequisite. Drag or use arrow keys to pan.</p>
      <details class="issue-list"><summary>Issue list and dependency links</summary><ul>${shown.map(node => `<li><button type="button" data-select="${escape(node.key)}" value="${escape(node.key)}">${escape(label(node))} · ${escape(nodeStatus(node))}</button>${edges.filter(edge => edge.dependent === node.key).map(edge => `<p>Waits for ${link(edge.blocker)}: ${escape(edge.reason || 'GitHub dependency; no saved reason')}</p>`).join('')}</li>`).join('')}</ul></details></section>
      <aside id="issue-details" tabindex="0" aria-label="Selected issue details">${details}</aside></div>
    <p class="hint">Source: ${escape(graph?.repository || 'not saved')} · Captured ${escape(graph?.capturedAt || 'not saved')}. VM-only work, account room and deployment are not proved by this view.</p><div id="selection-status" class="sr-only" role="status" aria-live="polite">${chosen ? escape(`Selected ${label(chosen)}`) : 'No issue selected'}</div></main>`;
  return { html, visible, context, selected: chosen?.key ?? '', reasons, sync, facts, emptyMessage };
}

// The same render boundary handles every browser change. Only viewport state is local.
function mount() {
  const initial = document.getElementById('graph-state');
  if (!initial) return;
  const state = JSON.parse(initial.textContent), base = new URL('.', location.href);
  let viewport = { x: 0, y: 0, scale: 1 }, polling = false, closed = false;
  const applyViewport = () => {
    const scene = document.querySelector('.graph-scene');
    if (scene) scene.style.transform = `translate(${viewport.x}px,${viewport.y}px) scale(${viewport.scale})`;
  };
  // Pack only connected components; graph ordering and native edges remain unchanged.
  function layoutGraph() {
    const canvas = document.getElementById('graph-canvas'), scene = canvas?.querySelector('.graph-scene');
    if (!scene) return;
    const items = [...scene.querySelectorAll('.graph-nodes li')], svg = scene.querySelector('svg');
    const groups = [...svg.querySelectorAll('g[data-from]')], parent = items.map((_, i) => i);
    const find = i => parent[i] === i ? i : (parent[i] = find(parent[i]));
    for (const g of groups) { const a = find(Number(g.dataset.from)), b = find(Number(g.dataset.to)); if (a !== b) parent[b] = a; }
    const components = new Map();
    items.forEach((_, i) => { const root = find(i); if (!components.has(root)) components.set(root, []); components.get(root).push(i); });
    const columns = Math.max(1, Math.floor((canvas.clientWidth - 16) / 245));
    const columnWidth = canvas.clientWidth / columns, heights = Array(columns).fill(14), positions = [];
    const ordered = [...components.values()].sort((a, b) => b.length - a.length || a[0] - b[0]);
    for (const component of ordered) {
      const col = heights.indexOf(Math.min(...heights));
      for (const index of component) {
        const item = items[index], left = col * columnWidth + 16;
        item.style.left = `${left}px`; item.style.width = `${columnWidth - 32}px`; item.style.top = `${heights[col]}px`;
        const height = item.offsetHeight; positions[index] = { left, top: heights[col], height };
        heights[col] += height + 26;
      }
      heights[col] += 4;
    }
    const height = Math.max(340, ...heights) + 50;
    scene.style.height = `${height}px`; svg.setAttribute('height', height); svg.setAttribute('viewBox', `0 0 ${canvas.clientWidth} ${height}`);
    for (const group of groups) {
      const from = positions[Number(group.dataset.from)], to = positions[Number(group.dataset.to)];
      const x = from.left - 8, start = from.top + from.height / 2, end = to.top + to.height / 2;
      group.querySelector('rect')?.remove(); group.querySelector('.arrow-tip')?.remove();
      const arrow = group.querySelector('polyline');
      arrow.setAttribute('points', `${from.left},${start} ${x},${start} ${x},${end} ${to.left},${end}`);
      arrow.setAttribute('stroke-width', '2');
      const tip = document.createElementNS('http://www.w3.org/2000/svg', 'polyline');
      tip.setAttribute('class', 'arrow-tip'); tip.setAttribute('points', `${to.left - 6},${end - 4} ${to.left},${end} ${to.left - 6},${end + 4}`);
      tip.setAttribute('fill', 'none'); tip.setAttribute('stroke', '#59728e'); tip.setAttribute('stroke-width', '2'); group.append(tip);
    }
  }
  function paint() {
    const active = document.activeElement, focusId = active?.id, focusKey = active?.dataset?.select;
    const cursor = focusId === 'issue-query' ? active.selectionStart : null;
    document.getElementById('dependency-app').outerHTML = renderIssueGraph(state).html.replace(/^<style>[\s\S]*?<\/style>/, '');
    layoutGraph(); applyViewport();
    const next = focusKey ? [...document.querySelectorAll('[data-select]')].find(element => element.dataset.select === focusKey) : document.getElementById(focusId);
    next?.focus({ preventScroll: true });
    if (cursor !== null) next?.setSelectionRange?.(cursor, cursor);
    bind();
  }
  function zoom(factor) { viewport.scale = Math.min(3, Math.max(.3, viewport.scale * factor)); applyViewport(); }
  function fit() {
    const canvas = document.getElementById('graph-canvas'), scene = document.querySelector('.graph-scene');
    viewport = { x: 0, y: 0, scale: scene ? Math.max(.3, Math.min(1, canvas.clientWidth / scene.offsetWidth)) : 1 };
    applyViewport();
  }
  function bind() {
    document.getElementById('search').addEventListener('submit', event => { event.preventDefault(); state.query = new FormData(event.currentTarget).get('query'); paint(); });
    document.getElementById('issue-query').addEventListener('input', event => { state.query = event.target.value; paint(); });
    for (const button of document.querySelectorAll('[data-filter]')) button.addEventListener('click', () => { state.filter = button.dataset.filter; paint(); });
    for (const button of document.querySelectorAll('[data-select]')) button.addEventListener('click', () => { state.selected = button.dataset.select; paint(); });
    document.getElementById('prepare-dependencies')?.addEventListener('click', () => { document.getElementById('prepare-instruction').hidden = false; });
    document.getElementById('zoom-in').addEventListener('click', () => zoom(1.2));
    document.getElementById('zoom-out').addEventListener('click', () => zoom(1 / 1.2));
    document.getElementById('fit-graph').addEventListener('click', fit);
    document.getElementById('refresh-graph').addEventListener('click', () => { if (!polling) { state.sync = state.graph ? 'refreshing' : 'empty'; paint(); void update(true); } });
    const canvas = document.getElementById('graph-canvas');
    canvas.addEventListener('keydown', event => {
      if (event.target !== canvas) return;
      if (['ArrowLeft', 'ArrowRight', 'ArrowUp', 'ArrowDown'].includes(event.key)) {
        event.preventDefault(); viewport.x += event.key === 'ArrowLeft' ? 30 : event.key === 'ArrowRight' ? -30 : 0;
        viewport.y += event.key === 'ArrowUp' ? 30 : event.key === 'ArrowDown' ? -30 : 0; applyViewport();
      } else if (['+', '=', '-'].includes(event.key)) { event.preventDefault(); zoom(event.key === '-' ? 1 / 1.2 : 1.2); }
    });
    let drag;
    canvas.addEventListener('pointerdown', event => { if (event.target.closest('button,a')) return; drag = { x: event.clientX, y: event.clientY, start: { ...viewport } }; canvas.setPointerCapture(event.pointerId); });
    canvas.addEventListener('pointermove', event => { if (drag) { viewport.x = drag.start.x + event.clientX - drag.x; viewport.y = drag.start.y + event.clientY - drag.y; applyViewport(); } });
    canvas.addEventListener('pointerup', () => { drag = null; });
    canvas.addEventListener('pointercancel', () => { drag = null; });
    canvas.addEventListener('wheel', event => { event.preventDefault(); if (event.ctrlKey || event.metaKey) zoom(event.deltaY > 0 ? 1 / 1.1 : 1.1); else { viewport.x -= event.deltaX; viewport.y -= event.deltaY; applyViewport(); } }, { passive: false });
  }
  async function update(refresh = false) {
    if (polling || closed) return;
    polling = true;
    try {
      const response = await fetch(new URL(refresh ? 'refresh' : 'data', base), { cache: 'no-store', credentials: 'omit' });
      if (!response.ok) throw Error('read failed');
      const next = await response.json();
      // A failed/empty update cannot erase the last successful model.
      if (next.graph) { state.graph = next.graph; state.lastSync = next.lastSync; }
      state.sync = next.graph || !state.graph ? next.sync : 'offline';
      state.warnings = Array.isArray(next.warnings) ? next.warnings : [];
      if (state.selected && !state.graph?.nodes.some(node => node.key === state.selected)) state.selected = '';
      paint();
    } catch { state.sync = state.graph ? 'offline' : 'empty'; paint(); }
    finally { polling = false; }
  }
  document.addEventListener('keydown', event => { if (event.key === 'Escape') { state.selected = ''; paint(); } });
  window.addEventListener('pagehide', () => { closed = true; });
  layoutGraph(); bind();
  window.addEventListener('resize', layoutGraph);
  const timer = setInterval(() => { if (!closed) void update(); else clearInterval(timer); }, 2000);
}
if (typeof window !== 'undefined') mount();
