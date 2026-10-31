// Generated from prompts/cli/try-http.prompt.md (sha256: f0f96cde921aa85d58cd7126e594c6e10acad1a9ea3e1b61feffe8817997be75).
import { createServer, validateHeaderName, validateHeaderValue } from 'node:http';
import { join, relative } from 'node:path';
import { checkInput } from './runtime-preflight.mjs';
import { cleanText, tryUsage, tryUsageHeaders, tryUsageLine } from './runtime-output.mjs';
import { runDoorCall } from './runtime-client.mjs';

const problem = (status, message) => Object.assign(new Error(message), { httpStatus: status });
const shellWord = word => /^[A-Za-z0-9_./:@%+=,-]+$/.test(word) ? word : `'${word.replaceAll("'", "'\\''")}'`;
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const HOP = new Set(['connection', 'keep-alive', 'proxy-authenticate', 'proxy-authorization', 'te', 'trailer', 'transfer-encoding', 'upgrade', 'content-length']);
function primitive(values, schema) {
  if (schema?.type === 'array') return values.map(v => primitive([v], schema.items));
  if (values.length !== 1) throw problem(400, 'A query field was repeated; declare an array to accept repeated values.');
  const value = values[0];
  if (schema?.type === 'string') return value;
  if (schema?.type === 'boolean' && /^(true|false)$/.test(value)) return value === 'true';
  if (['integer', 'number'].includes(schema?.type) && /^-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?$/.test(value)) {
    const number = Number(value);
    if (Number.isFinite(number) && (schema.type === 'number' || Number.isInteger(number))) return number;
  }
  throw problem(400, 'A query or path value does not match the prompt’s input type.');
}
function pathParams(route, pathname) {
  const wanted = route.path.split('/'), got = pathname.split('/');
  if (wanted.length !== got.length) return null;
  const params = Object.create(null);
  for (let i = 0; i < wanted.length; i++) {
    if (wanted[i].startsWith(':')) {
      try { params[wanted[i].slice(1)] = decodeURIComponent(got[i]); } catch { throw problem(400, 'A path parameter has invalid UTF-8 or escaping.'); }
    } else if (wanted[i] !== got[i]) return null;
  }
  return params;
}
function propertiesOf(schema) { return object(schema?.properties) ? schema.properties : {}; }
function inputFor(entry, req, url, params, text, method) {
  const props = propertiesOf(entry.input_schema), querySchema = propertiesOf(props.query), input = Object.create(null);
  const query = Object.create(null), paramValues = Object.create(null), bodyProps = Object.create(null);
  for (const key of new Set(url.searchParams.keys())) {
    const schema = props.query ? querySchema[key] : props[key];
    if (!schema || ['method', 'path', 'headers', 'body', 'params'].includes(key)) throw problem(400, `The route does not declare query field ${cleanText(key)}.`);
    query[key] = primitive(url.searchParams.getAll(key), schema);
  }
  for (const [key, value] of Object.entries(params)) {
    const schema = props.params ? propertiesOf(props.params)[key] : props[key];
    if (!schema) throw problem(400, 'The prompt does not declare this route parameter.');
    paramValues[key] = primitive([value], schema);
  }
  let body;
  if (text.length) {
    if (props.body?.type === 'string') body = text;
    else {
      try { body = JSON.parse(text); } catch { throw problem(400, 'The request body is not valid JSON.'); }
      if (object(body)) for (const [key, value] of Object.entries(body)) bodyProps[key] = value;
    }
  }
  for (const [key, schema] of Object.entries(props)) {
    if (key === 'method') input[key] = method;
    else if (key === 'path') input[key] = url.pathname;
    else if (key === 'query') input[key] = query;
    else if (key === 'params') input[key] = paramValues;
    else if (key === 'headers') {
      const headers = Object.create(null);
      for (const [name, headerSchema] of Object.entries(propertiesOf(schema))) {
        const value = req.headers[name.toLowerCase()];
        if (value !== undefined) headers[name] = primitive(Array.isArray(value) ? value : [value], headerSchema);
      }
      input[key] = headers;
    } else if (key === 'body') { if (body !== undefined) input[key] = body; }
    else if (Object.hasOwn(paramValues, key)) input[key] = paramValues[key];
    else if (Object.hasOwn(query, key)) input[key] = query[key];
    else if (Object.hasOwn(bodyProps, key)) input[key] = bodyProps[key];
  }
  const errors = checkInput(input, entry.input_schema, 0).refusals;
  if (errors.length) throw problem(400, errors[0].message || 'The request does not match the prompt’s input schema.');
  return input;
}
function responseFor(result) {
  if (!object(result) || !Number.isInteger(result.status) || result.status < 200 || result.status > 599) throw problem(502, 'The prompt must return an HTTP status from 200 to 599.');
  if (result.headers !== undefined && !object(result.headers)) throw problem(502, 'The prompt must return an object of HTTP headers.');
  const headers = Object.create(null), nominated = new Set(String(result.headers?.connection ?? result.headers?.Connection ?? '').toLowerCase().split(',').map(s => s.trim()));
  for (const [name, value] of Object.entries(result.headers ?? {})) {
    if (HOP.has(name.toLowerCase()) || nominated.has(name.toLowerCase())) continue;
    if (!(typeof value === 'string' || Array.isArray(value) && value.every(v => typeof v === 'string'))) throw problem(502, 'The prompt returned an invalid HTTP header value.');
    try { validateHeaderName(name); for (const item of Array.isArray(value) ? value : [value]) validateHeaderValue(name, item); } catch { throw problem(502, 'The prompt returned an invalid HTTP header.'); }
    headers[name.toLowerCase()] = value;
  }
  const value = Object.hasOwn(result, 'body') ? result.body : Object.fromEntries(Object.entries(result).filter(([key]) => !['status', 'headers'].includes(key)));
  const body = typeof value === 'string' ? value : JSON.stringify(value);
  if (body === undefined) throw problem(502, 'The prompt returned no HTTP response body.');
  if (!headers['content-type']) headers['content-type'] = typeof value === 'string' ? 'text/plain; charset=utf-8' : 'application/json; charset=utf-8';
  return { status: result.status, headers, body };
}

const SCREEN_PREFIX = '/__pdd/screen/';
const SCREEN_CSP = "default-src 'none'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src data:; connect-src 'self'; frame-src 'self'; base-uri 'self'; form-action 'none'; frame-ancestors 'none'; object-src 'none'";
function screenResource(url, method) {
  if (url.pathname === '/' && ['GET', 'HEAD'].includes(method) && !url.search) return 'index.html';
  if (!url.pathname.startsWith(SCREEN_PREFIX)) return null;
  const path = url.pathname.slice(SCREEN_PREFIX.length);
  if (['GET', 'HEAD'].includes(method)) {
    if (!url.search && (['index.html', 'door-screen.js', 'door-screen.css', 'try-frame.js', 'api/state'].includes(path) || /^app-asset\/[0-9]+$/.test(path))) return path;
    if (path === 'api/action' && [...url.searchParams.keys()].length === 1 && url.searchParams.has('id') && /^[A-Za-z0-9_-]{1,128}$/.test(url.searchParams.get('id'))) return path + url.search;
  }
  if (method === 'POST' && !url.search && ['api/app/open', 'api/act'].includes(path)) return path;
  return null;
}
async function requestText(req) {
  const chunks = []; let size = 0;
  const timeout = setTimeout(() => req.destroy(), 30_000);
  try {
    for await (const chunk of req) { size += chunk.length; if (size > 1024 * 1024) throw problem(413, 'The request body exceeds 1 MiB.'); chunks.push(chunk); }
  } finally { clearTimeout(timeout); }
  try { return new TextDecoder('utf-8', { fatal: true }).decode(Buffer.concat(chunks)); } catch { throw problem(400, 'The request body must be UTF-8.'); }
}

// Build a request only from authored input; missing values remain visible placeholders.
function requestExample(entry, tests, port) {
  const step = tests.flatMap(test => test.doc?.steps ?? []).find(step => step.entry_path === entry.entry_path && step.operation === entry.operation);
  const input = step?.input ?? {}, props = propertiesOf(entry.input_schema);
  const missing = name => `<required:${name}>`;
  const path = entry.route.path.replace(/:([A-Za-z][A-Za-z0-9_]*)/g, (_, name) => {
    const value = (input.params ?? input)[name];
    return value === undefined ? missing(name) : encodeURIComponent(String(value));
  });
  const query = new URLSearchParams();
  const queryProps = props.query ? propertiesOf(props.query) : props;
  const required = props.query?.required ?? entry.input_schema?.required ?? [];
  const parameters = new Set([...entry.route.path.matchAll(/:([A-Za-z][A-Za-z0-9_]*)/g)].map(match => match[1]));
  for (const name of Object.keys(queryProps)) {
    if (!props.query && (parameters.has(name) || ['body', 'headers', 'method', 'path', 'params'].includes(name))) continue;
    const value = (props.query ? input.query : input)?.[name];
    if (value !== undefined) for (const item of Array.isArray(value) ? value : [value]) query.append(name, String(item));
    else if (required.includes(name)) query.append(name, missing(name));
  }
  const url = `http://127.0.0.1:${port}${path}${query.size ? `?${query}` : ''}`;
  const args = ['curl', '-X', entry.route.method, url];
  for (const name of Object.keys(propertiesOf(props.headers))) {
    const value = input.headers?.[name];
    if (value !== undefined || props.headers.required?.includes(name)) args.push('-H', `${name}: ${value ?? missing(name)}`);
  }
  if (props.body && (input.body !== undefined || entry.input_schema.required?.includes('body'))) {
    const body = input.body === undefined ? missing('body') : typeof input.body === 'string' ? input.body : JSON.stringify(input.body);
    if (props.body.type !== 'string') args.push('-H', 'Content-Type: application/json');
    args.push('--data', body);
  }
  return args.map(shellWord).join(' ');
}

export async function openServe(context, test, sessionId, options) {
  const { ports, root, origin, identity } = context;
  const model = await context.runtime.send(`/v1/try/${sessionId}/model`, { method: 'GET' }, 30_000);
  if (model.status !== 200 || !Array.isArray(model.json?.entries)) throw problem(502, cleanText(model.json?.error?.message || 'The interpreter could not read this Try’s routes. It needs the Try doors server branch.'));
  const routes = model.json.entries.filter(e => e.http).map(entry => ({ ...entry, route: entry.http }));
  const hasScreen = model.json.app_map === true;
  if (hasScreen && routes.some(e => ['GET', 'HEAD'].includes(e.route.method) && e.route.path === '/' || e.route.path.startsWith(SCREEN_PREFIX))) throw problem(502, 'This app map reserves GET/HEAD / and /__pdd/screen/; its HTTP routes conflict with the Screen.');
  if (!routes.length && !hasScreen) {
    if (context.appMap) {
      const command = ['pdd', 'try', test.story, '--serve', String(options['--serve'] ?? 8080), '--new', '--app-map', relative(context.cwd ?? root, join(root, context.appMap))].map(shellWord).join(' ');
      throw problem(502, `This saved Try has no Screen app map. Start a new Try with the selected app map: ${command}`);
    }
    throw problem(502, 'This Story has neither a Screen app map nor named HTTP routes. Add an app map (RUNBOOK §13), or name an HTTP route such as HTTP GET /api/books in input_schema.title (RUNBOOK §19).');
  }
  const keys = new Set();
  for (const entry of routes) {
    const key = `${entry.route.method} ${entry.route.path.replace(/:[A-Za-z][A-Za-z0-9_]*/g, ':param')}`;
    if (keys.has(key)) throw problem(502, 'This Try has overlapping HTTP route labels; name each method/path once.');
    keys.add(key);
  }
  let latestUsage = tryUsage(model.json);
  const callCap = latestUsage.cap;
  (ports.stderr ?? process.stderr).write(`${tryUsageLine(latestUsage)}\n`);
  let tail = Promise.resolve(), pending = 0, stopped = false;
  const server = createServer(async (req, res) => {
    let counted = false, usage = { ...latestUsage, calls: 0 }, usageSource = 'last-known';
    const reply = (status, message) => { if (!res.headersSent) { res.writeHead(status, { 'content-type': 'text/plain; charset=utf-8', 'cache-control': 'no-store', ...tryUsageHeaders(usage), 'x-pdd-usage-source': usageSource }); res.end(`pdd try: ${cleanText(message)}\n`); } else res.destroy(); };
    try {
      const port = server.address()?.port, acceptedHost = new Set([`127.0.0.1:${port}`, `localhost:${port}`]);
      if (port === 80) { acceptedHost.add('127.0.0.1'); acceptedHost.add('localhost'); }
      const acceptedOrigin = new Set([...acceptedHost].map(host => `http://${host}`));
      if (!acceptedHost.has(req.headers.host) || (req.headers.origin && !acceptedOrigin.has(req.headers.origin)) || req.headers['sec-fetch-site'] === 'cross-site') throw problem(403, 'This local Try accepts requests only from its own origin.');
      if (!req.url.startsWith('/') || req.url.startsWith('//') || req.url.includes('\\')) throw problem(400, 'Use a local absolute request path.');
      const url = new URL(req.url, `http://127.0.0.1:${port}`);
      const resource = hasScreen ? screenResource(url, req.method) : null;
      if (resource) {
        if (pending >= 32 || stopped || context.signal?.aborted) throw problem(503, 'The local Try is busy or stopped.');
        pending++; counted = true;
        const body = await requestText(req);
        if (req.method === 'POST' && req.headers['content-type']?.split(';')[0] !== 'application/json') throw problem(415, 'Screen actions require application/json.');
        if (stopped || context.signal?.aborted) throw problem(503, 'The local Try is stopped.');
        const upstream = await context.runtime.send(`/v1/try/${sessionId}/screen/${resource}`, { method: req.method === 'HEAD' ? 'GET' : req.method,
          ...(req.method === 'POST' ? { headers: { 'Content-Type': 'application/json' }, body } : {}) }, 90_000);
        if (upstream.lost || !Number.isInteger(upstream.status) || upstream.status < 200 || upstream.status > 599) throw problem(502, 'The Screen request result is unknown. Read its action ID; do not resubmit.');
        const text = upstream.text ?? JSON.stringify(upstream.json);
        if (typeof text !== 'string' || Buffer.byteLength(text) > 16 * 1024 * 1024) throw problem(502, 'The Screen response is unavailable or too large.');
        res.writeHead(upstream.status, { 'content-type': upstream.headers?.get('content-type') || 'application/json; charset=utf-8',
          'content-length': Buffer.byteLength(text), 'cache-control': 'no-store', 'content-security-policy': SCREEN_CSP,
          'referrer-policy': 'no-referrer', 'x-content-type-options': 'nosniff' });
        res.end(req.method === 'HEAD' ? '' : text); return;
      }
      if (hasScreen && url.pathname.startsWith(SCREEN_PREFIX)) { req.resume(); reply(404, 'This Screen resource is not available.'); return; }
      let selected, params;
      // A literal route wins over a parameter route; HEAD has its own entry before GET fallback.
      const candidates = routes.filter(e => e.route.method === req.method || req.method === 'HEAD' && e.route.method === 'GET')
        .sort((a, b) => Number(a.route.method !== req.method) - Number(b.route.method !== req.method) || (a.route.path.match(/:/g)?.length ?? 0) - (b.route.path.match(/:/g)?.length ?? 0));
      for (const entry of candidates) { const found = pathParams(entry.route, url.pathname); if (found) { selected = entry; params = found; break; } }
      if (!selected) { req.resume(); reply(404, 'No prompt names this HTTP route.'); return; }
      if (req.headers['sec-fetch-dest'] && req.headers['sec-fetch-dest'] !== 'empty') throw problem(403, 'Use curl or fetch for this API route; embedded resources and page navigations cannot spend AI calls.');
      if (pending >= 32 || stopped) throw problem(503, 'The local Try is busy or stopped.');
      pending++; counted = true;
      const text = await requestText(req);
      const input = inputFor(selected, req, url, params, text, selected.route.method);
      // One line per request in the pdd window, like a local server log: the call can take many seconds.
      const label = `${req.method} ${url.pathname}`, sentAt = Date.now();
      ports.stderr?.write(`${label}: running on the Try…\n`);
      const work = tail.then(async () => {
        if (stopped || context.signal?.aborted) throw problem(503, 'The local Try is stopped.');
        return runDoorCall({ root, origin, login: identity.login, sessionId, callCap, prompt: selected.entry_path, operation: selected.operation }, input,
          { ...ports, signal: context.signal });
      });
      tail = work.catch(() => {});
      usage = tryUsage({}, { cap: callCap }); usageSource = 'runtime';
      const answer = await work;
      usage = answer.usage; latestUsage = usage;
      const result = responseFor(answer.result);
      const body = req.method === 'HEAD' || [204, 304].includes(result.status) ? '' : result.body;
      const headers = { ...result.headers, ...(![204, 304].includes(result.status) ? { 'content-length': Buffer.byteLength(req.method === 'HEAD' ? result.body : body) } : {}) };
      res.writeHead(result.status, { ...headers, ...tryUsageHeaders(usage), 'x-pdd-usage-source': usageSource }); res.end(body);
      ports.stderr?.write(`${label}: ${result.status} in ${Math.round((Date.now() - sentAt) / 1000)} s\n`);
    } catch (error) {
      if (error.tryUsage) { usage = error.tryUsage; latestUsage = usage; usageSource = 'runtime'; }
      req.resume(); reply(error.httpStatus || 502, error.message || 'The interpreter could not confirm this request.');
      ports.stderr?.write(`${req.method} ${req.url.split('?')[0]}: ${error.httpStatus || 502} ${cleanText(error.message || 'The interpreter could not confirm this request.')}\n`);
    }
    finally { if (counted) pending--; }
  });
  server.requestTimeout = 30_000; server.headersTimeout = 15_000;
  const wanted = Number(options['--serve'] ?? 8080);
  await new Promise((done, reject) => { server.once('error', reject); server.listen(wanted, '127.0.0.1', done); }).catch(error => {
    if (error.code === 'EADDRINUSE') throw problem(502, `port ${wanted} is in use by another program. Stop it, or run pdd try ${test.story} --serve ${wanted === 65535 ? wanted - 1 : wanted + 1}.`);
    if (error.code === 'EACCES') throw problem(502, `port ${wanted} needs extra rights on this computer. Run pdd try ${test.story} --serve 8080.`);
    throw error;
  });
  const stop = () => { stopped = true; server.close(); server.closeIdleConnections(); server.closeAllConnections(); };
  context.signal?.addEventListener('abort', stop, { once: true });
  const port = server.address().port;
  ports.stdout.write(`Try is serving at http://127.0.0.1:${port}\n${routes.length ? routes.map(e => `  ${e.route.method} ${e.route.path}`).join('\n') : '  Screen only (no named HTTP routes).'}\nCtrl-C closes this server. The Try session keeps its saved data.\n`);
  if (routes.length) ports.stdout.write(`Example: ${requestExample(routes[0], context.simulationTests ?? [test], port)}\n`);
  if (hasScreen) ports.stdout.write(`Screen: http://127.0.0.1:${port}/\n`);
  try {
    if (ports.serve) { await ports.serve(server); return 0; }
    await new Promise(done => { server.once('close', done); if (context.signal?.aborted) stop(); });
    return 0;
  } finally { stop(); context.signal?.removeEventListener('abort', stop); }
}
