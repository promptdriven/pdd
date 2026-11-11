// A fake PDD login server for tests: the login server API v1 of the pool design (#3252, DESIGN.md section 7),
// in memory, on 127.0.0.1. Fake gh tokens and fake logins only. It keeps a full login in memory and only ever
// sends back an access-only copy (unless a test turns on copyWithRefresh to prove that the client refuses it).
// The copy desk treats a login with no usage row as ready (the real server also needs a fresh usage row).
import { createServer } from 'node:http';
import { randomBytes } from 'node:crypto';

const NAME = /^[a-z0-9][a-z0-9._-]{0,31}$/;
const GH_LOGIN = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;
const lower = value => String(value).toLowerCase();
const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);

// A fake JWT whose payload has `exp` (seconds); the fake reads the access end from it.
export function fakeJwt(payload) {
  const part = value => Buffer.from(JSON.stringify(value)).toString('base64url');
  return `${part({ alg: 'none', typ: 'JWT' })}.${part(payload)}.fake-signature`;
}

// A fake full Codex login (auth.json text) with a nonempty refresh token.
export function fakeLogin({ access = 'fake-access', refresh = 'fake-refresh', account = 'fake-account', exp = Math.floor(Date.now() / 1000) + 10 * 86400 } = {}) {
  return JSON.stringify({ OPENAI_API_KEY: null, tokens: { id_token: fakeJwt({ exp, email: 'fake@example.invalid' }), access_token: fakeJwt({ exp, sub: access }),
    refresh_token: refresh, account_id: account }, last_refresh: new Date().toISOString() });
}

function accessEnd(auth, now) {
  try {
    const payload = JSON.parse(Buffer.from(JSON.parse(auth).tokens.access_token.split('.')[1], 'base64url').toString('utf8'));
    if (Number.isFinite(payload.exp)) return payload.exp * 1000;
  } catch { /* not a fake JWT */ }
  return now + 10 * 86400_000;
}

export async function startFakeAccountsServer({ users = [], github = {}, now = () => Date.now() } = {}) {
  const byToken = new Map(users.map(user => [user.token, { login: user.login, id: Number(user.id) }]));
  const logins = new Map(), groups = new Map(), orders = new Map(), paused = new Map(), machines = new Map();
  const audit = [], requests = [], queued = [];
  const options = { copyWithRefresh: false };
  const counts = { fullLoginsReceived: 0, copies: 0 };
  const newId = prefix => `${prefix}_${randomBytes(6).toString('hex')}`;

  const inGroup = (group, user) => group.members.includes(lower(user.login))
    || (group.github !== null && (github[group.github] ?? github[lower(group.github)] ?? []).some(name => lower(name) === lower(user.login)));
  const groupOf = id => groups.get(id) ?? null;
  // How a user reaches a login: 'own', 'accepted', ['invited', via] or null.
  function relation(login, user) {
    if (login.owner.id === user.id) return { kind: 'own' };
    const share = login.shares.get(lower(user.login));
    if (share) return { kind: share.state, via: 'user' };
    if (login.left.has(lower(user.login))) return null;
    for (const groupId of login.groupShares) {
      const group = groupOf(groupId);
      if (!group || !inGroup(group, user)) continue;
      return { kind: group.accepted.has(lower(user.login)) ? 'accepted' : 'invited', via: `group:${group.name}` };
    }
    return null;
  }
  const canUse = (login, user) => ['own', 'accepted'].includes(relation(login, user)?.kind);
  const pausedFor = user => paused.get(user.id) ?? new Set();
  function rowFor(login, user) {
    const row = { id: login.id, name: login.name, owner: { ...login.owner }, provider: login.provider, plan: login.plan, reset: login.reset,
      stop: { ...login.stop }, paused: pausedFor(user).has(login.id), state: login.state, week: login.week, fiveHour: login.fiveHour,
      accessExpiresAt: login.accessExpiresAt, refreshOkAt: login.refreshOkAt };
    if (login.owner.id === user.id) row.sharedWith = [...login.shares.values()].map(share => share.login);
    const group = [...login.groupShares].map(groupOf).find(Boolean);
    if (group) row.group = group.name;
    return row;
  }
  const groupView = group => ({ id: group.id, name: group.name, owner: group.owner, members: [...group.members], github: group.github });
  function effectiveOrder(user) {
    const usable = [...logins.values()].filter(login => canUse(login, user));
    const named = (orders.get(user.id) ?? []).filter(id => usable.some(login => login.id === id));
    const rest = usable.filter(login => !named.includes(login.id)).sort((a, b) => (a.owner.id === user.id ? 0 : 1) - (b.owner.id === user.id ? 0 : 1) || a.addedAt - b.addedAt);
    return [...named, ...rest.map(login => login.id)];
  }
  function outUntil(login) {
    const at = now();
    if (login.state !== 'ok') return Infinity;
    if (Number.isFinite(login.limitedUntil) && login.limitedUntil > at) return login.limitedUntil;
    if (login.week && login.week.usedPercent >= login.stop.week) return login.week.resetsAt ?? Infinity;
    if (login.fiveHour && login.fiveHour.usedPercent >= login.stop.fiveHour) return login.fiveHour.resetsAt ?? Infinity;
    return null;
  }
  const log = (login, action, user, machine, detail = '') => audit.push({ loginId: login.id, at: new Date(now()).toISOString(), action, login: login.name, actor: user.login, machine: machine.name ?? machine.id ?? '-', detail });

  function addLogin({ owner, name, provider = 'codex', auth = fakeLogin(), plan = 'team', group = null }) {
    const user = typeof owner === 'string' ? [...byToken.values()].find(item => lower(item.login) === lower(owner)) : owner;
    const login = { id: newId('l'), name, owner: { login: user.login, id: user.id }, provider, auth, plan, reset: 'never', stop: { week: 97, fiveHour: 97 },
      state: 'ok', week: null, fiveHour: null, accessExpiresAt: accessEnd(auth, now()), refreshOkAt: null, shares: new Map(), groupShares: new Set(),
      left: new Set(), limitedUntil: null, limitReason: null, addedAt: logins.size };
    if (group) login.groupShares.add(group);
    logins.set(login.id, login);
    return login;
  }

  const error = (status, code, message, extra = {}) => ({ status, body: { error: { code, message, ...extra } } });
  function route(method, parts, body, user, machine) {
    const [, resource, id, verb] = parts;
    if (resource === 'accounts' && parts.length === 2 && method === 'GET') {
      const invites = [...logins.values()].map(login => ({ login, rel: relation(login, user) })).filter(item => item.rel?.kind === 'invited')
        .map(({ login, rel }) => ({ id: login.id, name: login.name, owner: { login: login.owner.login }, via: rel.via }));
      return { status: 200, body: { logins: effectiveOrder(user).map(loginId => rowFor(logins.get(loginId), user)), invites, order: effectiveOrder(user),
        groups: [...groups.values()].filter(group => group.ownerId === user.id || inGroup(group, user)).map(groupView) } };
    }
    if (resource === 'accounts' && parts.length === 2 && method === 'POST') {
      if (!isObject(body) || !NAME.test(body.name ?? '') || body.provider !== 'codex' || typeof body.auth !== 'string') return error(400, 'invalid', 'The login needs a name, provider codex and a login.');
      let full;
      try { full = JSON.parse(body.auth).tokens.refresh_token; } catch { full = ''; }
      if (typeof full !== 'string' || !full) return error(400, 'invalid', `${body.name} is not a full login.`);
      if ([...logins.values()].some(login => login.owner.id === user.id && login.name === body.name)) return error(409, 'conflict', `You already have a login named ${body.name}.`);
      let group = null;
      if (body.group !== undefined) {
        group = [...groups.values()].find(item => item.ownerId === user.id && item.name === body.group);
        if (!group) return error(404, 'not_found', `You have no group named ${body.group}.`);
      }
      counts.fullLoginsReceived++;
      const login = addLogin({ owner: user, name: body.name, provider: body.provider, auth: body.auth, group: group?.id ?? null });
      log(login, 'add', user, machine);
      return { status: 201, body: rowFor(login, user) };
    }
    if (resource === 'accounts' && id === 'order' && method === 'PUT') {
      if (!isObject(body) || !Array.isArray(body.order)) return error(400, 'invalid', 'The order needs a list of ids.');
      orders.set(user.id, body.order.filter(item => logins.has(item) && canUse(logins.get(item), user)));
      return { status: 200, body: { order: effectiveOrder(user) } };
    }
    if (resource === 'groups' && parts.length === 2 && method === 'POST') {
      const withList = Array.isArray(body?.with) ? body.with : null, team = typeof body?.github === 'string' ? body.github : null;
      if (!NAME.test(body?.name ?? '') || (withList && withList.length && team) || (!withList?.length && !team) || (withList && !withList.every(name => GH_LOGIN.test(name))))
        return error(400, 'invalid', 'A group needs a name and one of with or github.');
      if ([...groups.values()].some(group => group.ownerId === user.id && group.name === body.name)) return error(409, 'conflict', `You already have a group named ${body.name}.`);
      const group = { id: newId('g'), name: body.name, owner: user.login, ownerId: user.id, members: team ? [] : withList.map(lower), github: team, accepted: new Set() };
      groups.set(group.id, group);
      return { status: 201, body: groupView(group) };
    }
    if (resource === 'copy' && parts.length === 2 && method === 'POST') {
      const skip = Array.isArray(body?.skip) ? body.skip : [];
      let ids = effectiveOrder(user).filter(loginId => logins.get(loginId).provider === (body?.provider ?? 'codex') && !pausedFor(user).has(loginId) && !skip.includes(loginId));
      if (body?.pin !== undefined) {
        if (!logins.has(body.pin) || !canUse(logins.get(body.pin), user)) return error(404, 'not_found', 'No such login.');
        ids = ids.filter(loginId => loginId === body.pin);
      }
      const ready = ids.find(loginId => outUntil(logins.get(loginId)) === null);
      if (!ready) {
        const waits = ids.map(loginId => ({ id: loginId, at: outUntil(logins.get(loginId)) })).filter(item => Number.isFinite(item.at)).sort((a, b) => a.at - b.at);
        return error(409, 'all_out', 'No login has quota now.', { earliest: waits[0] ?? null });
      }
      const login = logins.get(ready), copy = JSON.parse(login.auth);
      if (!options.copyWithRefresh) copy.tokens.refresh_token = '';
      counts.copies++;
      log(login, 'copy', user, machine);
      return { status: 200, body: { login: rowFor(login, user), auth: JSON.stringify(copy), expiresAt: login.accessExpiresAt, copyId: newId('c') } };
    }
    if (resource === 'machines' && method === 'GET' && parts.length === 2) return { status: 200, body: { machines: [...(machines.get(user.id)?.values() ?? [])] } };
    if (resource === 'machines' && method === 'DELETE' && parts.length === 3) return machines.get(user.id)?.delete(id) ? { status: 200, body: { removed: true } } : error(404, 'not_found', 'No such machine.');
    if (resource !== 'accounts' || !id) return error(404, 'not_found', 'No such path.');
    const login = logins.get(id);
    const rel = login ? relation(login, user) : null;
    if (!login || !rel) return error(404, 'not_found', 'No such login.');
    const own = rel.kind === 'own';
    if (method === 'DELETE' && parts.length === 3) {
      if (!own) return error(403, 'forbidden', `Only the owner can remove ${login.name}.`);
      logins.delete(id); log(login, 'remove', user, machine);
      return { status: 200, body: { removed: true } };
    }
    if (method === 'GET' && verb === 'log') {
      if (!own) return error(403, 'forbidden', `Only the owner can read the log of ${login.name}.`);
      return { status: 200, body: { rows: audit.filter(row => row.loginId === id).map(({ loginId, ...row }) => row) } };
    }
    if (method === 'PUT' && verb === 'settings') {
      if (!own) return error(403, 'forbidden', `Only the owner can change ${login.name}.`);
      if (body?.reset !== undefined) {
        if (!['never', 'ask', 'auto'].includes(body.reset)) return error(400, 'invalid', 'reset is never, ask or auto.');
        login.reset = body.reset;
      }
      if (isObject(body?.stop)) login.stop = { ...login.stop, ...body.stop };
      log(login, 'settings', user, machine);
      return { status: 200, body: rowFor(login, user) };
    }
    if (method !== 'POST') return error(404, 'not_found', 'No such path.');
    if (verb === 'pause' || verb === 'resume') {
      if (!canUse(login, user)) return error(403, 'forbidden', `You do not use ${login.name}.`);
      const set = paused.get(user.id) ?? new Set();
      if (verb === 'pause') set.add(id); else set.delete(id);
      paused.set(user.id, set); log(login, verb, user, machine);
      return { status: 200, body: rowFor(login, user) };
    }
    if (verb === 'share' || verb === 'unshare') {
      if (!own) return error(403, 'forbidden', `Only the owner can share ${login.name}.`);
      const names = Array.isArray(body?.with) ? body.with : [];
      if (!names.every(name => typeof name === 'string' && GH_LOGIN.test(name))) return error(400, 'invalid', 'with lists GitHub logins.');
      if (verb === 'share') {
        for (const name of names) if (!login.shares.has(lower(name))) login.shares.set(lower(name), { login: name, state: 'invited' });
        if (body?.group !== undefined) {
          const group = [...groups.values()].find(item => item.ownerId === user.id && item.name === body.group);
          if (!group) return error(404, 'not_found', `You have no group named ${body.group}.`);
          login.groupShares.add(group.id);
        }
      } else for (const name of names) login.shares.delete(lower(name));
      log(login, verb, user, machine, `with ${names.join(', ')}${body?.group ? ` group ${body.group}` : ''}`);
      return { status: 200, body: rowFor(login, user) };
    }
    if (verb === 'accept' || verb === 'leave') {
      if (own) return error(400, 'invalid', `${login.name} is your own login.`);
      const share = login.shares.get(lower(user.login));
      if (verb === 'accept') {
        if (rel.kind !== 'invited') return { status: 200, body: rowFor(login, user) };
        if (rel.via === 'user') share.state = 'accepted';
        else groups.get([...login.groupShares].find(groupId => groupOf(groupId)?.name === rel.via.slice(6))).accepted.add(lower(user.login));
        login.left.delete(lower(user.login));
      } else {
        if (share) login.shares.delete(lower(user.login));
        login.left.add(lower(user.login));
      }
      log(login, verb, user, machine);
      return { status: 200, body: rowFor(login, user) };
    }
    if (verb === 'usage') {
      if (!canUse(login, user)) return error(403, 'forbidden', `You do not use ${login.name}.`);
      for (const key of ['week', 'fiveHour', 'limitedUntil', 'limitReason']) if (body?.[key] !== undefined) login[key] = body[key];
      log(login, 'usage', user, machine);
      return { status: 200, body: rowFor(login, user) };
    }
    return error(404, 'not_found', 'No such path.');
  }

  const server = createServer((request, response) => {
    const chunks = [];
    let size = 0;
    request.on('data', chunk => { size += chunk.length; if (size <= 1024 * 1024) chunks.push(chunk); });
    request.on('end', () => {
      const url = new URL(request.url, 'http://fake.invalid');
      const at = url.pathname.indexOf('/v1/');
      const parts = at < 0 ? [] : url.pathname.slice(at + 1).split('/').map(decodeURIComponent);
      const header = String(request.headers.authorization ?? '');
      const user = header.startsWith('Bearer ') ? byToken.get(header.slice(7)) ?? null : null;
      const machine = { id: request.headers['x-pdd-machine'] ?? null, name: request.headers['x-pdd-machine-name'] ?? null };
      let body;
      try { body = chunks.length ? JSON.parse(Buffer.concat(chunks).toString('utf8')) : undefined; } catch { body = null; }
      const summary = isObject(body) && Object.hasOwn(body, 'auth') ? { ...body, auth: '[full login]' } : body;
      requests.push({ method: request.method, path: url.pathname, prefix: at < 0 ? null : url.pathname.slice(0, at), user: user?.login ?? null,
        bearer: header.startsWith('Bearer '), machine: machine.id, machineName: machine.name, userAgent: request.headers['user-agent'] ?? null,
        contentType: request.headers['content-type'] ?? null, body: summary });
      let reply;
      if (queued.length) reply = queued.shift();
      else if (!user) reply = error(401, 'forbidden', 'GitHub did not accept this login.');
      else if (parts[0] !== 'v1' || body === null) reply = error(400, 'invalid', 'The request is not JSON.');
      else {
        if (machine.id) {
          const own = machines.get(user.id) ?? new Map();
          own.set(machine.id, { id: machine.id, name: machine.name, lastSeen: now() });
          machines.set(user.id, own);
        }
        reply = route(request.method, parts, body, user, machine);
      }
      const text = typeof reply.raw === 'string' ? reply.raw : JSON.stringify(reply.body);
      response.writeHead(reply.status, { 'content-type': typeof reply.raw === 'string' ? 'text/plain' : 'application/json', ...(reply.headers ?? {}) });
      response.end(text);
    });
  });
  await new Promise(done => server.listen(0, '127.0.0.1', done));
  const url = `http://127.0.0.1:${server.address().port}/`;
  return {
    url, requests, audit, options, counts, logins, groups,
    addUser(user) { byToken.set(user.token, { login: user.login, id: Number(user.id) }); },
    addLogin(spec) { const login = addLogin(spec); return login.id; },
    setUsage(id, values) { Object.assign(logins.get(id), values); },
    // The next request gets this reply: { status, body } (JSON), or { status, raw, headers } (text).
    failNext(reply) { queued.push(reply); },
    close: () => new Promise(done => { server.closeAllConnections?.(); server.close(() => done()); }),
  };
}
