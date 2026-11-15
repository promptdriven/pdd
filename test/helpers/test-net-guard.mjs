import dns from 'node:dns';
import net from 'node:net';
import tls from 'node:tls';

export const NET_BLOCKED_CODE = 'ERR_PDD_OFFLINE_TEST_NET_BLOCKED';

export function isNetGuardBypassed(env = process.env) {
  return env?.PDD_ALLOW_NET === '1' || env?.PDD_LIVE_CANARY === '1';
}

export function isAllowedOfflineHost(rawHost) {
  if (rawHost === undefined || rawHost === null) return true;
  const trimmed = String(rawHost).trim();
  if (!trimmed) return true;
  const unbracketed = trimmed.startsWith('[') && trimmed.endsWith(']') ? trimmed.slice(1, -1) : trimmed;
  const host = unbracketed.toLowerCase().replace(/\.$/, '').split('%')[0];
  if (!host) return true;
  if (host === 'localhost' || host.endsWith('.localhost')) return true;
  if (host === '0.0.0.0' || /^127(?:\.\d{1,3}){3}$/.test(host)) return true;
  if (host === '::1' || host === '0:0:0:0:0:0:0:1' || host === '::' || host === '0:0:0:0:0:0:0:0') return true;
  if (/^::ffff:(?:127(?:\.\d{1,3}){3}|0\.0\.0\.0)$/.test(host)) return true;
  return false;
}

export function createOfflineNetBlockedError(target, detail = '') {
  const label = target ? String(target) : 'external host';
  const suffix = detail ? ` (${detail})` : '';
  const err = new Error(
    `Offline unit-test network guard blocked outbound connection to ${label}${suffix}. ` +
    `Use loopback (127.0.0.1, ::1, localhost, Unix socket) or set PDD_ALLOW_NET=1 / PDD_LIVE_CANARY=1 for explicit live tests.`,
  );
  err.code = NET_BLOCKED_CODE;
  return err;
}

function extractConnectTarget(args) {
  const first = Array.isArray(args[0]) ? args[0][0] : args[0];
  if (typeof first === 'string' && Number.isNaN(Number(first))) {
    return { ipc: true, host: null, port: null };
  }
  if (first !== null && typeof first === 'object') {
    if (typeof first.path === 'string' && first.path.length > 0) return { ipc: true, host: null, port: null };
    if (Number.isInteger(first.fd)) return { ipc: true, host: null, port: null };
    return { ipc: false, host: first.host ?? first.hostname ?? first.servername ?? null, port: first.port ?? null };
  }
  const host = typeof args[1] === 'string' ? args[1] : null;
  return { ipc: false, host, port: first ?? null };
}

const GUARD_SYMBOL = Symbol.for('pdd.offlineTestNetGuardInstalled');

export function installOfflineNetGuard() {
  if (globalThis[GUARD_SYMBOL]) return;
  globalThis[GUARD_SYMBOL] = true;

  const origSocketConnect = net.Socket.prototype.connect;
  net.Socket.prototype.connect = function guardedSocketConnect(...args) {
    if (!isNetGuardBypassed()) {
      const target = extractConnectTarget(args);
      if (!target.ipc && !isAllowedOfflineHost(target.host)) {
        const label = target.port ? `${target.host}:${target.port}` : String(target.host);
        const err = createOfflineNetBlockedError(label, 'net.Socket.connect');
        process.nextTick(() => this.destroy(err));
        return this;
      }
    }
    return origSocketConnect.apply(this, args);
  };

  const origTlsConnect = tls.connect;
  tls.connect = function guardedTlsConnect(...args) {
    if (!isNetGuardBypassed()) {
      const first = args[0];
      const hasExistingSocket = first !== null && typeof first === 'object' && Boolean(first.socket);
      if (!hasExistingSocket) {
        const target = extractConnectTarget(args);
        if (!target.ipc && !isAllowedOfflineHost(target.host)) {
          const sock = new tls.TLSSocket(new net.Socket());
          const label = target.port ? `${target.host}:${target.port}` : String(target.host);
          const err = createOfflineNetBlockedError(label, 'tls.connect');
          process.nextTick(() => sock.destroy(err));
          return sock;
        }
      }
    }
    return origTlsConnect.apply(this, args);
  };

  const origDnsLookup = dns.lookup;
  dns.lookup = function guardedDnsLookup(hostname, options, callback) {
    const cb = typeof options === 'function' ? options : callback;
    if (!isNetGuardBypassed() && !isAllowedOfflineHost(hostname)) {
      const err = createOfflineNetBlockedError(hostname, 'dns.lookup');
      if (typeof cb === 'function') process.nextTick(() => cb(err));
      return undefined;
    }
    return origDnsLookup.call(this, hostname, options, callback);
  };

  if (dns.promises && typeof dns.promises.lookup === 'function') {
    const origPromisesLookup = dns.promises.lookup.bind(dns.promises);
    dns.promises.lookup = async function guardedPromisesLookup(hostname, options) {
      if (!isNetGuardBypassed() && !isAllowedOfflineHost(hostname)) {
        throw createOfflineNetBlockedError(hostname, 'dns.promises.lookup');
      }
      return origPromisesLookup(hostname, options);
    };
  }

  if (typeof globalThis.fetch === 'function') {
    const origFetch = globalThis.fetch;
    globalThis.fetch = async function guardedFetch(input, init) {
      if (!isNetGuardBypassed()) {
        let parsed = null;
        try {
          if (input instanceof URL) parsed = input;
          else if (typeof input === 'string') parsed = new URL(input);
          else if (input && typeof input.url === 'string') parsed = new URL(input.url);
        } catch {
          parsed = null;
        }
        if (parsed && (parsed.protocol === 'http:' || parsed.protocol === 'https:') && !isAllowedOfflineHost(parsed.hostname)) {
          throw createOfflineNetBlockedError(parsed.host || parsed.hostname, 'fetch');
        }
      }
      return origFetch.call(this, input, init);
    };
  }
}

installOfflineNetGuard();
