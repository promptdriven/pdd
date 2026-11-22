// Generated from prompts/cli/login-pool.prompt.md.
// TOML codec and Codex gateway-config stripping helpers (parser injected by login-pool.mjs).
import { CloudAccountsError } from './cloud-error.mjs';

export const CODEX_GATEWAY_PROVIDER_ID = 'pdd_codex_gateway';
const INLINE_TOML_TABLE_KEYS = new Set(['http_headers', 'env_http_headers', 'filters', 'set']);
const MANAGED_CODEX_GATEWAY_RE = /\/v1\/(?:accounts\/)?codex-gateway(?:\/|$)/i;

let tomlParserFn = null;

export function registerTomlParser(fn) {
  if (typeof fn === 'function') tomlParserFn = fn;
}

export function parseTomlText(raw) {
  if (typeof tomlParserFn !== 'function') {
    throw new CloudAccountsError('TOML parser is not registered; load via src/login-pool.mjs.', { code: 'toml_parser_unregistered' });
  }
  return tomlParserFn(raw);
}

export const isTomlTable = value => value !== null
  && typeof value === 'object'
  && !Array.isArray(value)
  && !(value instanceof Date)
  && typeof value.toISOString !== 'function';

export const formatTomlKey = key => (/^[A-Za-z0-9_-]+$/.test(key) ? key : JSON.stringify(key));

export function formatTomlValue(value) {
  if (typeof value === 'string') return JSON.stringify(value);
  if (typeof value === 'boolean') return value ? 'true' : 'false';
  if (typeof value === 'bigint') return String(value);
  if (typeof value === 'number') {
    if (Number.isFinite(value)) return String(value);
    if (Number.isNaN(value)) return 'nan';
    return value > 0 ? 'inf' : '-inf';
  }
  if (value instanceof Date || typeof value?.toISOString === 'function') return value.toISOString();
  if (Array.isArray(value)) return `[${value.map(formatTomlValue).join(', ')}]`;
  if (isTomlTable(value)) {
    const pairs = Object.entries(value)
      .filter(([, v]) => v !== undefined && v !== null)
      .map(([k, v]) => `${formatTomlKey(k)} = ${formatTomlValue(v)}`);
    return pairs.length ? `{ ${pairs.join(', ')} }` : '{}';
  }
  return JSON.stringify(String(value));
}

function isInlineLeafMap(key, value, depth) {
  return depth >= 1
    && INLINE_TOML_TABLE_KEYS.has(key)
    && isTomlTable(value)
    && Object.values(value).every(v => v === undefined || v === null || (!isTomlTable(v) && !Array.isArray(v)));
}

export function parseCodexTomlQuiet(text) {
  if (typeof text !== 'string' || !text.trim()) return null;
  try {
    const parsed = parseTomlText(text);
    return isTomlTable(parsed) ? parsed : null;
  } catch (err) {
    if (err?.code === 'toml_parser_unregistered') throw err;
    return null;
  }
}

export function readCodexTomlQuiet(fs, filePath) {
  if (typeof filePath !== 'string' || !filePath) return null;
  try {
    return parseCodexTomlQuiet(fs.readFileSync(filePath, 'utf8'));
  } catch (err) {
    if (err?.code === 'toml_parser_unregistered') throw err;
    return null;
  }
}

export function readCodexTomlObject(fs, configPath, { strict = true } = {}) {
  let raw;
  try {
    raw = fs.readFileSync(configPath, 'utf8');
  } catch (error) {
    if (error?.code === 'ENOENT' || !strict) return { exists: false, data: {} };
    throw error;
  }
  try {
    const parsed = parseTomlText(raw);
    return { exists: true, data: isTomlTable(parsed) ? parsed : {} };
  } catch (err) {
    if (err?.code === 'toml_parser_unregistered') throw err;
    if (!strict) return { exists: true, data: {} };
    throw new CloudAccountsError(`${configPath} contains malformed TOML; fix it before updating Codex Cloud accounts.`, { code: 'invalid_codex_config' });
  }
}

export function serializeTomlConfig(root, fileLabel = 'config.toml') {
  const blocks = [];
  const visit = (table, path) => {
    const scalars = [], subtables = [], tableArrays = [];
    for (const [key, val] of Object.entries(table)) {
      if (val === undefined || val === null) continue;
      if (Array.isArray(val) && val.length > 0 && val.every(isTomlTable)) tableArrays.push([key, val]);
      else if (isTomlTable(val) && !isInlineLeafMap(key, val, path.length)) subtables.push([key, val]);
      else scalars.push([key, val]);
    }
    if (path.length === 0) {
      if (scalars.length > 0) blocks.push(scalars.map(([k, v]) => `${formatTomlKey(k)} = ${formatTomlValue(v)}`).join('\n'));
    } else if (scalars.length > 0 || (subtables.length === 0 && tableArrays.length === 0)) {
      const header = `[${path.map(formatTomlKey).join('.')}]`;
      blocks.push([header, ...scalars.map(([k, v]) => `${formatTomlKey(k)} = ${formatTomlValue(v)}`)].join('\n'));
    }
    for (const [key, sub] of subtables) visit(sub, [...path, key]);
    for (const [key, list] of tableArrays) {
      const arrPath = [...path, key];
      const header = `[[${arrPath.map(formatTomlKey).join('.')}]]`;
      for (const item of list) {
        const itemScalars = [], itemSubs = [];
        for (const [ik, iv] of Object.entries(item)) {
          if (iv === undefined || iv === null) continue;
          if (isTomlTable(iv) && !isInlineLeafMap(ik, iv, arrPath.length)) itemSubs.push([ik, iv]);
          else itemScalars.push([ik, iv]);
        }
        blocks.push([header, ...itemScalars.map(([k, v]) => `${formatTomlKey(k)} = ${formatTomlValue(v)}`)].join('\n'));
        for (const [sk, sv] of itemSubs) visit(sv, [...arrPath, sk]);
      }
    }
  };
  visit(root, []);
  const text = blocks.length ? `${blocks.join('\n\n')}\n` : '';
  try {
    parseTomlText(text);
  } catch {
    throw new CloudAccountsError(`Failed to serialize valid TOML for ${fileLabel}.`, { code: 'invalid_codex_config' });
  }
  return text;
}

export function isManagedCodexGatewayUrl(value) {
  return typeof value === 'string' && MANAGED_CODEX_GATEWAY_RE.test(value.trim());
}

export function stripGatewayFromTomlObject(configData, previousModelProvider = null) {
  const hasGatewaySection = isTomlTable(configData?.model_providers) && Object.hasOwn(configData.model_providers, CODEX_GATEWAY_PROVIDER_ID);
  const hasGatewayProvider = configData?.model_provider === CODEX_GATEWAY_PROVIDER_ID;
  const hasGatewayOpenaiBaseUrl = isManagedCodexGatewayUrl(configData?.openai_base_url);
  const hasGatewayChatgptBaseUrl = isManagedCodexGatewayUrl(configData?.chatgpt_base_url);
  const wasGatewayManaged = hasGatewaySection || hasGatewayProvider || hasGatewayOpenaiBaseUrl || hasGatewayChatgptBaseUrl;
  const nextData = { ...(isTomlTable(configData) ? configData : {}) };
  if (isTomlTable(nextData.model_providers)) {
    const nextProviders = { ...nextData.model_providers };
    delete nextProviders[CODEX_GATEWAY_PROVIDER_ID];
    if (Object.keys(nextProviders).length > 0) nextData.model_providers = nextProviders;
    else delete nextData.model_providers;
  }
  if (hasGatewayOpenaiBaseUrl) delete nextData.openai_base_url;
  if (hasGatewayChatgptBaseUrl) delete nextData.chatgpt_base_url;
  const priorProvider = typeof previousModelProvider === 'string' && previousModelProvider.trim() && previousModelProvider.trim() !== CODEX_GATEWAY_PROVIDER_ID
    ? previousModelProvider.trim()
    : null;
  if (nextData.model_provider === CODEX_GATEWAY_PROVIDER_ID) {
    if (priorProvider) nextData.model_provider = priorProvider;
    else delete nextData.model_provider;
  } else if (wasGatewayManaged && !nextData.model_provider && priorProvider) {
    nextData.model_provider = priorProvider;
  }
  return { changed: wasGatewayManaged, nextData };
}
