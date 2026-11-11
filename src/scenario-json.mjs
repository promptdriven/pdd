// Generated from prompts/cli/scenario-json.prompt.md (sha256: 80fefc699838e7c089f836758490d434534a92498fef604139af902f20cd0bbf).
// Exact whole numbers in Runtime scenario files: read, write and compare without rounding.

const EXACT_INTEGER = /^-?(?:0|[1-9][0-9]*)$/;
const plain = value => value !== null && typeof value === 'object' && !Array.isArray(value)
  && (Object.getPrototypeOf(value) === Object.prototype || Object.getPrototypeOf(value) === null);
const pointerToken = key => String(key).replaceAll('~', '~0').replaceAll('/', '~1');
const fromToken = token => token.replaceAll('~1', '/').replaceAll('~0', '~');
const inexact = (Kind, message) => Object.assign(new Kind(message), { code: 'scenario-number-inexact' });

export function parseScenarioJson(text) {
  return JSON.parse(text, (_key, value, context) =>
    typeof value === 'number' && !Number.isSafeInteger(value) && typeof context?.source === 'string' && EXACT_INTEGER.test(context.source)
      ? BigInt(context.source) : value);
}

export function stringifyScenarioJson(value, space) {
  return JSON.stringify(value, (_key, item) => typeof item === 'bigint' ? JSON.rawJSON(item.toString()) : item, space);
}

export function exactNumber(value) {
  if (typeof value === 'number') return value;
  if (typeof value !== 'bigint') throw inexact(TypeError, `Expected a Number or an exact integer, got ${typeof value}.`);
  const nearest = Number(value);
  if (Number.isFinite(nearest) && BigInt(nearest) === value) return nearest;
  throw inexact(RangeError, `${value} has no exact JavaScript Number; the nearest Number is ${Number.isFinite(nearest) ? BigInt(nearest) : nearest}.`);
}

export function exactValue(value) {
  if (typeof value === 'number') return Number.isInteger(value) && !Number.isSafeInteger(value) ? BigInt(value) : value;
  if (typeof value === 'bigint') return value >= BigInt(Number.MIN_SAFE_INTEGER) && value <= BigInt(Number.MAX_SAFE_INTEGER) ? Number(value) : value;
  if (Array.isArray(value)) return value.map(exactValue);
  if (plain(value)) return Object.fromEntries(Object.entries(value).map(([key, item]) => [key, exactValue(item)]));
  return value;
}

// A number token with a fraction or exponent whose digits change when it is read as a Number.
class Read { constructor(source, value) { this.source = source; this.value = value; } }
const normalNumber = text => {
  const match = /^(-?)([0-9]+)(?:\.([0-9]+))?(?:[eE]([+-]?[0-9]+))?$/.exec(text);
  if (!match) return text;
  const digits = (match[2] + (match[3] ?? '')).replace(/^0+/, '');
  if (!digits) return '0';
  const zeros = /0*$/.exec(digits)[0].length;
  return `${match[1]}${digits.slice(0, digits.length - zeros)}e${BigInt(match[4] ?? 0) - BigInt((match[3] ?? '').length) + BigInt(zeros)}`;
};
export function roundedNumberTokens(text) {
  const doc = JSON.parse(text, (_key, value, context) => typeof value === 'number' && typeof context?.source === 'string'
    && !EXACT_INTEGER.test(context.source) && normalNumber(context.source) !== normalNumber(String(value)) ? new Read(context.source, value) : value);
  const found = [];
  const visit = (item, path) => {
    if (item instanceof Read) found.push({ path, source: item.source, value: item.value });
    else if (Array.isArray(item)) item.forEach((member, index) => visit(member, [...path, index]));
    else if (plain(item)) for (const [key, member] of Object.entries(item)) visit(member, [...path, key]);
  };
  visit(doc, []);
  return found;
}

export function exactIntegerLeaves(value) {
  const leaves = [];
  const visit = (item, pointer) => {
    if (typeof item === 'bigint') leaves.push({ pointer, value: item.toString() });
    else if (Array.isArray(item)) item.forEach((member, index) => visit(member, `${pointer}/${index}`));
    else if (plain(item)) for (const [key, member] of Object.entries(item)) visit(member, `${pointer}/${pointerToken(key)}`);
  };
  visit(value, '');
  return leaves;
}

export function jsonSafe(value) {
  if (typeof value === 'bigint') return Number(value);
  if (Array.isArray(value)) return value.map(jsonSafe);
  if (plain(value)) return Object.fromEntries(Object.entries(value).map(([key, item]) => [key, jsonSafe(item)]));
  return value;
}

export function withExactIntegers(value, leaves) {
  let copy = structuredClone(value);
  for (const leaf of Array.isArray(leaves) ? leaves : []) {
    if (typeof leaf?.pointer !== 'string' || typeof leaf?.value !== 'string' || !EXACT_INTEGER.test(leaf.value)) continue;
    const exact = BigInt(leaf.value);
    if (leaf.pointer === '') { if (copy === Number(exact)) copy = exact; continue; }
    if (!leaf.pointer.startsWith('/')) continue;
    const tokens = leaf.pointer.slice(1).split('/').map(fromToken), last = tokens.pop();
    let holder = copy;
    for (const token of tokens) holder = (Array.isArray(holder) || plain(holder)) && Object.hasOwn(holder, token) ? holder[token] : undefined;
    if ((Array.isArray(holder) || plain(holder)) && Object.hasOwn(holder, last) && holder[last] === Number(exact)) holder[last] = exact;
  }
  return copy;
}
