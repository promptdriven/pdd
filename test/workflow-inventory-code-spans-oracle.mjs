// Independent report-format oracle from the approved contract. It deliberately
// encodes characters one at a time and searches forbidden fence lengths rather
// than copying the formatter's JSON replacement / longest-run implementation.
export function jsonLiteral(value) {
  const short = new Map([['\t', '\\t'], ['\n', '\\n'], ['\r', '\\r'], ['\b', '\\b'], ['\f', '\\f'], ['"', '\\"'], ['\\', '\\\\']]);
  let result = '"';
  for (const char of value) {
    const point = char.codePointAt(0);
    const escaped = point < 32 || (point >= 127 && point <= 159) ||
      [0x61c, 0x200e, 0x200f].includes(point) ||
      (point >= 0x202a && point <= 0x202e) || (point >= 0x2066 && point <= 0x2069);
    result += short.get(char) ?? (escaped ? `\\u${point.toString(16).padStart(4, '0')}` : char);
  }
  return result + '"';
}
export function codeLiteral(value) {
  const payload = jsonLiteral(value);
  let fence = '`';
  while (payload.includes(fence)) fence += '`';
  return fence + payload + fence;
}
export function pathLiteral(value) {
  const entities = new Map([['&', 38], ['<', 60], ['>', 62], ['`', 96], ['|', 124], [':', 58], ['@', 64], ['#', 35]]);
  return [...jsonLiteral(value)].map(char => entities.has(char) ? `&#${entities.get(char)};` : char).join('');
}
export const disclaimer = 'Static inventory only; tests were not run.\n';
