// Read the `-c key=value` overrides that a fake Codex program received, as Codex would.
// The decoder follows TOML 1.0 basic strings; it does not reuse the launcher's encoder.
import assert from 'node:assert/strict';

export function tomlBasicString(text) {
  assert.ok(text.length >= 2 && text.startsWith('"') && text.endsWith('"'), `not a TOML basic string: ${text}`);
  const body = text.slice(1, -1);
  let out = '';
  for (let i = 0; i < body.length; i++) {
    const c = body[i];
    assert.doesNotMatch(c, /[\x00-\x08\x0a-\x1f\x7f"]/, `raw ${JSON.stringify(c)} at ${i} is not allowed in a TOML basic string`);
    if (c !== '\\') { out += c; continue; }
    const e = body[++i];
    const simple = { b: '\b', t: '\t', n: '\n', f: '\f', r: '\r', '"': '"', '\\': '\\' }[e];
    if (simple !== undefined) { out += simple; continue; }
    const width = e === 'u' ? 4 : e === 'U' ? 8 : 0, hex = body.slice(i + 1, i + 1 + width);
    assert.ok(width && hex.length === width && /^[0-9A-Fa-f]+$/.test(hex), `bad TOML escape \\${e}`);
    const code = parseInt(hex, 16);
    assert.ok(code <= 0x10ffff && (code < 0xd800 || code > 0xdfff), `TOML escape is not a Unicode scalar value: ${hex}`);
    out += String.fromCodePoint(code); i += width;
  }
  return out;
}

// Split overrides into shell_environment_policy.set entries and the other keys.
// Basic strings and booleans are decoded; other values (inline tables) stay as text.
export function codexConfigs(argv) {
  const set = {}, config = {};
  for (let i = 0; i < argv.length; i++) {
    if (argv[i] !== '-c' && argv[i] !== '--config') continue;
    const text = argv[++i], at = text.indexOf('=');
    assert.ok(at > 0, `override without a key: ${text}`);
    const key = text.slice(0, at).trim(), raw = text.slice(at + 1).trim();
    const value = raw.startsWith('"') ? tomlBasicString(raw) : raw === 'true' ? true : raw === 'false' ? false : raw;
    const name = /^shell_environment_policy\.set\.([A-Za-z_][A-Za-z0-9_]*)$/.exec(key)?.[1];
    const target = name ? set : config, slot = name ?? key;
    assert.equal(Object.hasOwn(target, slot), false, `override ${key} appears twice`);
    target[slot] = value;
  }
  return { set, config };
}
