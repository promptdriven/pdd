// A TOML basic string: JSON escapes plus DEL, which TOML also forbids raw.
export const tomlString = value => JSON.stringify(String(value)).replaceAll('\x7f', '\\u007f');
