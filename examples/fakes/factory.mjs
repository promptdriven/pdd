// Generated from examples/fakes/factory.prompt.md (sha256: 12ebaa807b06b0a97137d6434ff511c693a10cba8d07d8d9df4a49152f070813).
export function createGreeter(prefix) {
  return { greet(name) { return { text: prefix + name }; } };
}
