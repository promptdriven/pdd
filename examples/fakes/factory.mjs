// Generated from examples/fakes/factory.prompt.md (sha256: 63c1a8967a57cd871ad1e4311ea1a66e1afa99c88eb37a3f3d686b69b9cd20d6).
export function createGreeter(prefix) {
  return { greet(name) { return { text: prefix + name }; } };
}
