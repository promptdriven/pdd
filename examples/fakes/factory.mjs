// Prompt: examples/fakes/factory.prompt.md

export function createGreeter(prefix) {
  return { greet(name) { return { text: prefix + name }; } };
}
