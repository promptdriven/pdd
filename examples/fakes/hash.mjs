// Prompt: examples/fakes/hash.prompt.md

export function fingerprint(compute, text) {
  return compute.hash_utf8({ text });
}
