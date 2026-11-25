// Prompt: prompts/worker.prompt.md
export function runWorker(vault, audit, key, nextValue) {
  const existing = vault.read(key);
  if (nextValue !== undefined) vault.write(key, nextValue);
  audit.append({ key, hadExisting: Boolean(existing?.found) });
  return existing;
}
