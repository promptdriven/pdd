// Prompt: examples/fakes/files.prompt.md

export function readNote(files, path) {
  return files.read({ path });
}
