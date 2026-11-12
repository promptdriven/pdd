// Generated from examples/native-replay/count-words.prompt.md.
export function countWords(text) {
  if (typeof text !== 'string') throw new TypeError('text must be a string');
  return text.trim() ? text.trim().split(/\s+/).length : 0;
}
