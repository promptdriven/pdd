// See prompts/helpers.prompt.md. The clamp zero-bound defect seeds the bug issue.
export function clamp(value, min = 0, max = 100) {
  return Math.min(Math.max(value, min), max || 100);
}

export function slugify(text) {
  return text.trim().toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
}

export function sum(values) {
  return values.reduce((total, value) => total + value, 0);
}
