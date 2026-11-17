// Generated from prompts/cli/saved-value-warning.prompt.md.
const terminalText = value => value.replace(/[^\x20-\x7e]/g, char => '\\u' + char.charCodeAt(0).toString(16).padStart(4, '0'));
const markdownText = value => terminalText(value)
  .replaceAll('pdd-workflow:', 'pdd-workflow\\u003a').replaceAll('pdd-product:', 'pdd-product\\u003a')
  .replace(/[\\`*_[\]()|]/g, '\\$&').replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('/', '&#47;');

export function formatSavedValueWarning({ vector, reason, path, before, after, format = 'markdown' }) {
  const display = format === 'plain' ? terminalText : markdownText;
  const identity = value => display(JSON.stringify(String(value)).slice(1, -1));
  const detail = reason ? identity(reason) : `${identity(path)} ${display(before)} -> ${display(after)}`;
  return `warning: Saved test values changed: ${identity(vector)} ${detail}`;
}
