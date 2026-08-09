/**
 * PDD Directive autocomplete extension for CodeMirror 6
 * Provides autocomplete suggestions for PDD directives like <include>, <pdd>, <shell>, etc.
 */

import { autocompletion, CompletionContext, Completion, acceptCompletion } from '@codemirror/autocomplete';
import { EditorView, keymap } from '@codemirror/view';
import { PDD_DIRECTIVES, CATEGORY_LABELS } from './pddDirectives';

/**
 * Autocomplete source for PDD directives
 * Triggers when user types '<' followed by optional characters
 */
function pddDirectiveCompletions(context: CompletionContext) {
  // Check for explicit activation (Ctrl+Space) or if we should trigger
  const explicit = context.explicit;

  // Get the word/text before cursor - match '<' followed by word chars
  const word = context.matchBefore(/<[\w-]*/);

  // Also check the character right before cursor
  const charBefore = context.state.sliceDoc(context.pos - 1, context.pos);

  // Determine if we should show completions
  let from = context.pos;
  let prefix = '';

  if (word && word.text.length > 0) {
    // User has typed '<' followed by optional characters
    from = word.from;
    prefix = word.text.slice(1).toLowerCase(); // Remove '<' for filtering

    // Don't trigger for closing tags like </
    const textBefore = context.state.sliceDoc(Math.max(0, word.from - 1), word.from);
    if (textBefore === '/') return null;
  } else if (charBefore === '<' || explicit) {
    // User just typed '<' or explicitly triggered with Ctrl+Space
    if (charBefore === '<') {
      from = context.pos - 1;
    } else {
      // Check if there's a < somewhere before on this line
      const line = context.state.doc.lineAt(context.pos);
      const lineText = line.text.slice(0, context.pos - line.from);
      const lastAngle = lineText.lastIndexOf('<');
      if (lastAngle >= 0) {
        from = line.from + lastAngle;
        prefix = lineText.slice(lastAngle + 1).toLowerCase();
      } else if (!explicit) {
        return null;
      }
    }
  } else {
    // No trigger condition met
    return null;
  }

  // Filter and map directives to completions
  const options: Completion[] = PDD_DIRECTIVES
    .filter(d => d.tag.toLowerCase().startsWith(prefix))
    .map(d => ({
      label: d.tag,
      type: 'keyword',
      detail: CATEGORY_LABELS[d.category],
      info: `${d.description}\n\nSyntax: ${d.syntax}\nExample: ${d.example}`,
      apply: (view: EditorView, _completion: Completion, from: number, to: number) => {
        // Insert full tag with cursor positioned inside
        const insertText = d.hasClosingTag
          ? `<${d.tag}></${d.tag}>`
          : `<${d.tag}/>`;

        // Calculate cursor position (after opening tag, before content)
        const cursorPos = from + d.tag.length + 2; // +2 for '<' and '>'

        view.dispatch({
          changes: { from, to, insert: insertText },
          selection: { anchor: cursorPos }
        });
      },
      boost: d.category === 'include' ? 2 : d.category === 'dynamic' ? 1 : 0,
    }));

  if (options.length === 0) return null;

  return {
    from,
    options,
    filter: false, // We already filtered
  };
}

/**
 * Theme extension for autocomplete popup styling
 */
const autocompleteTheme = EditorView.theme({
  '.cm-tooltip.cm-tooltip-autocomplete': {
    backgroundColor: '#1e293b',
    border: '1px solid #334155',
    borderRadius: '8px',
    boxShadow: '0 10px 25px -5px rgba(0, 0, 0, 0.4)',
    overflow: 'hidden',
  },
  '.cm-tooltip.cm-tooltip-autocomplete > ul': {
    fontFamily: 'inherit',
    maxHeight: '280px',
  },
  '.cm-tooltip.cm-tooltip-autocomplete > ul > li': {
    padding: '6px 12px',
    display: 'flex',
    alignItems: 'center',
    gap: '8px',
  },
  '.cm-tooltip.cm-tooltip-autocomplete > ul > li[aria-selected]': {
    backgroundColor: '#3b82f6',
    color: 'white',
  },
  '.cm-completionLabel': {
    color: '#60a5fa',
    fontWeight: '500',
  },
  '.cm-tooltip.cm-tooltip-autocomplete > ul > li[aria-selected] .cm-completionLabel': {
    color: 'white',
  },
  '.cm-completionDetail': {
    color: '#94a3b8',
    fontSize: '11px',
    marginLeft: 'auto',
    fontStyle: 'normal',
  },
  '.cm-tooltip.cm-tooltip-autocomplete > ul > li[aria-selected] .cm-completionDetail': {
    color: 'rgba(255, 255, 255, 0.8)',
  },
  '.cm-completionInfo': {
    backgroundColor: '#1e293b',
    border: '1px solid #334155',
    borderRadius: '8px',
    padding: '12px',
    marginLeft: '4px',
    maxWidth: '350px',
  },
});

/**
 * Creates the PDD autocomplete extension for CodeMirror
 * Use this in your editor's extensions array
 */
export function pddAutocompleteExtension() {
  return [
    autocompletion({
      override: [pddDirectiveCompletions],
      icons: false,
      optionClass: () => 'cm-pdd-completion',
      activateOnTyping: true,
      activateOnTypingDelay: 0,  // Trigger immediately
    }),
    // Add Tab key binding to accept completion
    keymap.of([
      { key: "Tab", run: acceptCompletion },
    ]),
    autocompleteTheme,
  ];
}
