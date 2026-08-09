/**
 * Include Tag Analyzer for CodeMirror
 * Detects <include> tags at cursor position and analyzes their token content
 */

import { EditorState } from '@codemirror/state';

export interface IncludeTagInfo {
  from: number;       // Start position of the tag
  to: number;         // End position of the tag
  path: string;       // The file path inside the tag
  tagType: 'include' | 'include-many' | 'shell' | 'web';
}

/**
 * Find an include-type tag at or near the cursor position
 * Supports: <include>, <include-many>, <shell>, <web>
 */
export function findIncludeAtCursor(state: EditorState): IncludeTagInfo | null {
  const pos = state.selection.main.head;
  const doc = state.doc.toString();

  // Define tag patterns we want to analyze
  const tagPatterns = [
    { regex: /<include>(.*?)<\/include>/g, type: 'include' as const },
    { regex: /<include-many>(.*?)<\/include-many>/g, type: 'include-many' as const },
    { regex: /<shell>(.*?)<\/shell>/g, type: 'shell' as const },
    { regex: /<web>(.*?)<\/web>/g, type: 'web' as const },
  ];

  // Search for each tag type
  for (const { regex, type } of tagPatterns) {
    let match;
    // Reset regex lastIndex
    regex.lastIndex = 0;

    while ((match = regex.exec(doc)) !== null) {
      const from = match.index;
      const to = match.index + match[0].length;

      // Check if cursor is within this tag
      if (pos >= from && pos <= to) {
        return {
          from,
          to,
          path: match[1].trim(),
          tagType: type,
        };
      }
    }
  }

  return null;
}

/**
 * Get the line containing an include tag for display purposes
 */
export function getIncludeTagLine(state: EditorState, info: IncludeTagInfo): string {
  const line = state.doc.lineAt(info.from);
  return line.text;
}

/**
 * Parse include-many tag to get individual file paths
 */
export function parseIncludeManyPaths(path: string): string[] {
  return path.split(',').map(p => p.trim()).filter(Boolean);
}
