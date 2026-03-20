import React from 'react';
import {
  SYN_KEYWORD,
  SYN_STRING,
  SYN_TYPE,
  SYN_COMMENT,
  SYN_PROPERTY,
  SYN_BOOLEAN,
  SYN_REGEX,
  SYN_PUNCTUATION,
  SYN_PARAM,
  CODE_TEXT_COLOR,
} from './constants';

/**
 * A token produced by our simple syntax highlighter.
 */
export interface SyntaxToken {
  text: string;
  color: string;
}

const KEYWORDS = new Set([
  'function', 'const', 'let', 'var', 'return', 'if', 'else', 'for',
  'while', 'do', 'switch', 'case', 'break', 'continue', 'new', 'typeof',
  'import', 'export', 'from', 'default', 'class', 'extends', 'interface',
  'type', 'enum',
]);

const BOOLEANS = new Set(['true', 'false', 'null', 'undefined']);

/**
 * Tokenize a line of TypeScript-like code into colored spans.
 */
export function tokenizeLine(line: string): SyntaxToken[] {
  const tokens: SyntaxToken[] = [];
  let i = 0;

  while (i < line.length) {
    // Comments
    if (line.slice(i, i + 2) === '//') {
      tokens.push({ text: line.slice(i), color: SYN_COMMENT });
      return tokens;
    }

    // Strings (single or double quote)
    if (line[i] === "'" || line[i] === '"') {
      const quote = line[i];
      let j = i + 1;
      while (j < line.length && line[j] !== quote) {
        if (line[j] === '\\') j++; // skip escaped char
        j++;
      }
      j++; // include closing quote
      tokens.push({ text: line.slice(i, j), color: SYN_STRING });
      i = j;
      continue;
    }

    // Template literals
    if (line[i] === '`') {
      let j = i + 1;
      while (j < line.length && line[j] !== '`') {
        if (line[j] === '\\') j++;
        j++;
      }
      j++;
      tokens.push({ text: line.slice(i, j), color: SYN_STRING });
      i = j;
      continue;
    }

    // Regex literals (simple heuristic)
    if (line[i] === '/' && i > 0 && /[=(,]\s*$/.test(line.slice(0, i))) {
      let j = i + 1;
      while (j < line.length && line[j] !== '/') {
        if (line[j] === '\\') j++;
        j++;
      }
      j++; // closing slash
      // flags
      while (j < line.length && /[gimsuy]/.test(line[j])) j++;
      tokens.push({ text: line.slice(i, j), color: SYN_REGEX });
      i = j;
      continue;
    }

    // Words (identifiers, keywords)
    if (/[a-zA-Z_$]/.test(line[i])) {
      let j = i;
      while (j < line.length && /[\w$]/.test(line[j])) j++;
      const word = line.slice(i, j);

      if (KEYWORDS.has(word)) {
        tokens.push({ text: word, color: SYN_KEYWORD });
      } else if (BOOLEANS.has(word)) {
        tokens.push({ text: word, color: SYN_BOOLEAN });
      } else if (j < line.length && line[j] === ':') {
        // property name before colon
        tokens.push({ text: word, color: SYN_PROPERTY });
      } else if (j < line.length && line[j] === '(') {
        // function call
        tokens.push({ text: word, color: SYN_PROPERTY });
      } else if (i > 0 && line[i - 1] === ':' && /\s/.test(line[i - 2] || '')) {
        // type annotation
        tokens.push({ text: word, color: SYN_TYPE });
      } else if (i > 0 && line.slice(0, i).includes('(') && !line.slice(0, i).includes(')')) {
        // inside function params
        tokens.push({ text: word, color: SYN_PARAM });
      } else {
        tokens.push({ text: word, color: CODE_TEXT_COLOR });
      }
      i = j;
      continue;
    }

    // Numbers
    if (/\d/.test(line[i])) {
      let j = i;
      while (j < line.length && /[\d.]/.test(line[j])) j++;
      tokens.push({ text: line.slice(i, j), color: SYN_BOOLEAN });
      i = j;
      continue;
    }

    // Spread operator
    if (line.slice(i, i + 3) === '...') {
      tokens.push({ text: '...', color: SYN_KEYWORD });
      i += 3;
      continue;
    }

    // Punctuation / operators / whitespace
    tokens.push({ text: line[i], color: SYN_PUNCTUATION });
    i++;
  }

  return tokens;
}

interface SyntaxLineProps {
  line: string;
  /** If set, only show the first N characters */
  visibleChars?: number;
}

/**
 * Renders a single line of syntax-highlighted code.
 */
export const SyntaxLine: React.FC<SyntaxLineProps> = ({ line, visibleChars }) => {
  const tokens = tokenizeLine(line);
  const showAll = visibleChars === undefined;

  let charCount = 0;
  const rendered: React.ReactNode[] = [];

  for (let t = 0; t < tokens.length; t++) {
    const token = tokens[t];
    if (!showAll && charCount >= visibleChars!) break;

    let text = token.text;
    if (!showAll) {
      const remaining = visibleChars! - charCount;
      if (text.length > remaining) {
        text = text.slice(0, remaining);
      }
    }

    rendered.push(
      <span key={t} style={{ color: token.color }}>
        {text}
      </span>
    );
    charCount += token.text.length;
  }

  return <>{rendered}</>;
};
