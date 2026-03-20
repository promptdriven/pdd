import React from 'react';
import {
  CODE_TEXT_COLOR,
  SYN_KEYWORD,
  SYN_TYPE,
  SYN_STRING,
  SYN_IDENTIFIER,
  SYN_OPERATOR,
  SYN_COMMENT,
  SYN_BOOLEAN,
  SYN_REGEX,
  SYN_NUMBER,
  CODE_FONT_SIZE,
  LINE_HEIGHT,
  GUTTER_WIDTH,
  CODE_LEFT_PADDING,
  LINE_NUMBER_COLOR,
} from './constants';

// ── Token types and tokenizer ───────────────────────────────────────────────

interface Token {
  text: string;
  color: string;
}

const KEYWORDS = new Set([
  'function', 'const', 'let', 'var', 'return', 'if', 'else', 'import',
  'export', 'from', 'new', 'typeof', 'instanceof',
]);

const TYPES = new Set([
  'string', 'number', 'boolean', 'void', 'any', 'never',
  'ProcessedInput',
]);

function tokenizeLine(line: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;

  while (i < line.length) {
    // Leading whitespace
    if (line[i] === ' ' || line[i] === '\t') {
      let ws = '';
      while (i < line.length && (line[i] === ' ' || line[i] === '\t')) {
        ws += line[i];
        i++;
      }
      tokens.push({ text: ws, color: CODE_TEXT_COLOR });
      continue;
    }

    // Comments (// ...)
    if (line[i] === '/' && line[i + 1] === '/') {
      tokens.push({ text: line.slice(i), color: SYN_COMMENT });
      i = line.length;
      continue;
    }

    // Regex literal  /pattern/flags
    if (line[i] === '/' && i > 0 && line.slice(0, i).match(/[\(=,]\s*$/)) {
      let regex = '/';
      i++;
      let escaped = false;
      while (i < line.length && (escaped || line[i] !== '/')) {
        escaped = !escaped && line[i] === '\\';
        regex += line[i];
        i++;
      }
      if (i < line.length) {
        regex += line[i]; // closing /
        i++;
      }
      // flags
      while (i < line.length && /[gimsuy]/.test(line[i])) {
        regex += line[i];
        i++;
      }
      tokens.push({ text: regex, color: SYN_REGEX });
      continue;
    }

    // String literals
    if (line[i] === "'" || line[i] === '"' || line[i] === '`') {
      const quote = line[i];
      let str = quote;
      i++;
      while (i < line.length && line[i] !== quote) {
        if (line[i] === '\\') {
          str += line[i];
          i++;
        }
        if (i < line.length) {
          str += line[i];
          i++;
        }
      }
      if (i < line.length) {
        str += line[i]; // closing quote
        i++;
      }
      tokens.push({ text: str, color: SYN_STRING });
      continue;
    }

    // Numbers
    if (/[0-9]/.test(line[i])) {
      let num = '';
      while (i < line.length && /[0-9.]/.test(line[i])) {
        num += line[i];
        i++;
      }
      tokens.push({ text: num, color: SYN_NUMBER });
      continue;
    }

    // Identifiers / keywords
    if (/[a-zA-Z_$]/.test(line[i])) {
      let word = '';
      while (i < line.length && /[a-zA-Z0-9_$]/.test(line[i])) {
        word += line[i];
        i++;
      }
      if (KEYWORDS.has(word)) {
        tokens.push({ text: word, color: SYN_KEYWORD });
      } else if (TYPES.has(word)) {
        tokens.push({ text: word, color: SYN_TYPE });
      } else if (word === 'true' || word === 'false') {
        tokens.push({ text: word, color: SYN_BOOLEAN });
      } else if (word === 'MAX_INPUT_LENGTH') {
        tokens.push({ text: word, color: SYN_TYPE });
      } else {
        // Check if next non-space is '(' => function call color
        let peek = i;
        while (peek < line.length && line[peek] === ' ') peek++;
        if (peek < line.length && line[peek] === '(') {
          tokens.push({ text: word, color: SYN_IDENTIFIER });
        } else {
          tokens.push({ text: word, color: CODE_TEXT_COLOR });
        }
      }
      continue;
    }

    // Spread/rest operator
    if (line[i] === '.' && line[i + 1] === '.' && line[i + 2] === '.') {
      tokens.push({ text: '...', color: SYN_OPERATOR });
      i += 3;
      continue;
    }

    // Operators
    if ('=!<>&|+-*/%?:'.includes(line[i])) {
      let op = line[i];
      i++;
      // Grab multi-char operators
      while (i < line.length && '=!<>&|'.includes(line[i])) {
        op += line[i];
        i++;
      }
      tokens.push({ text: op, color: SYN_OPERATOR });
      continue;
    }

    // Punctuation / brackets — default color
    tokens.push({ text: line[i], color: CODE_TEXT_COLOR });
    i++;
  }

  return tokens;
}

// ── Component ───────────────────────────────────────────────────────────────

interface SyntaxLineProps {
  line: string;
  lineIndex: number;
  /** How many characters to show (for typewriter effect). undefined = show all */
  visibleChars?: number;
  /** Extra background color for selection/glow */
  bgColor?: string;
  /** Optional line number override (1-based). Defaults to lineIndex + 1 */
  lineNumber?: number;
}

const SyntaxLine: React.FC<SyntaxLineProps> = ({
  line,
  lineIndex,
  visibleChars,
  bgColor,
  lineNumber,
}) => {
  const tokens = tokenizeLine(line);
  const displayLineNum = lineNumber ?? lineIndex + 1;

  // Build clipped token spans
  let charCount = 0;
  const spans: React.ReactNode[] = [];

  for (let t = 0; t < tokens.length; t++) {
    const token = tokens[t];
    if (visibleChars !== undefined && charCount >= visibleChars) break;

    let text = token.text;
    if (visibleChars !== undefined) {
      const remaining = visibleChars - charCount;
      if (text.length > remaining) {
        text = text.slice(0, remaining);
      }
    }
    charCount += text.length;

    spans.push(
      <span key={t} style={{ color: token.color }}>
        {text}
      </span>,
    );
  }

  return (
    <div
      style={{
        position: 'absolute',
        top: lineIndex * LINE_HEIGHT,
        left: 0,
        width: '100%',
        height: LINE_HEIGHT,
        display: 'flex',
        alignItems: 'center',
        background: bgColor ?? 'transparent',
      }}
    >
      {/* Line number in gutter */}
      <span
        style={{
          width: GUTTER_WIDTH,
          textAlign: 'right',
          paddingRight: 16,
          fontFamily: '"JetBrains Mono", monospace',
          fontSize: CODE_FONT_SIZE - 2,
          color: LINE_NUMBER_COLOR,
          flexShrink: 0,
          userSelect: 'none',
        }}
      >
        {displayLineNum}
      </span>
      {/* Code content */}
      <span
        style={{
          marginLeft: CODE_LEFT_PADDING - GUTTER_WIDTH,
          fontFamily: '"JetBrains Mono", monospace',
          fontSize: CODE_FONT_SIZE,
          whiteSpace: 'pre',
          lineHeight: `${LINE_HEIGHT}px`,
        }}
      >
        {spans}
      </span>
    </div>
  );
};

export default SyntaxLine;
