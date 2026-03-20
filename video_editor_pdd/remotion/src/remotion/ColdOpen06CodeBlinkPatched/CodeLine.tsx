import React from 'react';
import {
  BASE_CODE_COLOR,
  KEYWORD_COLOR,
  STRING_COLOR,
  COMMENT_COLOR,
  FUNCTION_NAME_COLOR,
  CODE_FONT_SIZE,
  CODE_LINE_HEIGHT,
  CODE_X_START,
  CODE_Y_START,
  LINE_NUMBER_COLOR,
  LINE_NUMBER_FONT_SIZE,
  LINE_NUMBER_X_END,
  Token,
  TokenType,
} from './constants';

const TOKEN_COLORS: Record<TokenType, string> = {
  keyword: KEYWORD_COLOR,
  string: STRING_COLOR,
  comment: COMMENT_COLOR,
  functionName: FUNCTION_NAME_COLOR,
  type: BASE_CODE_COLOR,
  plain: BASE_CODE_COLOR,
};

const KEYWORDS = new Set([
  'function',
  'const',
  'let',
  'var',
  'if',
  'else',
  'return',
]);

/**
 * Simple tokenizer for the code lines.
 * Handles keywords, strings, comments, and the function name.
 */
function tokenize(line: string, lineIndex: number): Token[] {
  const tokens: Token[] = [];

  // Entire line is a comment
  const trimmed = line.trimStart();
  if (trimmed.startsWith('//')) {
    const leadingWhitespace = line.slice(0, line.length - trimmed.length);
    if (leadingWhitespace) {
      tokens.push({ text: leadingWhitespace, type: 'plain' });
    }
    tokens.push({ text: trimmed, type: 'comment' });
    return tokens;
  }

  // Empty line
  if (line.trim() === '') {
    tokens.push({ text: '', type: 'plain' });
    return tokens;
  }

  // Tokenize character by character with simple state machine
  let i = 0;
  let current = '';
  let inString: string | null = null;

  const flush = (type: TokenType) => {
    if (current.length > 0) {
      tokens.push({ text: current, type });
      current = '';
    }
  };

  while (i < line.length) {
    const ch = line[i];

    // Handle strings
    if (inString) {
      current += ch;
      if (ch === inString && line[i - 1] !== '\\') {
        flush('string');
        inString = null;
      }
      i++;
      continue;
    }

    if (ch === "'" || ch === '"' || ch === '`') {
      flush('plain');
      inString = ch;
      current += ch;
      i++;
      continue;
    }

    // Handle inline comments
    if (ch === '/' && line[i + 1] === '/') {
      flush('plain');
      current = line.slice(i);
      flush('comment');
      i = line.length;
      continue;
    }

    // Handle regex literal (simple detection)
    if (ch === '/' && i > 0 && line[i - 1] !== ' ' && line[i - 1] !== '(') {
      current += ch;
      i++;
      continue;
    }

    // Word boundaries
    if (/\w/.test(ch)) {
      current += ch;
      i++;
      continue;
    }

    // Non-word character: flush current word
    if (current.length > 0) {
      // Check if current word is a keyword
      if (KEYWORDS.has(current)) {
        flush('keyword');
      } else if (
        lineIndex === 0 &&
        current === 'processUserInput'
      ) {
        flush('functionName');
      } else if (current === 'ProcessedInput' || current === 'MAX_INPUT_LENGTH') {
        flush('type');
      } else {
        flush('plain');
      }
    }

    // Push the non-word character
    tokens.push({ text: ch, type: 'plain' });
    i++;
  }

  // Flush remaining
  if (current.length > 0) {
    if (KEYWORDS.has(current)) {
      flush('keyword');
    } else if (
      lineIndex === 0 &&
      current === 'processUserInput'
    ) {
      flush('functionName');
    } else if (current === 'ProcessedInput' || current === 'MAX_INPUT_LENGTH') {
      flush('type');
    } else {
      flush('plain');
    }
  }

  return tokens;
}

interface CodeLineProps {
  text: string;
  lineIndex: number; // 0-based
}

export const CodeLineComponent: React.FC<CodeLineProps> = ({
  text,
  lineIndex,
}) => {
  const lineNumber = lineIndex + 1;
  const y = CODE_Y_START + lineIndex * CODE_LINE_HEIGHT;
  const tokens = tokenize(text, lineIndex);

  return (
    <>
      {/* Line number */}
      <div
        style={{
          position: 'absolute',
          right: 1920 - LINE_NUMBER_X_END,
          top: y,
          width: 30,
          height: CODE_LINE_HEIGHT,
          textAlign: 'right',
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: LINE_NUMBER_FONT_SIZE,
          lineHeight: `${CODE_LINE_HEIGHT}px`,
          color: LINE_NUMBER_COLOR,
          opacity: 0.5,
          userSelect: 'none',
        }}
      >
        {lineNumber}
      </div>

      {/* Code tokens */}
      <div
        style={{
          position: 'absolute',
          left: CODE_X_START,
          top: y,
          height: CODE_LINE_HEIGHT,
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: CODE_FONT_SIZE,
          lineHeight: `${CODE_LINE_HEIGHT}px`,
          whiteSpace: 'pre',
          display: 'flex',
        }}
      >
        {tokens.map((token, idx) => {
          const isComment = token.type === 'comment';
          return (
            <span
              key={idx}
              style={{
                color: TOKEN_COLORS[token.type],
                opacity: isComment ? 0.7 : 1,
              }}
            >
              {token.text}
            </span>
          );
        })}
      </div>
    </>
  );
};
