import React from 'react';
import {
  CODE_LINES,
  CODE_FONT_SIZE,
  CODE_LINE_HEIGHT,
  CODE_X_OFFSET,
  CODE_Y_OFFSET,
  CODE_COLORS,
} from './constants';

/**
 * Simple syntax-highlighted code block rendered as positioned spans.
 * Purely decorative — used as a dimmed background texture.
 */

type TokenType = 'keyword' | 'function' | 'string' | 'property' | 'punctuation' | 'default';

interface Token {
  text: string;
  type: TokenType;
}

const KEYWORDS = new Set([
  'async', 'function', 'const', 'await', 'return',
]);

function tokenizeLine(line: string): Token[] {
  if (line.trim() === '') return [{ text: ' ', type: 'default' }];

  const tokens: Token[] = [];
  // Simple regex-based tokenizer for display purposes
  const regex = /("(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*')|(\b(?:async|function|const|await|return)\b)|([\w.]+(?=\s*\())|([{}();,:])|(\s+)|([\w.]+)/g;
  let match: RegExpExecArray | null;

  while ((match = regex.exec(line)) !== null) {
    const [full, str, kw, fn, punct, ws, ident] = match;
    if (str) {
      tokens.push({ text: str, type: 'string' });
    } else if (kw) {
      tokens.push({ text: kw, type: 'keyword' });
    } else if (fn) {
      tokens.push({ text: fn, type: 'function' });
    } else if (punct) {
      tokens.push({ text: punct, type: 'punctuation' });
    } else if (ws) {
      tokens.push({ text: ws, type: 'default' });
    } else if (ident) {
      tokens.push({
        text: ident,
        type: KEYWORDS.has(ident) ? 'keyword' : 'property',
      });
    }
  }

  return tokens.length > 0 ? tokens : [{ text: line, type: 'default' }];
}

export const CodeUnderlay: React.FC = () => {
  return (
    <div
      style={{
        position: 'absolute',
        top: CODE_Y_OFFSET,
        left: CODE_X_OFFSET,
        fontFamily: '"JetBrains Mono", "Fira Code", "Courier New", monospace',
        fontSize: CODE_FONT_SIZE,
        lineHeight: `${CODE_LINE_HEIGHT}px`,
        whiteSpace: 'pre',
      }}
    >
      {CODE_LINES.map((line, i) => {
        const tokens = tokenizeLine(line);
        return (
          <div key={i} style={{ height: CODE_LINE_HEIGHT }}>
            {tokens.map((token, j) => (
              <span
                key={j}
                style={{ color: CODE_COLORS[token.type] || CODE_COLORS.default }}
              >
                {token.text}
              </span>
            ))}
          </div>
        );
      })}
    </div>
  );
};

export default CodeUnderlay;
