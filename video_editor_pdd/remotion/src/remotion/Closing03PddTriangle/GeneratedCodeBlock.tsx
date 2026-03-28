import React, { useMemo } from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CODE_BOX_WIDTH,
  CODE_BOX_HEIGHT,
  CODE_BG_COLOR,
  CODE_BORDER_RADIUS,
  CODE_FONT_SIZE,
  CODE_FONT_FAMILY,
  CODE_LINES,
  CODE_FADE_START,
  CODE_TYPE_START,
  TRIANGLE_CENTER_X,
  SYNTAX_KEYWORD,
  SYNTAX_STRING,
  SYNTAX_FUNCTION,
  SYNTAX_PUNCTUATION,
  SYNTAX_DEFAULT,
} from './constants';

// Simple Python syntax token types
type TokenType = 'keyword' | 'string' | 'function' | 'punctuation' | 'default';

interface Token {
  text: string;
  type: TokenType;
}

const PYTHON_KEYWORDS = ['def', 'return', 'for', 'in', 'import', 'from', 'class', 'if', 'else'];

function tokenizeLine(line: string): Token[] {
  if (line.trim() === '') return [{ text: ' ', type: 'default' }];

  const tokens: Token[] = [];
  // Capture leading whitespace
  const leadMatch = line.match(/^(\s+)/);
  if (leadMatch) {
    tokens.push({ text: leadMatch[1], type: 'default' });
    line = line.slice(leadMatch[1].length);
  }

  // Simple tokenizer: split by word boundaries and punctuation
  const parts = line.split(/(\s+|[(),:.*\-+])/);
  let prevWasDef = false;

  for (const part of parts) {
    if (part === '') continue;

    if (PYTHON_KEYWORDS.includes(part)) {
      tokens.push({ text: part, type: 'keyword' });
      prevWasDef = part === 'def';
    } else if (/^['"]/.test(part)) {
      tokens.push({ text: part, type: 'string' });
      prevWasDef = false;
    } else if (/^[(),:.*\-+]$/.test(part)) {
      tokens.push({ text: part, type: 'punctuation' });
      prevWasDef = false;
    } else if (prevWasDef || /^[a-z_][a-z0-9_]*$/i.test(part)) {
      if (prevWasDef) {
        tokens.push({ text: part, type: 'function' });
        prevWasDef = false;
      } else {
        tokens.push({ text: part, type: 'default' });
      }
    } else {
      tokens.push({ text: part, type: 'default' });
      prevWasDef = false;
    }
  }

  return tokens;
}

function getTokenColor(type: TokenType): string {
  switch (type) {
    case 'keyword':
      return SYNTAX_KEYWORD;
    case 'string':
      return SYNTAX_STRING;
    case 'function':
      return SYNTAX_FUNCTION;
    case 'punctuation':
      return SYNTAX_PUNCTUATION;
    default:
      return SYNTAX_DEFAULT;
  }
}

const GeneratedCodeBlock: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in the code block container
  const containerOpacity = interpolate(frame, [CODE_FADE_START, CODE_FADE_START + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Total characters across all lines (including newline separators)
  const allText = CODE_LINES.join('\n');
  const totalChars = allText.length;

  // Characters revealed so far (2 frames per char = 0.5 chars per frame)
  const typeFrames = frame - CODE_TYPE_START;
  const charsRevealed = Math.max(0, Math.floor(typeFrames * 0.5));

  // Tokenize all lines once
  const tokenizedLines = useMemo(() => CODE_LINES.map(tokenizeLine), []);

  // Shimmer effect after typing is done
  const typingDone = charsRevealed >= totalChars;
  let shimmerOpacity = 0;
  if (typingDone && frame >= 130) {
    const shimmerCycle = (frame - 130) % 60;
    shimmerOpacity = Math.sin((shimmerCycle / 60) * Math.PI * 2) * 0.06 + 0.04;
  }

  // Figure out how many chars to show per line
  let charBudget = charsRevealed;

  return (
    <div
      style={{
        position: 'absolute',
        left: TRIANGLE_CENTER_X - CODE_BOX_WIDTH / 2,
        top: 480 - CODE_BOX_HEIGHT / 2,
        width: CODE_BOX_WIDTH,
        height: CODE_BOX_HEIGHT,
        backgroundColor: CODE_BG_COLOR,
        opacity: containerOpacity,
        borderRadius: CODE_BORDER_RADIUS,
        padding: '16px 20px',
        overflow: 'hidden',
        boxShadow: `0 0 30px rgba(226, 232, 240, 0.1)`,
      }}
    >
      {/* Shimmer overlay */}
      {shimmerOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            inset: 0,
            backgroundColor: '#E2E8F0',
            opacity: shimmerOpacity,
            borderRadius: CODE_BORDER_RADIUS,
            pointerEvents: 'none',
          }}
        />
      )}
      {tokenizedLines.map((tokens, lineIndex) => {
        // Each line uses its text length + 1 for newline
        const lineText = CODE_LINES[lineIndex];
        const lineLen = lineText.length + (lineIndex < CODE_LINES.length - 1 ? 1 : 0);

        if (charBudget <= 0) return null;

        const lineCharsToShow = Math.min(lineText.length, charBudget);
        charBudget -= lineLen;

        // Render tokens up to lineCharsToShow
        let charCount = 0;
        const renderedTokens: React.ReactNode[] = [];

        for (let t = 0; t < tokens.length; t++) {
          const token = tokens[t];
          if (charCount >= lineCharsToShow) break;

          const remaining = lineCharsToShow - charCount;
          const visibleText = token.text.slice(0, remaining);
          charCount += token.text.length;

          renderedTokens.push(
            <span key={t} style={{ color: getTokenColor(token.type) }}>
              {visibleText}
            </span>
          );
        }

        return (
          <div
            key={lineIndex}
            style={{
              fontFamily: CODE_FONT_FAMILY,
              fontSize: CODE_FONT_SIZE,
              lineHeight: '20px',
              whiteSpace: 'pre',
              minHeight: '20px',
            }}
          >
            {renderedTokens}
            {/* Blinking cursor at end of current typing line */}
            {charBudget < lineLen && charBudget >= -lineLen && !typingDone && (
              <span
                style={{
                  color: SYNTAX_DEFAULT,
                  opacity: frame % 16 < 8 ? 1 : 0.3,
                }}
              >
                |
              </span>
            )}
          </div>
        );
      })}
    </div>
  );
};

export default GeneratedCodeBlock;
