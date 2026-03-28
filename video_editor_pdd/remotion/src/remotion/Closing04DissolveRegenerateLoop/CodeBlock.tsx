import React, { useMemo } from 'react';
import { useCurrentFrame } from 'remotion';
import {
  CODE_BLOCK_CENTER_X,
  CODE_BLOCK_CENTER_Y,
  CODE_BLOCK_WIDTH,
  CODE_BLOCK_HEIGHT,
  CODE_BG,
  CODE_BG_OPACITY,
  CODE_BORDER_RADIUS,
  SYNTAX_KEYWORD,
  SYNTAX_FUNCTION,
  SYNTAX_DEFAULT,
  SYNTAX_STRING,
  CodeLine,
} from './constants';

// ── Syntax highlighting ────────────────────────────────────────────
const PYTHON_KEYWORDS = ['def', 'for', 'in', 'return', 'import'];

interface TokenSpan {
  text: string;
  color: string;
}

function tokenizeLine(line: string): TokenSpan[] {
  if (line.trim() === '') return [{ text: '', color: SYNTAX_DEFAULT }];

  const spans: TokenSpan[] = [];
  let remaining = line;

  while (remaining.length > 0) {
    // Leading whitespace
    const wsMatch = remaining.match(/^(\s+)/);
    if (wsMatch) {
      spans.push({ text: wsMatch[1], color: SYNTAX_DEFAULT });
      remaining = remaining.slice(wsMatch[1].length);
      continue;
    }

    // Keywords
    let matched = false;
    for (const kw of PYTHON_KEYWORDS) {
      if (remaining.startsWith(kw) && (remaining.length === kw.length || /\W/.test(remaining[kw.length]))) {
        spans.push({ text: kw, color: SYNTAX_KEYWORD });
        remaining = remaining.slice(kw.length);
        matched = true;
        break;
      }
    }
    if (matched) continue;

    // Function name detection (after def keyword)
    const prevText = spans.map(s => s.text).join('');
    if (prevText.trimEnd().endsWith('def')) {
      const fnMatch = remaining.match(/^([a-zA-Z_]\w*)/);
      if (fnMatch) {
        spans.push({ text: fnMatch[1], color: SYNTAX_FUNCTION });
        remaining = remaining.slice(fnMatch[1].length);
        continue;
      }
    }

    // String literals
    if (remaining[0] === "'" || remaining[0] === '"') {
      const quote = remaining[0];
      const endIdx = remaining.indexOf(quote, 1);
      if (endIdx > 0) {
        const str = remaining.slice(0, endIdx + 1);
        spans.push({ text: str, color: SYNTAX_STRING });
        remaining = remaining.slice(endIdx + 1);
        continue;
      }
    }

    // Regular text - grab until next keyword, whitespace, or special char
    const wordMatch = remaining.match(/^([^\s]+)/);
    if (wordMatch) {
      spans.push({ text: wordMatch[1], color: SYNTAX_DEFAULT });
      remaining = remaining.slice(wordMatch[1].length);
    } else {
      spans.push({ text: remaining[0], color: SYNTAX_DEFAULT });
      remaining = remaining.slice(1);
    }
  }

  return spans;
}

// ── Component ──────────────────────────────────────────────────────
interface CodeBlockProps {
  code: CodeLine[];
  /** Frame at which code starts appearing (type-in effect) */
  typeInStartFrame: number;
  /** Frame at which code begins dissolving (hide) */
  dissolveStartFrame: number;
  /** Whether code is shown from frame 0 without type-in */
  showImmediate?: boolean;
}

const CodeBlock: React.FC<CodeBlockProps> = ({
  code,
  typeInStartFrame,
  dissolveStartFrame,
  showImmediate = false,
}) => {
  const frame = useCurrentFrame();

  const tokenizedLines = useMemo(
    () => code.map((line) => tokenizeLine(line.text)),
    [code]
  );

  // Total character count for type-in animation
  const allChars = useMemo(() => {
    let count = 0;
    for (const line of code) {
      count += line.text.length + 1; // +1 for newline
    }
    return count;
  }, [code]);

  // Determine visibility
  const isDissolving = frame >= dissolveStartFrame;
  if (isDissolving) return null; // Particles take over

  const isTypingIn = !showImmediate && frame >= typeInStartFrame;
  const isVisible = showImmediate || isTypingIn;
  if (!isVisible) return null;

  // How many characters to show
  const typeProgress = showImmediate
    ? allChars
    : Math.max(0, frame - typeInStartFrame); // 1 char per frame

  let charsShown = 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: CODE_BLOCK_CENTER_X - CODE_BLOCK_WIDTH / 2,
        top: CODE_BLOCK_CENTER_Y - CODE_BLOCK_HEIGHT / 2,
        width: CODE_BLOCK_WIDTH,
        height: CODE_BLOCK_HEIGHT,
        backgroundColor: CODE_BG,
        opacity: CODE_BG_OPACITY,
        borderRadius: CODE_BORDER_RADIUS,
        padding: '16px 16px',
        boxSizing: 'border-box',
        overflow: 'hidden',
      }}
    >
      {tokenizedLines.map((spans, lineIdx) => {
        const lineCharsNeeded = code[lineIdx].text.length;
        const lineStart = charsShown;
        charsShown += lineCharsNeeded + 1;

        return (
          <div
            key={lineIdx}
            style={{
              fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
              fontSize: 13,
              fontWeight: 400,
              lineHeight: '20px',
              whiteSpace: 'pre',
              height: 20,
            }}
          >
            {spans.map((span, spanIdx) => {
              // Calculate how many chars of this span to show
              let spanOffset = 0;
              for (let s = 0; s < spanIdx; s++) {
                spanOffset += spans[s].text.length;
              }
              const globalStart = lineStart + spanOffset;
              const visibleCount = Math.min(
                span.text.length,
                Math.max(0, typeProgress - globalStart)
              );

              if (visibleCount <= 0) return null;

              return (
                <span key={spanIdx} style={{ color: span.color }}>
                  {span.text.slice(0, visibleCount)}
                </span>
              );
            })}
          </div>
        );
      })}
    </div>
  );
};

export default CodeBlock;
