import React from 'react';
import { useCurrentFrame, Easing, interpolate, spring, useVideoConfig } from 'remotion';
import {
  PANEL_WIDTH,
  PANEL_HEIGHT,
  PANEL_BG,
  PANEL_BORDER,
  PANEL_TITLE_BG,
  PANEL_TITLE_HEIGHT,
  FONT_MONO,
  FONT_SANS,
  SYN_KEYWORD,
  SYN_STRING,
  SYN_FUNCTION,
  SYN_COMMENT,
  SYN_DEFAULT,
  COLOR_FAIL,
  COLOR_WARN,
  COLOR_PASS,
  TEXT_MUTED,
  CODE_TYPE_START,
  CODE_TYPE_END,
  TEST_RESULTS_START,
  WINNER_HIGHLIGHT_START,
  WINNER_INDEX,
  type TestResult,
} from './constants';

const KEYWORDS = new Set([
  'def', 'import', 'from', 'return', 'if', 'class', 'self', 'not', 'and', 'or',
]);
const BUILTINS = new Set([
  'int', 'str', 'len', 'None', 'Optional', 'dict', 're', 'typing',
]);

interface TokenSpan {
  text: string;
  color: string;
}

function tokenizeLine(line: string): TokenSpan[] {
  const spans: TokenSpan[] = [];
  if (line.startsWith('#')) {
    spans.push({ text: line, color: SYN_COMMENT });
    return spans;
  }

  const regex = /("[^"]*"|'[^']*'|\b\w+\b|[^\s\w]+|\s+)/g;
  let match: RegExpExecArray | null;
  while ((match = regex.exec(line)) !== null) {
    const tok = match[0];
    if (tok.startsWith('"') || tok.startsWith("'")) {
      spans.push({ text: tok, color: SYN_STRING });
    } else if (KEYWORDS.has(tok)) {
      spans.push({ text: tok, color: SYN_KEYWORD });
    } else if (BUILTINS.has(tok)) {
      spans.push({ text: tok, color: SYN_FUNCTION });
    } else if (/^\w+$/.test(tok) && tok === tok) {
      // Check if it looks like a function call by peeking ahead
      const rest = line.slice((match.index ?? 0) + tok.length);
      if (rest.startsWith('(')) {
        spans.push({ text: tok, color: SYN_FUNCTION });
      } else {
        spans.push({ text: tok, color: SYN_DEFAULT });
      }
    } else {
      spans.push({ text: tok, color: SYN_DEFAULT });
    }
  }
  return spans;
}

function getResultColor(type: TestResult['type']): string {
  if (type === 'fail') return COLOR_FAIL;
  if (type === 'warning') return COLOR_WARN;
  return COLOR_PASS;
}

interface CodePanelProps {
  x: number;
  y: number;
  panelIndex: number;
  filename: string;
  codeLines: string[];
  testResult: TestResult;
  staggerDelay: number; // frames offset for panel appearance
}

export const CodePanel: React.FC<CodePanelProps> = ({
  x,
  y,
  panelIndex,
  filename,
  codeLines,
  testResult,
  staggerDelay,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const isWinner = panelIndex === WINNER_INDEX;

  // Panel appear animation (frame 0-30, staggered)
  const appearProgress = interpolate(
    frame,
    [staggerDelay, staggerDelay + 12],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Code typing (frame 30-120)
  const totalChars = codeLines.join('\n').length;
  const typeProgress = interpolate(
    frame,
    [CODE_TYPE_START + staggerDelay, CODE_TYPE_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const visibleChars = Math.floor(typeProgress * totalChars);

  // Test result appearance (frame 120-180, staggered by 8 frames)
  const testAppearFrame = TEST_RESULTS_START + panelIndex * 8;
  const testProgress = interpolate(
    frame,
    [testAppearFrame, testAppearFrame + 8],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.exp) }
  );

  // Progress bar sweep (frame 120-160)
  const progressBarWidth = interpolate(
    frame,
    [TEST_RESULTS_START, TEST_RESULTS_START + 40],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Winner highlight (frame 180+)
  const winnerScale = isWinner
    ? spring({
        frame: Math.max(0, frame - WINNER_HIGHLIGHT_START),
        fps,
        config: { stiffness: 150, damping: 14 },
      })
    : 0;
  const scale = isWinner ? 1 + winnerScale * 0.05 : 1;

  // Dim non-winners (frame 180-200)
  const dimOpacity = !isWinner
    ? interpolate(
        frame,
        [WINNER_HIGHLIGHT_START, WINNER_HIGHLIGHT_START + 20],
        [1, 0.3],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
      )
    : 1;

  // Build visible code string
  let charCount = 0;
  const renderedLines: React.ReactNode[] = [];
  for (let lineIdx = 0; lineIdx < codeLines.length; lineIdx++) {
    const line = codeLines[lineIdx];
    const lineStart = charCount;
    charCount += line.length + (lineIdx < codeLines.length - 1 ? 1 : 0); // +1 for newline

    if (lineStart >= visibleChars) break;

    const visibleLineChars = Math.min(line.length, visibleChars - lineStart);
    const visibleLine = line.substring(0, visibleLineChars);
    const tokens = tokenizeLine(visibleLine);

    renderedLines.push(
      <div key={lineIdx} style={{ display: 'flex', flexWrap: 'wrap', minHeight: 14 }}>
        {tokens.map((tok, ti) => (
          <span key={ti} style={{ color: tok.color, whiteSpace: 'pre' }}>
            {tok.text}
          </span>
        ))}
        {visibleLineChars === line.length ? null : (
          <span
            style={{
              display: 'inline-block',
              width: 6,
              height: 12,
              backgroundColor: '#E2E8F0',
              marginLeft: 1,
              opacity: frame % 16 < 8 ? 1 : 0,
            }}
          />
        )}
      </div>
    );
  }

  const resultColor = getResultColor(testResult.type);

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width: PANEL_WIDTH,
        height: PANEL_HEIGHT,
        opacity: appearProgress * dimOpacity,
        transform: `scale(${scale}) translateY(${(1 - appearProgress) * 20}px)`,
        transformOrigin: 'center center',
        borderRadius: 6,
        border: isWinner && frame >= WINNER_HIGHLIGHT_START
          ? `2px solid ${COLOR_PASS}`
          : `1px solid ${PANEL_BORDER}`,
        boxShadow: isWinner && frame >= WINNER_HIGHLIGHT_START
          ? `0 0 8px ${COLOR_PASS}60, 0 4px 20px rgba(0,0,0,0.4)`
          : '0 2px 8px rgba(0,0,0,0.3)',
        overflow: 'hidden',
        backgroundColor: PANEL_BG,
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: PANEL_TITLE_HEIGHT,
          backgroundColor: PANEL_TITLE_BG,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 10,
          borderBottom: `1px solid ${PANEL_BORDER}`,
        }}
      >
        {/* Fake window dots */}
        <div style={{ display: 'flex', gap: 5 }}>
          <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#EF4444', opacity: 0.6 }} />
          <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#F59E0B', opacity: 0.6 }} />
          <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#22C55E', opacity: 0.6 }} />
        </div>
        <span
          style={{
            fontFamily: FONT_MONO,
            fontSize: 10,
            color: TEXT_MUTED,
            opacity: 0.6,
            marginLeft: 10,
          }}
        >
          {filename}
        </span>
      </div>

      {/* Code area */}
      <div
        style={{
          padding: '8px 10px',
          fontFamily: FONT_MONO,
          fontSize: 10,
          lineHeight: '14px',
          height: PANEL_HEIGHT - PANEL_TITLE_HEIGHT - 50,
          overflow: 'hidden',
        }}
      >
        {renderedLines}
      </div>

      {/* Progress bar at bottom */}
      {frame >= TEST_RESULTS_START && (
        <div
          style={{
            position: 'absolute',
            bottom: 50,
            left: 0,
            width: `${progressBarWidth * 100}%`,
            height: 2,
            backgroundColor: resultColor,
            opacity: 0.6,
          }}
        />
      )}

      {/* Test result overlay */}
      {testProgress > 0 && (
        <div
          style={{
            position: 'absolute',
            bottom: 0,
            left: 0,
            right: 0,
            height: 46,
            backgroundColor: `${resultColor}15`,
            borderTop: `1px solid ${resultColor}40`,
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
            justifyContent: 'center',
            opacity: testProgress,
            transform: `scale(${0.8 + testProgress * 0.2})`,
          }}
        >
          <span
            style={{
              fontFamily: FONT_SANS,
              fontSize: testResult.type === 'pass' ? 22 : 18,
              color: resultColor,
              fontWeight: 700,
              opacity: 0.8,
            }}
          >
            {testResult.symbol}
          </span>
          <span
            style={{
              fontFamily: FONT_SANS,
              fontSize: 9,
              color: resultColor,
              opacity: 0.7,
              marginTop: 2,
            }}
          >
            {testResult.label}
          </span>
        </div>
      )}
    </div>
  );
};

export default CodePanel;
