import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing, spring, useVideoConfig } from 'remotion';
import { COLORS, PANEL, TIMING, type TestResult } from './constants';

interface CodePanelProps {
  x: number;
  y: number;
  panelIndex: number;
  code: string;
  filename: string;
  testResult: TestResult;
  isWinner: boolean;
}

// Simple syntax highlighter for Python-like code
function tokenizeLine(line: string): { text: string; color: string }[] {
  const tokens: { text: string; color: string }[] = [];
  const keywords = ['def', 'if', 'else', 'return', 'import', 'try', 'except', 'for', 'in', 'not', 'and', 'or', 'None'];
  const builtins = ['len', 'int', 'str', 'print', 'range', 'split', 'strip', 'match', 'group', 'index', 'isdigit', 'Valid'];

  // Handle comments
  const commentIdx = line.indexOf('#');
  const mainPart = commentIdx >= 0 ? line.substring(0, commentIdx) : line;
  const commentPart = commentIdx >= 0 ? line.substring(commentIdx) : '';

  // Tokenize main part word by word preserving whitespace
  const wordRegex = /(\s+|[a-zA-Z_]\w*|"[^"]*"|'[^']*'|[^\s\w]+)/g;
  let m: RegExpExecArray | null;
  while ((m = wordRegex.exec(mainPart)) !== null) {
    const token = m[1];
    if (/^["']/.test(token)) {
      tokens.push({ text: token, color: COLORS.string });
    } else if (keywords.includes(token)) {
      tokens.push({ text: token, color: COLORS.keyword });
    } else if (builtins.some((b) => token.includes(b))) {
      tokens.push({ text: token, color: COLORS.func });
    } else {
      tokens.push({ text: token, color: '#CBD5E1' });
    }
  }

  if (commentPart) {
    tokens.push({ text: commentPart, color: COLORS.comment });
  }

  return tokens;
}

export const CodePanel: React.FC<CodePanelProps> = ({
  x,
  y,
  panelIndex,
  code,
  filename,
  testResult,
  isWinner,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Panel appear animation (staggered)
  const appearStart = panelIndex * TIMING.panelStagger;
  const panelOpacity = interpolate(
    frame,
    [appearStart, appearStart + TIMING.panelAppearDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );
  const panelSlideY = interpolate(
    frame,
    [appearStart, appearStart + TIMING.panelAppearDuration],
    [20, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Code typing animation
  const totalChars = code.length;
  const typeStartFrame = TIMING.codeTypeStart + panelIndex * TIMING.panelStagger;
  const typeDuration = TIMING.codeTypeEnd - TIMING.codeTypeStart;
  const charsVisible = Math.floor(
    interpolate(
      frame,
      [typeStartFrame, typeStartFrame + typeDuration],
      [0, totalChars],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
    )
  );

  // Test result animation
  const testAppearFrame = TIMING.testResultStart + panelIndex * 8;
  const testOpacity = interpolate(
    frame,
    [testAppearFrame, testAppearFrame + 8],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) }
  );
  const testScale = interpolate(
    frame,
    [testAppearFrame, testAppearFrame + 8],
    [1.5, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) }
  );

  // Progress bar sweep
  const progressBarWidth = interpolate(
    frame,
    [TIMING.testResultStart, TIMING.testResultStart + 30],
    [0, 100],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Winner highlight / dim others
  const winnerScale = isWinner
    ? spring({
        frame: frame - TIMING.winnerHighlightStart,
        fps,
        config: { stiffness: 150, damping: 14 },
      })
    : 0;
  const scale = isWinner
    ? interpolate(winnerScale, [0, 1], [1, 1.05], { extrapolateRight: 'clamp' })
    : 1;

  const dimOpacity = !isWinner
    ? interpolate(
        frame,
        [TIMING.winnerHighlightStart, TIMING.winnerHighlightStart + 20],
        [1, 0.3],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
      )
    : 1;

  // Green glow for winner
  const glowOpacity = isWinner
    ? interpolate(
        frame,
        [TIMING.winnerHighlightStart, TIMING.winnerHighlightStart + 20],
        [0, 0.6],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : 0;

  // Get visible code text
  const visibleCode = code.substring(0, charsVisible);
  const lines = visibleCode.split('\n');

  // Tokenize visible lines
  const tokenizedLines = useMemo(() => {
    return lines.map((line) => tokenizeLine(line));
  }, [visibleCode]);

  const resultColor =
    testResult.type === 'fail'
      ? COLORS.fail
      : testResult.type === 'warning'
        ? COLORS.warning
        : COLORS.pass;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y + panelSlideY,
        width: PANEL.width,
        height: PANEL.height,
        opacity: panelOpacity * dimOpacity,
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
        borderRadius: PANEL.borderRadius,
        border: isWinner && glowOpacity > 0
          ? `2px solid ${COLORS.pass}`
          : `1px solid ${COLORS.panelBorder}`,
        boxShadow: isWinner && glowOpacity > 0
          ? `0 0 ${8 * glowOpacity}px ${COLORS.pass}, 0 4px 20px rgba(0,0,0,0.5)`
          : '0 2px 8px rgba(0,0,0,0.3)',
        overflow: 'hidden',
        backgroundColor: `rgba(30, 41, 59, 0.6)`,
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: PANEL.titleBarHeight,
          backgroundColor: COLORS.panelTitleBar,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 10,
          gap: 6,
        }}
      >
        {/* Window dots */}
        <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#EF4444', opacity: 0.6 }} />
        <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#D9944A', opacity: 0.6 }} />
        <div style={{ width: 8, height: 8, borderRadius: '50%', backgroundColor: '#5AAA6E', opacity: 0.6 }} />
        <span
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 10,
            color: COLORS.textSecondary,
            opacity: 0.6,
            marginLeft: 8,
          }}
        >
          {filename}
        </span>
      </div>

      {/* Code area */}
      <div
        style={{
          padding: '8px 10px',
          height: PANEL.height - PANEL.titleBarHeight - 40,
          overflow: 'hidden',
        }}
      >
        {tokenizedLines.map((tokens, lineIdx) => (
          <div
            key={lineIdx}
            style={{
              fontFamily: 'JetBrains Mono, monospace',
              fontSize: 10,
              lineHeight: '16px',
              whiteSpace: 'pre',
              height: 16,
            }}
          >
            {tokens.map((token, tIdx) => (
              <span key={tIdx} style={{ color: token.color }}>
                {token.text}
              </span>
            ))}
          </div>
        ))}
      </div>

      {/* Progress bar */}
      {frame >= TIMING.testResultStart && (
        <div
          style={{
            position: 'absolute',
            bottom: 40,
            left: 0,
            width: `${progressBarWidth}%`,
            height: 2,
            backgroundColor: resultColor,
            opacity: 0.5,
          }}
        />
      )}

      {/* Test result overlay */}
      {frame >= testAppearFrame && (
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: 0,
            width: '100%',
            height: '100%',
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
            justifyContent: 'center',
            opacity: testOpacity,
          }}
        >
          {/* Result background overlay */}
          <div
            style={{
              position: 'absolute',
              top: 0,
              left: 0,
              width: '100%',
              height: '100%',
              backgroundColor: resultColor,
              opacity: testResult.type === 'pass' ? 0.08 : 0.05,
            }}
          />
          {/* Symbol */}
          <div
            style={{
              fontSize: testResult.type === 'warning' ? 60 : 80,
              color: resultColor,
              opacity: testResult.type === 'pass' ? 0.8 : 0.6,
              transform: `scale(${testScale})`,
              fontWeight: 700,
              lineHeight: 1,
            }}
          >
            {testResult.symbol}
          </div>
          {/* Label */}
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 11,
              color: resultColor,
              marginTop: 8,
              opacity: 0.8,
            }}
          >
            {testResult.label}
          </div>
        </div>
      )}
    </div>
  );
};
