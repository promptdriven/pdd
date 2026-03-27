import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import {
  CODE_BG,
  CODE_BORDER_RADIUS,
  CODE_PADDING,
  CODE_BLOCK_X,
  CODE_BLOCK_Y,
  CODE_BLOCK_WIDTH,
  CODE_TYPE_START,
  VERILOG_CODE_LINES,
  VERILOG_CODE_FLAT,
  TYPE_SPEED,
} from './constants';

/**
 * Renders the Verilog code block with a typewriter effect.
 * Code types in character by character from CODE_TYPE_START.
 */
export const CodeBlock: React.FC = () => {
  const frame = useCurrentFrame();

  const totalChars = VERILOG_CODE_FLAT.length;
  const typingFrames = totalChars * TYPE_SPEED;

  // How many characters are visible at this frame
  const charsVisible = Math.floor(
    interpolate(
      frame,
      [CODE_TYPE_START, CODE_TYPE_START + typingFrames],
      [0, totalChars],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
    )
  );

  // Container opacity — appears at CODE_TYPE_START
  const containerOpacity = interpolate(
    frame,
    [CODE_TYPE_START, CODE_TYPE_START + 10],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  if (frame < CODE_TYPE_START) return null;

  // Walk through lines and tokens, rendering only up to charsVisible
  let charsSoFar = 0;
  const renderedLines: React.ReactNode[] = [];

  for (let lineIdx = 0; lineIdx < VERILOG_CODE_LINES.length; lineIdx++) {
    const line = VERILOG_CODE_LINES[lineIdx];
    const lineStartChar = charsSoFar;

    // Account for newline between lines (except first)
    if (lineIdx > 0) charsSoFar += 1; // \n

    if (charsSoFar >= charsVisible) break;

    const tokenSpans: React.ReactNode[] = [];

    for (let tokenIdx = 0; tokenIdx < line.tokens.length; tokenIdx++) {
      const token = line.tokens[tokenIdx];
      const tokenStartChar = charsSoFar;
      const tokenLen = token.value.length;

      if (tokenStartChar >= charsVisible) break;

      const visibleLen = Math.min(tokenLen, charsVisible - tokenStartChar);
      const visibleText = token.value.slice(0, visibleLen);

      tokenSpans.push(
        <span key={`${lineIdx}-${tokenIdx}`} style={{ color: token.color }}>
          {visibleText}
        </span>
      );

      charsSoFar += tokenLen;
    }

    // If we haven't started this line yet, skip
    if (lineStartChar + (lineIdx > 0 ? 1 : 0) >= charsVisible) break;

    renderedLines.push(
      <div key={`line-${lineIdx}`} style={{ minHeight: 24, lineHeight: '24px' }}>
        {tokenSpans}
      </div>
    );

    // If line text not fully consumed, still advance charsSoFar past the full line
    // (it's already advanced token by token above)
  }

  // Blinking cursor
  const cursorVisible = Math.floor(frame / 15) % 2 === 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: CODE_BLOCK_X,
        top: CODE_BLOCK_Y,
        width: CODE_BLOCK_WIDTH,
        backgroundColor: CODE_BG,
        borderRadius: CODE_BORDER_RADIUS,
        padding: CODE_PADDING,
        fontFamily: '"JetBrains Mono", "Fira Code", "Courier New", monospace',
        fontSize: 16,
        fontWeight: 400,
        opacity: containerOpacity,
        boxShadow: '0 4px 24px rgba(0,0,0,0.3)',
      }}
    >
      {/* Window chrome dots */}
      <div style={{ display: 'flex', gap: 6, marginBottom: 16 }}>
        <div style={{ width: 10, height: 10, borderRadius: '50%', backgroundColor: '#FF5F56' }} />
        <div style={{ width: 10, height: 10, borderRadius: '50%', backgroundColor: '#FFBD2E' }} />
        <div style={{ width: 10, height: 10, borderRadius: '50%', backgroundColor: '#27C93F' }} />
      </div>

      {/* Code content */}
      <div>
        {renderedLines}
        {charsVisible < totalChars && cursorVisible && (
          <span
            style={{
              display: 'inline-block',
              width: 8,
              height: 18,
              backgroundColor: '#E2E8F0',
              verticalAlign: 'text-bottom',
              marginLeft: 1,
            }}
          />
        )}
      </div>
    </div>
  );
};
