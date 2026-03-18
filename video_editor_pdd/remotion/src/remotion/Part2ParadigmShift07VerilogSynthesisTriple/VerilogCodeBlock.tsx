import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { VERILOG_TOKENS, CODE_BG, CODE_BG_OPACITY, type CodeLine } from './constants';

interface VerilogCodeBlockProps {
  x: number;
  y: number;
  width: number;
  height: number;
  fontSize: number;
  /** Frame at which this block starts appearing (relative to parent Sequence) */
  startFrame: number;
  /** Whether to show typing animation. If false, shows all text immediately. */
  typeEffect?: boolean;
}

/**
 * Renders a syntax-highlighted Verilog code block with optional typing effect.
 */
export const VerilogCodeBlock: React.FC<VerilogCodeBlockProps> = ({
  x,
  y,
  width,
  height,
  fontSize,
  startFrame,
  typeEffect = true,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  const fadeIn = interpolate(localFrame, [0, 10], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Compute total character count across all lines for typing
  const allChars: Array<{ lineIdx: number; tokenIdx: number; charIdx: number; color: string; char: string }> = [];
  VERILOG_TOKENS.forEach((line: CodeLine, lineIdx: number) => {
    line.forEach((token, tokenIdx) => {
      for (let charIdx = 0; charIdx < token.text.length; charIdx++) {
        allChars.push({
          lineIdx,
          tokenIdx,
          charIdx,
          color: token.color,
          char: token.text[charIdx],
        });
      }
    });
  });

  // 2 frames per character typing speed
  const charsVisible = typeEffect
    ? Math.floor(interpolate(localFrame, [0, allChars.length * 2], [0, allChars.length], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      }))
    : allChars.length;

  // Group visible chars back into lines for rendering
  const visibleChars = allChars.slice(0, charsVisible);

  // Build line renders
  const lineHeight = fontSize * 1.6;
  const paddingX = 16;
  const paddingY = 12;

  return (
    <div
      style={{
        position: 'absolute',
        left: x - width / 2,
        top: y - height / 2,
        width,
        height,
        backgroundColor: CODE_BG,
        opacity: fadeIn,
        borderRadius: 4,
        padding: `${paddingY}px ${paddingX}px`,
        boxSizing: 'border-box',
        overflow: 'hidden',
      }}
    >
      {/* Code BG overlay for opacity */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          backgroundColor: CODE_BG,
          opacity: CODE_BG_OPACITY,
          borderRadius: 4,
          zIndex: 0,
        }}
      />
      <div style={{ position: 'relative', zIndex: 1 }}>
        {VERILOG_TOKENS.map((line: CodeLine, lineIdx: number) => {
          // Gather visible chars for this line
          const lineChars = visibleChars.filter((c) => c.lineIdx === lineIdx);
          if (lineChars.length === 0 && typeEffect) return null;

          return (
            <div
              key={lineIdx}
              style={{
                height: lineHeight,
                fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
                fontSize,
                lineHeight: `${lineHeight}px`,
                whiteSpace: 'pre',
              }}
            >
              {typeEffect
                ? lineChars.map((c, i) => (
                    <span key={i} style={{ color: c.color }}>
                      {c.char}
                    </span>
                  ))
                : line.map((token, tIdx) => (
                    <span key={tIdx} style={{ color: token.color, opacity: token.opacity ?? 1 }}>
                      {token.text}
                    </span>
                  ))}
            </div>
          );
        })}
      </div>
    </div>
  );
};
