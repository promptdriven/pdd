import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface CodeBlockProps {
  x: number;
  y: number;
  width: number;
  height: number;
  lines: string[];
  genStart: number;
  lineRate: number;
  glowColor: string;
  glowDuration: number;
  codeTextColor: string;
  codeBgColor: string;
}

const CodeBlock: React.FC<CodeBlockProps> = ({
  x,
  y,
  width,
  height,
  lines,
  genStart,
  lineRate,
  glowColor,
  glowDuration,
  codeTextColor,
  codeBgColor,
}) => {
  const frame = useCurrentFrame();

  // Calculate how many lines are visible based on current frame
  const elapsedSinceStart = Math.max(0, frame - genStart);
  const visibleLineCount = Math.min(
    lines.length,
    Math.floor(elapsedSinceStart / lineRate)
  );

  // All lines revealed => glow
  const allRevealed = visibleLineCount >= lines.length;
  const glowStartFrame = genStart + lines.length * lineRate;

  const glowOpacity = allRevealed
    ? interpolate(
        frame,
        [glowStartFrame, glowStartFrame + glowDuration],
        [0, 0.7],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.cubic),
        }
      )
    : 0;

  // Block fade in
  const blockOpacity = interpolate(
    frame,
    [genStart, genStart + 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height,
        opacity: blockOpacity,
      }}
    >
      {/* Glow border */}
      <div
        style={{
          position: 'absolute',
          inset: -3,
          borderRadius: 8,
          border: `2px solid ${glowColor}`,
          opacity: glowOpacity,
          boxShadow: `0 0 16px ${glowColor}, 0 0 32px ${glowColor}`,
          pointerEvents: 'none',
        }}
      />

      {/* Code container */}
      <div
        style={{
          width: '100%',
          height: '100%',
          backgroundColor: codeBgColor,
          borderRadius: 6,
          padding: '12px 14px',
          boxSizing: 'border-box',
          overflow: 'hidden',
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 11,
          lineHeight: '16px',
          color: codeTextColor,
        }}
      >
        {lines.slice(0, visibleLineCount).map((line, i) => (
          <div
            key={i}
            style={{
              opacity: 0.7,
              whiteSpace: 'pre',
              height: 16,
            }}
          >
            {line}
          </div>
        ))}
      </div>
    </div>
  );
};

export default CodeBlock;
