import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { MONO_FONT, COLORS, LINE_HEIGHT, GUTTER_WIDTH } from './constants';

const ScrollingCode: React.FC<{
  lines: string[];
  x: number;
  y: number;
  width: number;
  maxHeight: number;
  scrollSpeed: number;
  startFrame: number;
  showLineNumbers?: boolean;
  fontSize?: number;
  lineColor?: string;
  lineNumberColor?: string;
}> = ({
  lines,
  x,
  y,
  width,
  maxHeight,
  scrollSpeed,
  startFrame,
  showLineNumbers = true,
  fontSize = 10,
  lineColor = COLORS.codeColor,
  lineNumberColor = COLORS.lineNumberColor,
}) => {
  const frame = useCurrentFrame();
  const elapsed = Math.max(0, frame - startFrame);

  // Number of lines revealed so far
  const revealedCount = Math.min(
    lines.length,
    Math.floor(elapsed * scrollSpeed)
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width,
        height: maxHeight,
        overflow: 'hidden',
      }}
    >
      {lines.slice(0, revealedCount).map((line, i) => {
        // Per-line fade-in
        const lineAppearFrame = startFrame + i / scrollSpeed;
        const lineOpacity = interpolate(
          frame,
          [lineAppearFrame, lineAppearFrame + 3],
          [0, 0.7],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        return (
          <div
            key={i}
            style={{
              display: 'flex',
              height: LINE_HEIGHT,
              alignItems: 'center',
              opacity: lineOpacity,
            }}
          >
            {showLineNumbers && (
              <span
                style={{
                  fontFamily: MONO_FONT,
                  fontSize,
                  color: lineNumberColor,
                  opacity: 0.3,
                  width: GUTTER_WIDTH,
                  textAlign: 'right',
                  paddingRight: 8,
                  flexShrink: 0,
                  userSelect: 'none',
                }}
              >
                {i + 1}
              </span>
            )}
            <span
              style={{
                fontFamily: MONO_FONT,
                fontSize,
                color: lineColor,
                whiteSpace: 'pre',
                overflow: 'hidden',
                textOverflow: 'ellipsis',
              }}
            >
              {line}
            </span>
          </div>
        );
      })}
    </div>
  );
};

export default ScrollingCode;
