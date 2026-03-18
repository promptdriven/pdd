import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, LINE_HEIGHT, GUTTER_WIDTH } from './constants';

interface ScrollingCodeBlockProps {
  lines: string[];
  panelX: number;
  panelWidth: number;
  y: number;
  /** Frame at which scrolling starts */
  startFrame: number;
  /** Lines revealed per frame */
  scrollSpeed: number;
  /** Max visible height in px */
  maxHeight: number;
}

export const ScrollingCodeBlock: React.FC<ScrollingCodeBlockProps> = ({
  lines,
  panelX,
  panelWidth,
  y,
  startFrame,
  scrollSpeed,
  maxHeight,
}) => {
  const frame = useCurrentFrame();

  // How many lines have been revealed so far
  const elapsed = Math.max(0, frame - startFrame);
  const revealedCount = Math.min(
    lines.length,
    Math.floor(elapsed * scrollSpeed),
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX,
        top: y,
        width: panelWidth,
        height: maxHeight,
        overflow: 'hidden',
      }}
    >
      {lines.map((line, i) => {
        if (i >= revealedCount) return null;

        const lineNum = i + 1;
        const lineOpacity = interpolate(
          elapsed,
          [i / scrollSpeed, i / scrollSpeed + 2],
          [0, 0.7],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
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
            {/* Line number gutter */}
            <span
              style={{
                width: GUTTER_WIDTH,
                textAlign: 'right',
                paddingRight: 8,
                fontFamily: '"JetBrains Mono", monospace',
                fontSize: 10,
                color: COLORS.lineNumberColor,
                opacity: 0.3,
                flexShrink: 0,
              }}
            >
              {lineNum}
            </span>
            {/* Code text */}
            <span
              style={{
                fontFamily: '"JetBrains Mono", monospace',
                fontSize: 10,
                color: COLORS.codeTextColor,
                whiteSpace: 'pre',
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
