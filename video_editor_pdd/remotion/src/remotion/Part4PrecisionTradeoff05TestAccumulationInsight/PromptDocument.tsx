import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface PromptDocumentProps {
  width: number;
  height: number;
  lineCount: number;
  lineColor: string;
  lineOpacity: number;
  animStartFrame: number;
  animDuration: number;
}

/**
 * Renders a rectangular "prompt document" with horizontal lines
 * that draw in sequentially to represent lines of a prompt.
 */
const PromptDocument: React.FC<PromptDocumentProps> = ({
  width,
  height,
  lineCount,
  lineColor,
  lineOpacity,
  animStartFrame,
  animDuration,
}) => {
  const frame = useCurrentFrame();
  const padding = 10;
  const lineSpacing = (height - padding * 2) / (lineCount + 1);

  return (
    <div
      style={{
        width,
        height,
        backgroundColor: '#1E293B',
        borderRadius: 4,
        position: 'relative',
        overflow: 'hidden',
      }}
    >
      {Array.from({ length: lineCount }).map((_, i) => {
        // Each line draws with a 2-frame stagger
        const lineStart = animStartFrame + i * 2;
        const lineProgress = interpolate(
          frame,
          [lineStart, lineStart + 8],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        // Vary line widths for visual interest
        const lineWidth = width - padding * 2 - (i % 3 === 2 ? 20 : i % 5 === 0 ? 30 : 0);
        const yPos = padding + lineSpacing * (i + 1);

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: padding,
              top: yPos - 1,
              width: lineWidth * lineProgress,
              height: 2,
              backgroundColor: lineColor,
              opacity: lineOpacity,
              borderRadius: 1,
            }}
          />
        );
      })}
    </div>
  );
};

export default PromptDocument;
