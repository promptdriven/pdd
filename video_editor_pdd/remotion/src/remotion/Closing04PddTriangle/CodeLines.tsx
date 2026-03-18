import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { CODE_LINES_CONFIG, TIMING } from './constants';

export const CodeLines: React.FC = () => {
  const frame = useCurrentFrame();
  const { centerX, centerY, count, color, opacity, lineHeight, gap, widths } =
    CODE_LINES_CONFIG;
  const { start, fadeDuration, stagger } = TIMING.codeLines;

  const totalHeight = count * lineHeight + (count - 1) * gap;
  const startY = centerY - totalHeight / 2;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {Array.from({ length: count }).map((_, i) => {
        const lineStart = start + i * stagger;
        const lineOpacity = interpolate(
          frame,
          [lineStart, lineStart + fadeDuration],
          [0, opacity],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          },
        );

        if (lineOpacity <= 0) return null;

        const w = widths[i % widths.length];
        const y = startY + i * (lineHeight + gap);
        // Slight random-ish horizontal offset per line for visual variety
        const xOffset = ((i * 37 + 13) % 60) - 30;

        return (
          <rect
            key={i}
            x={centerX - w / 2 + xOffset}
            y={y}
            width={w}
            height={lineHeight - 2}
            rx={2}
            fill={color}
            opacity={lineOpacity}
          />
        );
      })}
    </svg>
  );
};
