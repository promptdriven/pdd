// CodeLines.tsx — Horizontal code-representation lines streaming into center
import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { CODE_COLOR, CODE_OPACITY } from './constants';

interface CodeLineSpec {
  readonly width: number;
  readonly offsetX: number;
  readonly offsetY: number;
}

interface CodeLinesProps {
  lines: readonly CodeLineSpec[];
  centerX: number;
  centerY: number;
  stagger: number;
  totalDuration: number;
}

export const CodeLines: React.FC<CodeLinesProps> = ({
  lines,
  centerX,
  centerY,
  stagger,
  totalDuration,
}) => {
  const frame = useCurrentFrame();

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {lines.map((line, i) => {
        const lineDelay = i * stagger;
        const lineDuration = Math.max(1, totalDuration - lineDelay);

        // Scale from 0 to full width (stream in from center)
        const scaleProgress = interpolate(
          frame,
          [lineDelay, lineDelay + Math.min(lineDuration, 12)],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        // Fade in
        const opacity = interpolate(
          frame,
          [lineDelay, lineDelay + Math.min(lineDuration, 8)],
          [0, CODE_OPACITY],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }
        );

        if (opacity <= 0) return null;

        const x = centerX + line.offsetX - (line.width * scaleProgress) / 2;
        const y = centerY + line.offsetY;
        const displayWidth = line.width * scaleProgress;

        return (
          <rect
            key={i}
            x={x}
            y={y}
            width={Math.max(0, displayWidth)}
            height={3}
            rx={1.5}
            fill={CODE_COLOR}
            opacity={opacity}
          />
        );
      })}
    </svg>
  );
};
