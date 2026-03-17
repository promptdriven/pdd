import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CodeLineData,
  CENTER_X,
  CENTER_Y,
  CODE_LINE_COLOR,
  CODE_LINE_OPACITY,
} from './constants';

interface CodeLinesProps {
  lines: CodeLineData[];
  staggerFrames: number;
  totalFrames: number;
}

export const CodeLines: React.FC<CodeLinesProps> = ({
  lines,
  staggerFrames,
  totalFrames,
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
        const staggerDelay = i * staggerFrames;
        const lineStart = staggerDelay;
        const lineEnd = Math.min(lineStart + 8, totalFrames);

        // Width animates from 0 to full — streaming in from center
        const widthProgress = interpolate(
          frame,
          [lineStart, lineEnd],
          [0, 1],
          {
            extrapolateRight: 'clamp',
            extrapolateLeft: 'clamp',
            easing: Easing.out(Easing.poly(2)),
          }
        );

        // Opacity fades in
        const opacity = interpolate(
          frame,
          [lineStart, Math.min(lineStart + 5, totalFrames)],
          [0, CODE_LINE_OPACITY],
          { extrapolateRight: 'clamp', extrapolateLeft: 'clamp' }
        );

        if (widthProgress <= 0) return null;

        const currentWidth = line.width * widthProgress;
        const x = CENTER_X + line.offsetX - currentWidth / 2;
        const y = CENTER_Y + line.offsetY;

        return (
          <rect
            key={i}
            x={x}
            y={y}
            width={currentWidth}
            height={2}
            rx={1}
            fill={CODE_LINE_COLOR}
            opacity={opacity}
          />
        );
      })}
    </svg>
  );
};

/** Static code lines (no animation, just rendered at full opacity) */
export const StaticCodeLines: React.FC<{ lines: CodeLineData[] }> = ({
  lines,
}) => {
  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {lines.map((line, i) => {
        const x = CENTER_X + line.offsetX - line.width / 2;
        const y = CENTER_Y + line.offsetY;

        return (
          <rect
            key={i}
            x={x}
            y={y}
            width={line.width}
            height={2}
            rx={1}
            fill={CODE_LINE_COLOR}
            opacity={CODE_LINE_OPACITY}
          />
        );
      })}
    </svg>
  );
};
