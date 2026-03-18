import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame } from 'remotion';
import { CANVAS, GRID, TIMING } from './constants';

export const BlueprintGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, TIMING.BG_FADE_END], [0, 1], {
    extrapolateRight: 'clamp',
  });

  const cols = Math.ceil(CANVAS.WIDTH / GRID.SPACING);
  const rows = Math.ceil(CANVAS.HEIGHT / GRID.SPACING);

  const lines: React.ReactNode[] = [];

  // Vertical lines
  for (let i = 0; i <= cols; i++) {
    lines.push(
      <line
        key={`v-${i}`}
        x1={i * GRID.SPACING}
        y1={0}
        x2={i * GRID.SPACING}
        y2={CANVAS.HEIGHT}
        stroke={GRID.COLOR}
        strokeWidth={0.5}
        opacity={GRID.OPACITY}
      />
    );
  }

  // Horizontal lines
  for (let j = 0; j <= rows; j++) {
    lines.push(
      <line
        key={`h-${j}`}
        x1={0}
        y1={j * GRID.SPACING}
        x2={CANVAS.WIDTH}
        y2={j * GRID.SPACING}
        stroke={GRID.COLOR}
        strokeWidth={0.5}
        opacity={GRID.OPACITY}
      />
    );
  }

  return (
    <AbsoluteFill style={{ opacity }}>
      <svg
        width={CANVAS.WIDTH}
        height={CANVAS.HEIGHT}
        viewBox={`0 0 ${CANVAS.WIDTH} ${CANVAS.HEIGHT}`}
      >
        {lines}
      </svg>
    </AbsoluteFill>
  );
};
