import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame } from 'remotion';
import { CANVAS, COLORS, OPACITIES, TIMING } from './constants';

export const BlueprintGrid: React.FC = () => {
  const frame = useCurrentFrame();
  const spacing = 60;

  const bgOpacity = interpolate(frame, [0, TIMING.bgFadeEnd], [0, 1], {
    extrapolateRight: 'clamp',
  });

  const gridOpacity = interpolate(frame, [0, TIMING.bgFadeEnd], [0, OPACITIES.blueprintGrid], {
    extrapolateRight: 'clamp',
  });

  const verticalLines: React.ReactNode[] = [];
  const horizontalLines: React.ReactNode[] = [];

  for (let x = 0; x <= CANVAS.WIDTH; x += spacing) {
    verticalLines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS.HEIGHT}
        stroke={COLORS.blueprintGrid}
        strokeWidth={0.5}
      />
    );
  }

  for (let y = 0; y <= CANVAS.HEIGHT; y += spacing) {
    horizontalLines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS.WIDTH}
        y2={y}
        stroke={COLORS.blueprintGrid}
        strokeWidth={0.5}
      />
    );
  }

  return (
    <AbsoluteFill>
      <AbsoluteFill
        style={{
          backgroundColor: COLORS.background,
          opacity: bgOpacity,
        }}
      />
      <svg
        width={CANVAS.WIDTH}
        height={CANVAS.HEIGHT}
        style={{ opacity: gridOpacity, position: 'absolute' }}
      >
        {verticalLines}
        {horizontalLines}
      </svg>
    </AbsoluteFill>
  );
};
