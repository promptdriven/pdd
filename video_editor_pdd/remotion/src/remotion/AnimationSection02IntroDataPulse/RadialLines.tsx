import React from 'react';
import { CANVAS, RADIAL_LINES } from './constants';

export const RadialLines: React.FC = () => {
  const lines = [];
  const angleStep = (2 * Math.PI) / RADIAL_LINES.count;

  for (let i = 0; i < RADIAL_LINES.count; i++) {
    const angle = angleStep * i;
    const endX = CANVAS.centerX + Math.cos(angle) * RADIAL_LINES.maxRadius;
    const endY = CANVAS.centerY + Math.sin(angle) * RADIAL_LINES.maxRadius;

    lines.push(
      <line
        key={i}
        x1={CANVAS.centerX}
        y1={CANVAS.centerY}
        x2={endX}
        y2={endY}
        stroke={RADIAL_LINES.color}
        strokeWidth={RADIAL_LINES.strokeWidth}
        opacity={RADIAL_LINES.opacity}
      />
    );
  }

  return (
    <svg
      width={CANVAS.width}
      height={CANVAS.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {lines}
    </svg>
  );
};
