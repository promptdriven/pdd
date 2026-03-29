import React from 'react';
import { AbsoluteFill } from 'remotion';

interface BlueprintGridProps {
  spacing: number;
  color: string;
  opacity: number;
}

const BlueprintGrid: React.FC<BlueprintGridProps> = ({
  spacing,
  color,
  opacity,
}) => {
  const lines: React.ReactNode[] = [];

  // Vertical lines
  for (let x = 0; x <= 1920; x += spacing) {
    lines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={1080}
        stroke={color}
        strokeWidth={1}
      />
    );
  }

  // Horizontal lines
  for (let y = 0; y <= 1080; y += spacing) {
    lines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={1920}
        y2={y}
        stroke={color}
        strokeWidth={1}
      />
    );
  }

  return (
    <AbsoluteFill style={{ opacity }}>
      <svg width={1920} height={1080} viewBox="0 0 1920 1080">
        {lines}
      </svg>
    </AbsoluteFill>
  );
};

export default BlueprintGrid;
