import React from 'react';
import { AbsoluteFill } from 'remotion';

interface DotGridProps {
  spacing?: number;
  color?: string;
  opacity?: number;
}

export const DotGrid: React.FC<DotGridProps> = ({
  spacing = 30,
  color = '#1E293B',
  opacity = 0.03,
}) => {
  const dots: React.ReactNode[] = [];
  const cols = Math.ceil(1920 / spacing);
  const rows = Math.ceil(1080 / spacing);

  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      dots.push(
        <circle
          key={`${r}-${c}`}
          cx={c * spacing}
          cy={r * spacing}
          r={1}
          fill={color}
        />
      );
    }
  }

  return (
    <AbsoluteFill style={{ opacity }}>
      <svg width={1920} height={1080} viewBox="0 0 1920 1080">
        {dots}
      </svg>
    </AbsoluteFill>
  );
};
