import React, { useMemo } from 'react';
import { DOT_GRID_SPACING, DOT_GRID_COLOR, DOT_GRID_OPACITY, WIDTH, HEIGHT } from './constants';

export const DotGrid: React.FC = () => {
  const dots = useMemo(() => {
    const cols = Math.ceil(WIDTH / DOT_GRID_SPACING);
    const rows = Math.ceil(HEIGHT / DOT_GRID_SPACING);
    const result: React.ReactNode[] = [];
    for (let r = 0; r < rows; r++) {
      for (let c = 0; c < cols; c++) {
        result.push(
          <circle
            key={`${r}-${c}`}
            cx={c * DOT_GRID_SPACING}
            cy={r * DOT_GRID_SPACING}
            r={1}
            fill={DOT_GRID_COLOR}
          />
        );
      }
    }
    return result;
  }, []);

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        opacity: DOT_GRID_OPACITY,
        pointerEvents: 'none',
      }}
    >
      {dots}
    </svg>
  );
};

export default DotGrid;
