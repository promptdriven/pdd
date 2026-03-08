import React from 'react';
import { COLORS, CANVAS } from './constants';

interface GridPatternProps {
  opacity: number;
}

export const GridPattern: React.FC<GridPatternProps> = ({ opacity }) => {
  return (
    <svg
      width={CANVAS.width}
      height={CANVAS.height}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        opacity,
      }}
    >
      <defs>
        <pattern
          id="grid-pattern"
          width="40"
          height="40"
          patternUnits="userSpaceOnUse"
        >
          <path
            d="M 40 0 L 0 0 0 40"
            fill="none"
            stroke={COLORS.grid}
            strokeWidth="1"
          />
        </pattern>
      </defs>
      <rect width="100%" height="100%" fill="url(#grid-pattern)" />
    </svg>
  );
};
