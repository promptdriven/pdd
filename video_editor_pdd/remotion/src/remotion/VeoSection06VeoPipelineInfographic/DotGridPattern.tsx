import React from 'react';
import { COLORS, DIMENSIONS } from './constants';

export const DotGridPattern: React.FC = () => {
  const spacing = DIMENSIONS.dotGridSpacing;
  const dotColor = COLORS.dotGrid;

  return (
    <svg
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '100%',
        height: '100%',
        pointerEvents: 'none',
      }}
    >
      <defs>
        <pattern
          id="pipelineDotGrid"
          x="0"
          y="0"
          width={spacing}
          height={spacing}
          patternUnits="userSpaceOnUse"
        >
          <circle cx={spacing / 2} cy={spacing / 2} r={1.5} fill={dotColor} />
        </pattern>
      </defs>
      <rect width="100%" height="100%" fill="url(#pipelineDotGrid)" />
    </svg>
  );
};
