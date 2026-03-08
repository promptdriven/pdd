import React from 'react';
import { DIMENSIONS, COLORS } from './constants';

interface SlidingDividerProps {
  x: number;
  color: string;
  width: number;
  height: number;
}

export const SlidingDivider: React.FC<SlidingDividerProps> = ({
  x,
  color,
  width,
  height,
}) => {
  return (
    <>
      {/* Divider Line */}
      <div
        style={{
          position: 'absolute',
          left: x - width / 2,
          top: 0,
          width,
          height,
          backgroundColor: color,
          boxShadow: `0 0 20px ${COLORS.dividerGlow}`,
        }}
      />

      {/* Diamond Handle */}
      <div
        style={{
          position: 'absolute',
          left: x - DIMENSIONS.handleSize / 2,
          top: DIMENSIONS.handleY - DIMENSIONS.handleSize / 2,
          width: DIMENSIONS.handleSize,
          height: DIMENSIONS.handleSize,
          backgroundColor: color,
          transform: 'rotate(45deg)',
          boxShadow: `0 0 20px ${COLORS.dividerGlow}`,
        }}
      />
    </>
  );
};
