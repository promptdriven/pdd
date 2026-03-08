import React from 'react';
import { AbsoluteFill } from 'remotion';
import { POSITIONS, COLORS } from './constants';

export const RadialSpotlight: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(circle at ${POSITIONS.monogramCenterX}px ${POSITIONS.monogramCenterY + 40}px, ${COLORS.spotlightColor} 0%, transparent 60%)`,
      }}
    />
  );
};
