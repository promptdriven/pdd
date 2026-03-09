import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { ANIMATION } from './constants';

export const DimmingOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION.dimFadeStart, ANIMATION.dimFadeEnd],
    [0, 0.7],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        backgroundColor: `rgba(0, 0, 0, ${opacity})`,
      }}
    />
  );
};
