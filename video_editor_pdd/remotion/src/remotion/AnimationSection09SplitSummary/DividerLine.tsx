import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { DIVIDER, INTRINSIC_FRAMES } from './constants';

export const DividerLine: React.FC = () => {
  const frame = useCurrentFrame();

  const x = interpolate(frame, [0, INTRINSIC_FRAMES], [DIVIDER.startX, DIVIDER.endX], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        bottom: 0,
        left: x,
        width: DIVIDER.width,
        backgroundColor: DIVIDER.color,
        boxShadow: `0 0 18px 4px ${DIVIDER.color}66`,
      }}
    />
  );
};
