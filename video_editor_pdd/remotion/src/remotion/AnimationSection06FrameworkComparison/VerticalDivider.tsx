import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const VerticalDivider: React.FC = () => {
  const frame = useCurrentFrame();

  // Divider draws top-to-bottom (linear easing)
  const dividerHeight = interpolate(
    frame,
    [ANIMATION_TIMING.dividerStart, ANIMATION_TIMING.dividerEnd],
    [0, CANVAS.height],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.halfWidth - DIMENSIONS.dividerWidth / 2,
        top: 0,
        width: DIMENSIONS.dividerWidth,
        height: dividerHeight,
        backgroundColor: COLORS.divider,
      }}
    />
  );
};
