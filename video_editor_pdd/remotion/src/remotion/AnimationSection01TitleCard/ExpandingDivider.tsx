import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const ExpandingDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [ANIMATION_TIMING.dividerExpandStart, ANIMATION_TIMING.dividerExpandEnd],
    [0, DIMENSIONS.dividerWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: `calc(50% + 28px + ${DIMENSIONS.dividerOffsetY}px)`,
        transform: 'translateX(-50%)',
        width,
        height: DIMENSIONS.dividerHeight,
        backgroundColor: COLORS.divider,
        opacity: DIMENSIONS.dividerOpacity,
      }}
    />
  );
};
