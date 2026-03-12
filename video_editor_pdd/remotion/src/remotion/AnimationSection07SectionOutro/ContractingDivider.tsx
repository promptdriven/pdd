import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const ContractingDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [ANIMATION_TIMING.lineContractStart, ANIMATION_TIMING.lineContractEnd],
    [DIMENSIONS.dividerWidth, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: 340,
        transform: 'translate(-50%, -50%)',
        width,
        height: DIMENSIONS.dividerHeight,
        backgroundColor: COLORS.divider,
        opacity: DIMENSIONS.dividerOpacity,
      }}
    />
  );
};
