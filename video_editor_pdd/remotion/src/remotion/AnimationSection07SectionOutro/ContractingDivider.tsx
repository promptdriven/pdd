import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const ContractingDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [ANIMATION_TIMING.dividerContractStart, ANIMATION_TIMING.dividerContractEnd],
    [DIMENSIONS.dividerStartWidth, DIMENSIONS.dividerEndWidth],
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
        left: (CANVAS.width - width) / 2,
        top: DIMENSIONS.dividerY,
        width,
        height: DIMENSIONS.dividerHeight,
        backgroundColor: COLORS.divider,
      }}
    />
  );
};
