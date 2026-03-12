import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  ANIMATION,
  type SplitNatureComparisonLayout,
} from './constants';

export const VerticalDivider: React.FC<{ layout: SplitNatureComparisonLayout }> = ({
  layout,
}) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [ANIMATION.dividerDrawStart, ANIMATION.dividerDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: layout.positions.dividerX - layout.dimensions.dividerWidth / 2,
        top: 0,
        width: layout.dimensions.dividerWidth,
        height: layout.height * drawProgress,
        backgroundColor: COLORS.divider,
      }}
    />
  );
};
