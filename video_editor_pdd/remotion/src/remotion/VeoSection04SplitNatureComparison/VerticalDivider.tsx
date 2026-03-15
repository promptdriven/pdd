import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  DIMENSIONS,
  ANIMATION,
  type SplitComparisonLayout,
} from './constants';

export const VerticalDivider: React.FC<{ layout: SplitComparisonLayout }> = ({
  layout,
}) => {
  const frame = useCurrentFrame();
  const scaledWidth = Math.max(2, DIMENSIONS.dividerWidth * layout.scaleX);
  const scaledLeft = layout.width / 2 - scaledWidth / 2;
  const fullHeight = DIMENSIONS.dividerHeight * layout.scaleY;
  const glowRadius = DIMENSIONS.dividerGlowRadius * layout.uniformScale;

  // Divider is visible from frame 0 (already at center during wipe)
  // Frame 10–30: subtle shimmer (opacity oscillates 0.85–1.0)
  const shimmerCycle = interpolate(
    frame,
    [ANIMATION.shimmerStart, ANIMATION.shimmerEnd],
    [0, Math.PI * 3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  const shimmerOpacity =
    frame < ANIMATION.shimmerStart
      ? 1.0
      : ANIMATION.shimmerOpacityMin +
        (ANIMATION.shimmerOpacityMax - ANIMATION.shimmerOpacityMin) *
          ((Math.sin(shimmerCycle) + 1) / 2);

  return (
    <div
      style={{
        position: 'absolute',
        left: scaledLeft,
        top: 0,
        width: scaledWidth,
        height: fullHeight,
        backgroundColor: COLORS.divider,
        boxShadow: `0 0 ${glowRadius}px ${COLORS.dividerGlow}`,
        opacity: shimmerOpacity,
      }}
    />
  );
};
