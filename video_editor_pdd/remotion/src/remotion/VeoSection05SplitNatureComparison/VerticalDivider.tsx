import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  DIMENSIONS,
  ANIMATION,
  type SplitNatureComparisonLayout,
} from './constants';

export const VerticalDivider: React.FC<{ layout: SplitNatureComparisonLayout }> = ({
  layout,
}) => {
  const frame = useCurrentFrame();
  const scaledWidth = Math.max(2, DIMENSIONS.dividerWidth * layout.scaleX);
  const scaledLeft = layout.width / 2 - scaledWidth / 2;
  const fullHeight = DIMENSIONS.dividerHeight * layout.scaleY;
  const glowRadius = DIMENSIONS.dividerGlowRadius * layout.uniformScale;

  // Frame 8–18: divider draws top-to-bottom (height 0→full), easeInOutCubic
  const dividerHeight = interpolate(
    frame,
    [ANIMATION.dividerDrawStart, ANIMATION.dividerDrawEnd],
    [0, fullHeight],
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
        left: scaledLeft,
        top: 0,
        width: scaledWidth,
        height: dividerHeight,
        backgroundColor: COLORS.divider,
        boxShadow: `0 0 ${glowRadius}px ${COLORS.dividerGlow}`,
      }}
    />
  );
};
