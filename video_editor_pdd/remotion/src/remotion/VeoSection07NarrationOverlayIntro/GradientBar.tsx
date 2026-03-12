import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION, type NarrationOverlayLayout } from './constants';

export const GradientBar: React.FC<{ layout: NarrationOverlayLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Frame 10-15: Accent bar fades in
  const opacity = interpolate(
    frame,
    [ANIMATION.accentFadeStart, ANIMATION.accentFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 0,
        left: 0,
        width: layout.pill.width,
        height: layout.dimensions.accentBarHeight,
        borderRadius: `0 0 ${layout.pill.borderRadius}px ${layout.pill.borderRadius}px`,
        background: `linear-gradient(90deg, ${COLORS.accentGradientStart} 0%, ${COLORS.accentGradientEnd} 100%)`,
        opacity,
      }}
    />
  );
};
