import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, POSITIONS, ANIMATION_TIMING } from './constants';

export const FrostedPill: React.FC<{ children: React.ReactNode }> = ({
  children,
}) => {
  const frame = useCurrentFrame();

  // Pill fade in: opacity 0 → 1
  const fadeIn = interpolate(
    frame,
    [ANIMATION_TIMING.pillFadeInStart, ANIMATION_TIMING.pillFadeInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Pill slide up: Y 800 → 780
  const slideY = interpolate(
    frame,
    [ANIMATION_TIMING.pillFadeInStart, ANIMATION_TIMING.pillFadeInEnd],
    [ANIMATION_TIMING.pillSlideFrom, ANIMATION_TIMING.pillSlideTo],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Fade out: opacity 1 → 0
  const fadeOut = interpolate(
    frame,
    [ANIMATION_TIMING.fadeOutStart, ANIMATION_TIMING.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  const opacity = Math.min(fadeIn, fadeOut);

  return (
    <div
      style={{
        position: 'absolute',
        top: slideY,
        left: '50%',
        transform: 'translateX(-50%)',
        height: DIMENSIONS.pillHeight,
        paddingLeft: DIMENSIONS.pillPaddingH,
        paddingRight: DIMENSIONS.pillPaddingH,
        borderRadius: DIMENSIONS.pillBorderRadius,
        backgroundColor: COLORS.pillBackground,
        backdropFilter: `blur(${DIMENSIONS.blurRadius}px)`,
        WebkitBackdropFilter: `blur(${DIMENSIONS.blurRadius}px)`,
        border: `1px solid ${COLORS.pillBorder}`,
        opacity,
        overflow: 'hidden',
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        whiteSpace: 'nowrap',
      }}
    >
      {children}
    </div>
  );
};
