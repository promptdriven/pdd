import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, POSITIONS, ANIMATION_TIMING } from './constants';

export const FrostedPill: React.FC<{ children: React.ReactNode }> = ({
  children,
}) => {
  const frame = useCurrentFrame();

  // Slide in from right: translateX +200 → 0, opacity 0 → 1
  const slideInX = interpolate(
    frame,
    [ANIMATION_TIMING.slideInStart, ANIMATION_TIMING.slideInEnd],
    [ANIMATION_TIMING.slideDistance, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const fadeIn = interpolate(
    frame,
    [ANIMATION_TIMING.slideInStart, ANIMATION_TIMING.slideInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Slide out to left: translateX 0 → -200, opacity 1 → 0
  const slideOutX = interpolate(
    frame,
    [ANIMATION_TIMING.slideOutStart, ANIMATION_TIMING.slideOutEnd],
    [0, -ANIMATION_TIMING.slideOutDistance],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    }
  );

  const fadeOut = interpolate(
    frame,
    [ANIMATION_TIMING.slideOutStart, ANIMATION_TIMING.slideOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    }
  );

  // Combine slide phases
  const isExiting = frame >= ANIMATION_TIMING.slideOutStart;
  const translateX = isExiting ? slideOutX : slideInX;
  const opacity = isExiting ? fadeOut : fadeIn;

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.pillY,
        left: '50%',
        width: DIMENSIONS.pillWidth,
        height: DIMENSIONS.pillHeight,
        marginLeft: -DIMENSIONS.pillWidth / 2,
        borderRadius: DIMENSIONS.pillBorderRadius,
        backgroundColor: COLORS.pillBackground,
        backdropFilter: `blur(${DIMENSIONS.blurRadius}px)`,
        WebkitBackdropFilter: `blur(${DIMENSIONS.blurRadius}px)`,
        border: `1px solid ${COLORS.pillBorder}`,
        transform: `translateX(${translateX}px)`,
        opacity,
        overflow: 'hidden',
      }}
    >
      {children}
    </div>
  );
};
