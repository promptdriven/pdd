import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  TYPOGRAPHY,
  POSITIONS,
  DIMENSIONS,
  ANIMATION,
  BADGE_TEXT,
} from './constants';
import { SparkleIcon } from './SparkleIcon';

export const BadgePill: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Slide in: frames 0-15, easeOutBack (slight overshoot) ---
  const slideInX = interpolate(
    frame,
    [ANIMATION.slideInStart, ANIMATION.slideInEnd],
    [POSITIONS.badgeOffscreenX, POSITIONS.badgeRestX],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    },
  );

  // --- Slide in opacity: 0→1 over same range ---
  const slideInOpacity = interpolate(
    frame,
    [ANIMATION.slideInStart, ANIMATION.slideInEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // --- Slide out: frames 75-90, easeInCubic ---
  const slideOutX = interpolate(
    frame,
    [ANIMATION.slideOutStart, ANIMATION.slideOutEnd],
    [POSITIONS.badgeRestX, POSITIONS.badgeOffscreenX],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(3)),
    },
  );

  const slideOutOpacity = interpolate(
    frame,
    [ANIMATION.slideOutStart, ANIMATION.slideOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(3)),
    },
  );

  // Composite X position: use slideIn before frame 75, slideOut after
  const posX = frame < ANIMATION.slideOutStart ? slideInX : slideOutX;
  const opacity = frame < ANIMATION.slideOutStart ? slideInOpacity : slideOutOpacity;

  // --- Breathing scale: frames 20-75 ---
  let scale = 1.0;
  if (frame >= ANIMATION.breathingStart && frame < ANIMATION.breathingEnd) {
    const breathFrame = frame - ANIMATION.breathingStart;
    const cycleProgress = (breathFrame % ANIMATION.breathingCycleDuration) / ANIMATION.breathingCycleDuration;
    // Sine wave: 0→1→0 maps to 1.0→1.03→1.0
    const sineValue = Math.sin(cycleProgress * Math.PI * 2);
    // Map sine [-1,1] to [1.0, 1.03] centered at 1.015
    scale = ANIMATION.breathingScaleMin + ((sineValue + 1) / 2) * (ANIMATION.breathingScaleMax - ANIMATION.breathingScaleMin);
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: posX,
        top: POSITIONS.badgeY,
        width: DIMENSIONS.badgeWidth,
        height: DIMENSIONS.badgeHeight,
        borderRadius: DIMENSIONS.badgeBorderRadius,
        backgroundColor: COLORS.badgeBg,
        backdropFilter: 'blur(8px)',
        WebkitBackdropFilter: 'blur(8px)',
        border: `1px solid ${COLORS.badgeBorder}`,
        boxShadow: COLORS.dropShadow,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
      }}
    >
      <SparkleIcon />
      <span
        style={{
          color: COLORS.badgeText,
          fontSize: TYPOGRAPHY.badge.fontSize,
          fontFamily: TYPOGRAPHY.badge.fontFamily,
          fontWeight: TYPOGRAPHY.badge.fontWeight,
          letterSpacing: TYPOGRAPHY.badge.letterSpacing,
          whiteSpace: 'nowrap',
        }}
      >
        {BADGE_TEXT}
      </span>
    </div>
  );
};
