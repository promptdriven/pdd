import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { BADGE, COLORS, TYPOGRAPHY, ANIMATION } from './constants';

export const VoiceBadge: React.FC = () => {
  const frame = useCurrentFrame();

  // Slide in from right: translateX 40 → 0
  const slideX = interpolate(
    frame,
    [ANIMATION.badgeSlideStart, ANIMATION.badgeSlideEnd],
    [BADGE.slideDistance, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Fade in alongside slide
  const opacity = interpolate(
    frame,
    [ANIMATION.badgeSlideStart, ANIMATION.badgeSlideEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: BADGE.x,
        top: BADGE.y,
        paddingLeft: BADGE.paddingX,
        paddingRight: BADGE.paddingX,
        paddingTop: BADGE.paddingY,
        paddingBottom: BADGE.paddingY,
        borderRadius: BADGE.borderRadius,
        backgroundColor: COLORS.badgeBackground,
        border: `1px solid ${COLORS.badgeBorder}`,
        transform: `translateX(${slideX}px)`,
        opacity,
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.badge.fontFamily,
          fontSize: TYPOGRAPHY.badge.fontSize,
          fontWeight: TYPOGRAPHY.badge.fontWeight,
          color: COLORS.badgeText,
          whiteSpace: 'nowrap',
        }}
      >
        {BADGE.text}
      </span>
    </div>
  );
};
