import React from 'react';
import { useCurrentFrame, spring, interpolate } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, DIMENSIONS, ANIMATION, BADGE_LABEL } from './constants';

const PlayIcon: React.FC<{ rotation: number }> = ({ rotation }) => (
  <svg
    width={DIMENSIONS.playIconSize * 2}
    height={DIMENSIONS.playIconSize * 2}
    viewBox="0 0 16 16"
    style={{
      marginRight: 8,
      transform: `rotate(${rotation}deg)`,
      flexShrink: 0,
    }}
  >
    <polygon points="4,2 14,8 4,14" fill={COLORS.badgeIcon} />
  </svg>
);

export const BadgePill: React.FC = () => {
  const frame = useCurrentFrame();

  // Badge appears starting at frame 8
  const badgeFrame = Math.max(0, frame - ANIMATION.badgeSlideStart);

  // Spring-based slide in
  const slideProgress = spring({
    frame: badgeFrame,
    fps: 30,
    config: { damping: 14, stiffness: 180 },
  });

  const translateX = interpolate(slideProgress, [0, 1], [-ANIMATION.badgeSlideDistance, 0]);

  // Play icon spin: 360° over the same spring
  const iconRotation = interpolate(slideProgress, [0, 1], [0, 360]);

  // Only render after badge slide starts
  if (frame < ANIMATION.badgeSlideStart) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.badgeX,
        top: POSITIONS.badgeY,
        width: DIMENSIONS.badgeWidth,
        height: DIMENSIONS.badgeHeight,
        borderRadius: DIMENSIONS.badgeBorderRadius,
        backgroundColor: COLORS.badgeBg,
        border: `1px solid ${COLORS.badgeBorder}`,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        transform: `translateX(${translateX}px)`,
      }}
    >
      <PlayIcon rotation={iconRotation} />
      <span
        style={{
          color: COLORS.badgeText,
          fontSize: TYPOGRAPHY.badge.fontSize,
          fontFamily: TYPOGRAPHY.badge.fontFamily,
          fontWeight: TYPOGRAPHY.badge.fontWeight,
          letterSpacing: TYPOGRAPHY.badge.letterSpacing,
          textTransform: TYPOGRAPHY.badge.textTransform,
          whiteSpace: 'nowrap',
        }}
      >
        {BADGE_LABEL}
      </span>
    </div>
  );
};
