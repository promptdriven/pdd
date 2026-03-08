import React from 'react';
import { useCurrentFrame, spring, interpolate } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, DIMENSIONS, ANIMATION, BADGE_LABEL } from './constants';

const AiSparkIcon: React.FC<{ opacity: number }> = ({ opacity }) => (
  <svg
    width={DIMENSIONS.iconSize}
    height={DIMENSIONS.iconSize}
    viewBox="0 0 16 16"
    style={{ marginRight: 8, flexShrink: 0, opacity }}
  >
    <path
      d="M8 0L9.5 5.5L16 8L9.5 10.5L8 16L6.5 10.5L0 8L6.5 5.5Z"
      fill={COLORS.badgeIcon}
    />
  </svg>
);

export const BadgePill: React.FC = () => {
  const frame = useCurrentFrame();

  // Scale-in with spring from frame 0
  const scaleProgress = spring({
    frame: Math.max(0, frame - ANIMATION.badgeScaleStart),
    fps: 30,
    config: { damping: 12, stiffness: 200 },
  });

  const scale = interpolate(scaleProgress, [0, 1], [0.3, 1]);
  const badgeOpacity = interpolate(scaleProgress, [0, 1], [0, 1]);

  // Pulsing glow effect
  const glowPhase = (frame % ANIMATION.badgeGlowCycleFrames) / ANIMATION.badgeGlowCycleFrames;
  const glowOpacity = interpolate(
    Math.sin(glowPhase * Math.PI * 2),
    [-1, 1],
    [ANIMATION.badgeGlowMinOpacity, ANIMATION.badgeGlowMaxOpacity],
  );

  // Icon sparkle: pulse in sync with glow
  const iconOpacity = interpolate(
    Math.sin(glowPhase * Math.PI * 2 + Math.PI * 0.5),
    [-1, 1],
    [0.6, 1],
  );

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
        boxShadow: `0 0 20px ${COLORS.badgeGlow}`,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        transform: `scale(${scale})`,
        opacity: badgeOpacity * glowOpacity + (1 - glowOpacity) * badgeOpacity * 0.7,
      }}
    >
      <AiSparkIcon opacity={iconOpacity} />
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
