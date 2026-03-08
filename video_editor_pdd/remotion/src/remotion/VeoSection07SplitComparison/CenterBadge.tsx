import React from 'react';
import { useCurrentFrame, interpolate, spring } from 'remotion';
import { COLORS, POSITIONS, DIMENSIONS, TYPOGRAPHY, ANIMATION } from './constants';

export const CenterBadge: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - ANIMATION.badgePopStart;
  if (localFrame < 0) return null;

  const scale = spring({
    frame: localFrame,
    fps: 30,
    config: {
      damping: 10,
      stiffness: 200,
    },
  });

  const opacity = interpolate(localFrame, [0, 5], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.dividerX - DIMENSIONS.badgeWidth / 2,
        top: POSITIONS.badgeY - DIMENSIONS.badgeHeight / 2,
        width: DIMENSIONS.badgeWidth,
        height: DIMENSIONS.badgeHeight,
        borderRadius: DIMENSIONS.badgeBorderRadius,
        backgroundColor: COLORS.badgeBg,
        border: `1.5px solid ${COLORS.badgeBorder}`,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        transform: `scale(${scale})`,
        opacity,
        zIndex: 20,
        boxShadow: '0 4px 20px rgba(0,0,0,0.4)',
      }}
    >
      <span
        style={{
          color: COLORS.badgeText,
          fontFamily: TYPOGRAPHY.badge.fontFamily,
          fontWeight: TYPOGRAPHY.badge.fontWeight,
          fontSize: TYPOGRAPHY.badge.fontSize,
          letterSpacing: '1px',
        }}
      >
        Veo 3.1
      </span>
    </div>
  );
};
