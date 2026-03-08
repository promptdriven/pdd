import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TYPOGRAPHY } from './constants';

interface MilestoneCardProps {
  x: number;
  y: number;
  title: string;
  stat: string;
  delay: number;
  highlight?: boolean;
}

export const MilestoneCard: React.FC<MilestoneCardProps> = ({
  x,
  y,
  title,
  stat,
  delay,
  highlight = false,
}) => {
  const frame = useCurrentFrame();

  // Slide up/down animation with delay
  const isAbove = y < DIMENSIONS.timeline.y;
  const slideDistance = 40;
  const startY = isAbove ? y + slideDistance : y - slideDistance;

  const slideProgress = interpolate(frame, [delay, delay + 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.poly(4), // easeOutQuart
  });

  const currentY = startY + (y - startY) * slideProgress;

  // Fade in text
  const textOpacity = interpolate(frame, [delay + 10, delay + 25], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.quad),
  });

  // Floating animation after card appears
  const floatOffset = frame > delay + 30
    ? Math.sin((frame - delay - 30) / 30) * 2
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: currentY + floatOffset,
        transform: 'translateX(-50%)',
        width: DIMENSIONS.card.width,
        height: DIMENSIONS.card.height,
        backgroundColor: COLORS.cardBackground,
        border: `${DIMENSIONS.card.borderWidth}px solid ${
          highlight ? COLORS.timelineProgress : COLORS.cardBorder
        }`,
        borderRadius: DIMENSIONS.card.borderRadius,
        display: 'flex',
        flexDirection: 'column',
        justifyContent: 'center',
        alignItems: 'center',
        gap: 8,
        padding: 16,
        boxShadow: highlight
          ? `0 0 20px ${COLORS.timelineProgress}40`
          : 'none',
      }}
    >
      {/* Milestone title */}
      <div
        style={{
          fontFamily: TYPOGRAPHY.milestoneTitle.fontFamily,
          fontWeight: TYPOGRAPHY.milestoneTitle.fontWeight,
          fontSize: TYPOGRAPHY.milestoneTitle.fontSize,
          color: TYPOGRAPHY.milestoneTitle.color,
          textAlign: 'center',
          opacity: textOpacity,
          lineHeight: 1.2,
        }}
      >
        {title}
      </div>

      {/* Adoption stat */}
      <div
        style={{
          fontFamily: TYPOGRAPHY.stat.fontFamily,
          fontWeight: TYPOGRAPHY.stat.fontWeight,
          fontSize: TYPOGRAPHY.stat.fontSize,
          color: highlight ? COLORS.textWhite : TYPOGRAPHY.stat.color,
          textAlign: 'center',
          opacity: textOpacity,
        }}
      >
        {stat}
      </div>
    </div>
  );
};
