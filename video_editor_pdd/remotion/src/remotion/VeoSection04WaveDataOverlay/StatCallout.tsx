import React from 'react';
import { useCurrentFrame, interpolate, Easing, spring, useVideoConfig } from 'remotion';
import { COLORS, ANIMATION, DIMENSIONS, type WaveOverlayLayout } from './constants';

interface StatCalloutProps {
  layout: WaveOverlayLayout;
  label: string;
  value: string;
  x: number;
  y: number;
  delayFrames: number;
}

export const StatCallout: React.FC<StatCalloutProps> = ({
  layout,
  label,
  value,
  x,
  y,
  delayFrames,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const appearFrame = ANIMATION.badgeStartFrame + delayFrames;

  // easeOutBack pop-in: scale from 0.8 -> 1.0 with fade
  const opacity = interpolate(
    frame,
    [appearFrame, appearFrame + ANIMATION.badgeFadeDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  const scale = spring({
    frame: Math.max(0, frame - appearFrame),
    fps,
    config: {
      damping: 12,
      stiffness: 150,
      mass: 0.8,
    },
  });

  // Scale position to current canvas size
  const px = x * layout.scaleX;
  const py = y * layout.scaleY;

  return (
    <div
      style={{
        position: 'absolute',
        left: px,
        top: py,
        opacity,
        transform: `scale(${0.8 + 0.2 * scale})`,
        transformOrigin: 'center center',
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'flex-start',
        gap: 4,
        padding: `${DIMENSIONS.badgePaddingY}px ${DIMENSIONS.badgePaddingX}px`,
        backgroundColor: COLORS.badgeBg,
        border: `${DIMENSIONS.badgeBorderWidth}px solid ${COLORS.badgeBorder}`,
        borderRadius: DIMENSIONS.badgeBorderRadius,
      }}
    >
      <span
        style={{
          fontFamily: layout.typography.badgeLabel.fontFamily,
          fontSize: layout.typography.badgeLabel.fontSize,
          fontWeight: layout.typography.badgeLabel.fontWeight,
          color: COLORS.badgeLabel,
          lineHeight: 1.2,
        }}
      >
        {label}
      </span>
      <span
        style={{
          fontFamily: layout.typography.badgeValue.fontFamily,
          fontSize: layout.typography.badgeValue.fontSize,
          fontWeight: layout.typography.badgeValue.fontWeight,
          color: COLORS.badgeValue,
          lineHeight: 1.2,
        }}
      >
        {value}
      </span>
    </div>
  );
};
