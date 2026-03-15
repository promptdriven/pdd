import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  CHECKMARK,
  CHECKMARK_PATH,
  CHECKMARK_PATH_LENGTH,
  CIRCLE_CIRCUMFERENCE,
  TIMING,
} from './constants';

export const AnimatedCheckmark: React.FC = () => {
  const frame = useCurrentFrame();

  const { cx, cy, size, strokeWidth, circleRadius } = CHECKMARK;
  const halfSize = size / 2;

  // Circle draws via stroke-dashoffset: frames 6-12 with easeInOutCubic
  const circleProgress = interpolate(
    frame,
    [TIMING.checkmarkStart, TIMING.circleSplitFrame],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );
  const circleDashOffset = CIRCLE_CIRCUMFERENCE * (1 - circleProgress);

  // Check path draws: frames 12-16 with easeInOutCubic
  const checkProgress = interpolate(
    frame,
    [TIMING.circleSplitFrame, TIMING.checkmarkEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );
  const checkDashOffset = CHECKMARK_PATH_LENGTH * (1 - checkProgress);

  // Glow fades in as checkmark draws
  const glowOpacity = interpolate(
    frame,
    [TIMING.checkmarkStart, TIMING.checkmarkEnd],
    [0, CHECKMARK.glowOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  const viewBox = `0 0 ${size} ${size}`;

  return (
    <>
      {/* Glow layer behind checkmark */}
      <div
        style={{
          position: 'absolute',
          left: cx - size,
          top: cy - size,
          width: size * 2,
          height: size * 2,
          borderRadius: '50%',
          background: `radial-gradient(circle, ${COLORS.glow} 0%, transparent 70%)`,
          opacity: glowOpacity,
          filter: `blur(${CHECKMARK.glowBlur}px)`,
          pointerEvents: 'none',
        }}
      />
      {/* Checkmark SVG */}
      <div
        style={{
          position: 'absolute',
          left: cx - halfSize,
          top: cy - halfSize,
          width: size,
          height: size,
        }}
      >
        <svg width={size} height={size} viewBox={viewBox} fill="none">
          {/* Circle outline — 40% opacity accent, drawn first */}
          <circle
            cx={halfSize}
            cy={halfSize}
            r={circleRadius}
            fill="none"
            stroke={COLORS.accent}
            strokeWidth={strokeWidth}
            opacity={0.4}
            strokeDasharray={CIRCLE_CIRCUMFERENCE}
            strokeDashoffset={circleDashOffset}
          />
          {/* Checkmark path — draws after circle */}
          <path
            d={CHECKMARK_PATH}
            stroke={COLORS.accent}
            strokeWidth={strokeWidth}
            strokeLinecap="round"
            strokeLinejoin="round"
            fill="none"
            strokeDasharray={CHECKMARK_PATH_LENGTH}
            strokeDashoffset={checkDashOffset}
          />
        </svg>
      </div>
    </>
  );
};
