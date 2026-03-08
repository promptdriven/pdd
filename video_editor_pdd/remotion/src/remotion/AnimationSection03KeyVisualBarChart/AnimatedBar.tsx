import React from 'react';
import { interpolate, spring, useCurrentFrame, useVideoConfig, Easing } from 'remotion';
import { DIMENSIONS, TIMING, TYPOGRAPHY, COLORS } from './constants';

interface AnimatedBarProps {
  targetHeight: number;
  delay: number;
  color: string;
  label: string;
  labelDelay: number;
}

export const AnimatedBar: React.FC<AnimatedBarProps> = ({
  targetHeight,
  delay,
  color,
  label,
  labelDelay,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const growProgress = spring({
    frame: Math.max(0, frame - delay),
    fps,
    config: {
      damping: 12,
      stiffness: 100,
    },
  });

  const currentHeight = targetHeight * growProgress;

  const labelOpacity = interpolate(
    frame,
    [labelDelay, labelDelay + TIMING.labelFadeDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'flex-end',
        width: DIMENSIONS.barWidth,
        height: DIMENSIONS.maxBarHeight + 40,
      }}
    >
      {/* Value label */}
      <div
        style={{
          opacity: labelOpacity,
          color: COLORS.label,
          fontSize: TYPOGRAPHY.labelSize,
          fontWeight: TYPOGRAPHY.labelWeight,
          fontFamily: TYPOGRAPHY.fontFamily,
          marginBottom: 8,
          height: 32,
          display: 'flex',
          alignItems: 'center',
        }}
      >
        {label}
      </div>

      {/* Bar */}
      <div
        style={{
          width: DIMENSIONS.barWidth,
          height: currentHeight,
          backgroundColor: color,
          borderRadius: DIMENSIONS.barRadius,
          boxShadow: `0 12px 40px ${COLORS.barShadow}`,
        }}
      />
    </div>
  );
};
