import React from 'react';
import { useCurrentFrame, spring, interpolate, Easing } from 'remotion';
import { CHART, TYPOGRAPHY, COLORS, ANIMATION_TIMING, SPRING_CONFIG } from './constants';

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

  // Bar growth using Remotion spring
  const growProgress = spring({
    frame: frame - delay,
    fps: 30,
    config: {
      damping: SPRING_CONFIG.damping,
      stiffness: SPRING_CONFIG.stiffness,
      mass: SPRING_CONFIG.mass,
    },
  });

  const barHeight = growProgress * targetHeight;

  // Label fade-in
  const labelOpacity = interpolate(
    frame,
    [labelDelay, labelDelay + ANIMATION_TIMING.labelFadeDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        justifyContent: 'flex-end',
        width: CHART.barWidth,
        height: CHART.maxBarHeight + 40,
      }}
    >
      {/* Percentage label */}
      <div
        style={{
          opacity: labelOpacity,
          fontSize: TYPOGRAPHY.label.fontSize,
          fontFamily: TYPOGRAPHY.label.fontFamily,
          fontWeight: TYPOGRAPHY.label.fontWeight,
          color: COLORS.labelText,
          marginBottom: 8,
          whiteSpace: 'nowrap',
        }}
      >
        {label}
      </div>

      {/* Bar */}
      <div
        style={{
          width: CHART.barWidth,
          height: barHeight,
          backgroundColor: color,
          borderRadius: CHART.borderRadius,
          boxShadow: '0 12px 40px rgba(15, 23, 42, 0.45)',
        }}
      />
    </div>
  );
};
