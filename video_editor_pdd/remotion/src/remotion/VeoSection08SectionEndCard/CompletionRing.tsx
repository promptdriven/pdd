import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, POSITIONS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const CompletionRing: React.FC = () => {
  const frame = useCurrentFrame();

  const { ringRadius, ringStrokeWidth, checkSize } = DIMENSIONS;
  const circumference = 2 * Math.PI * ringRadius;

  // Ring draws from 0 to full circle
  const ringProgress = interpolate(
    frame,
    [ANIMATION_TIMING.ringDrawStart, ANIMATION_TIMING.ringDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  const strokeDashoffset = circumference * (1 - ringProgress);

  // Checkmark draws in
  const checkProgress = interpolate(
    frame,
    [ANIMATION_TIMING.checkmarkStart, ANIMATION_TIMING.checkmarkEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Checkmark path: a simple check shape
  const checkPathLength = 40;
  const checkDashoffset = checkPathLength * (1 - checkProgress);

  // Glow pulse after ring completes
  const glowOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.ringDrawEnd, ANIMATION_TIMING.ringDrawEnd + 10],
    [0, 0.4],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  const svgSize = (ringRadius + ringStrokeWidth) * 2 + 20;
  const center = svgSize / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.width / 2 - svgSize / 2,
        top: POSITIONS.ringCy - svgSize / 2,
        width: svgSize,
        height: svgSize,
      }}
    >
      <svg
        width={svgSize}
        height={svgSize}
        viewBox={`0 0 ${svgSize} ${svgSize}`}
      >
        {/* Glow behind ring */}
        <circle
          cx={center}
          cy={center}
          r={ringRadius + 8}
          fill="none"
          stroke={COLORS.accentWarm}
          strokeWidth={6}
          opacity={glowOpacity}
          style={{ filter: 'blur(8px)' }}
        />

        {/* Ring stroke */}
        <circle
          cx={center}
          cy={center}
          r={ringRadius}
          fill="none"
          stroke={COLORS.ringStroke}
          strokeWidth={ringStrokeWidth}
          strokeDasharray={circumference}
          strokeDashoffset={strokeDashoffset}
          strokeLinecap="round"
          transform={`rotate(-90 ${center} ${center})`}
        />

        {/* Checkmark */}
        <path
          d={`M ${center - checkSize * 0.35} ${center + checkSize * 0.05} L ${center - checkSize * 0.05} ${center + checkSize * 0.35} L ${center + checkSize * 0.4} ${center - checkSize * 0.25}`}
          fill="none"
          stroke={COLORS.accentGold}
          strokeWidth={3}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={checkPathLength}
          strokeDashoffset={checkDashoffset}
        />
      </svg>
    </div>
  );
};
