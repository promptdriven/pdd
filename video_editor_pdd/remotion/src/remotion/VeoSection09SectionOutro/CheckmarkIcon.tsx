import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, POSITIONS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const CheckmarkIcon: React.FC = () => {
  const frame = useCurrentFrame();

  const { checkmarkCircleSize, checkmarkStrokeWidth, checkmarkBorderWidth } = DIMENSIONS;
  const radius = checkmarkCircleSize / 2;

  // Circle container fades in (frames 8-14)
  const circleOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.checkmarkFadeStart, ANIMATION_TIMING.checkmarkFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Checkmark stroke draw-on via strokeDashoffset (frames 8-22)
  const checkPathLength = 34;
  const drawProgress = interpolate(
    frame,
    [ANIMATION_TIMING.checkmarkDrawStart, ANIMATION_TIMING.checkmarkDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.poly(3)),
    },
  );
  const checkDashoffset = checkPathLength * (1 - drawProgress);

  // Pulse scale (frames 18-22): 1.0 → 1.15 → 1.0
  const pulseMid = (ANIMATION_TIMING.pulseStart + ANIMATION_TIMING.pulseEnd) / 2;
  const pulseScale = interpolate(
    frame,
    [ANIMATION_TIMING.pulseStart, pulseMid, ANIMATION_TIMING.pulseEnd],
    [1.0, 1.15, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const svgSize = checkmarkCircleSize + 20;
  const center = svgSize / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.width / 2 - svgSize / 2,
        top: POSITIONS.checkmarkCy - svgSize / 2,
        width: svgSize,
        height: svgSize,
        opacity: circleOpacity,
        transform: `scale(${pulseScale})`,
      }}
    >
      <svg
        width={svgSize}
        height={svgSize}
        viewBox={`0 0 ${svgSize} ${svgSize}`}
      >
        {/* Background circle fill */}
        <circle
          cx={center}
          cy={center}
          r={radius}
          fill={COLORS.checkmarkBg}
          stroke={COLORS.checkmarkBorder}
          strokeWidth={checkmarkBorderWidth}
        />

        {/* Checkmark stroke path */}
        <path
          d={`M ${center - 10} ${center + 1} L ${center - 3} ${center + 8} L ${center + 12} ${center - 7}`}
          fill="none"
          stroke={COLORS.checkmark}
          strokeWidth={checkmarkStrokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={checkPathLength}
          strokeDashoffset={checkDashoffset}
        />
      </svg>
    </div>
  );
};
