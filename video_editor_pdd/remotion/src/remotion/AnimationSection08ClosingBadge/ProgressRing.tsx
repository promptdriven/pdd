import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, POSITIONS, ANIMATION_TIMING } from './constants';

const RING_CIRCUMFERENCE = 2 * Math.PI * DIMENSIONS.ringRadius;

export const ProgressRing: React.FC = () => {
  const frame = useCurrentFrame();

  const ringProgress = interpolate(
    frame,
    [ANIMATION_TIMING.ringStart, ANIMATION_TIMING.ringEnd],
    [RING_CIRCUMFERENCE, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  const ringOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.ringStart, ANIMATION_TIMING.ringStart + 3],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const svgSize = DIMENSIONS.ringDiameter + 20;
  const center = svgSize / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.monogramCenterX - svgSize / 2,
        top: POSITIONS.monogramCenterY - svgSize / 2,
        width: svgSize,
        height: svgSize,
        opacity: ringOpacity,
      }}
    >
      <svg width={svgSize} height={svgSize}>
        <defs>
          <linearGradient id="ringGradient" x1="0%" y1="0%" x2="100%" y2="100%">
            <stop offset="0%" stopColor={COLORS.gradientStart} />
            <stop offset="100%" stopColor={COLORS.gradientEnd} />
          </linearGradient>
        </defs>
        <circle
          cx={center}
          cy={center}
          r={DIMENSIONS.ringRadius}
          fill="none"
          stroke="url(#ringGradient)"
          strokeWidth={DIMENSIONS.strokeWidth}
          strokeDasharray={RING_CIRCUMFERENCE}
          strokeDashoffset={ringProgress}
          strokeLinecap="round"
          transform={`rotate(-90, ${center}, ${center})`}
        />
      </svg>
    </div>
  );
};
