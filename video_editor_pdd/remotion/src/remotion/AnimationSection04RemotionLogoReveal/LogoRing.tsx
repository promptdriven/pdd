import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, LOGO, TIMING } from './constants';

export const LogoRing: React.FC = () => {
  const frame = useCurrentFrame();

  const circumference = 2 * Math.PI * LOGO.ringRadius;

  const drawProgress = interpolate(
    frame,
    [TIMING.ringStart, TIMING.ringEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) },
  );

  const dashOffset = circumference * (1 - drawProgress);

  const ringOpacity = interpolate(
    frame,
    [TIMING.ringStart, TIMING.ringStart + 5],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  return (
    <svg
      width={CANVAS.width}
      height={CANVAS.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <circle
        cx={LOGO.cx}
        cy={LOGO.cy}
        r={LOGO.ringRadius}
        fill="none"
        stroke={COLORS.logoBlue}
        strokeWidth={LOGO.ringStroke}
        strokeDasharray={circumference}
        strokeDashoffset={dashOffset}
        strokeLinecap="round"
        opacity={ringOpacity}
        transform={`rotate(-90, ${LOGO.cx}, ${LOGO.cy})`}
      />
    </svg>
  );
};
