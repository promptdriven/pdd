import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, PULSE, TIMING } from './constants';

export const PulseRing: React.FC = () => {
  const frame = useCurrentFrame();

  // Only visible during pulse phase (frames 40-60)
  if (frame < TIMING.pulseStart || frame > TIMING.pulseEnd) return null;

  // Ring expands from 100px radius to 150px radius with easeOutQuad
  const ringRadius = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulseEnd],
    [PULSE.ringStartRadius, PULSE.ringEndRadius],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Opacity fades from 30% to 0%
  const opacity = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulseEnd],
    [PULSE.ringStartOpacity, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const size = ringRadius * 2;
  const cx = size / 2;
  const cy = size / 2;

  // Equilateral triangle points centered in the SVG
  const topX = cx;
  const topY = cy - ringRadius;
  const bottomLeftX = cx - ringRadius;
  const bottomLeftY = cy + ringRadius;
  const bottomRightX = cx + ringRadius;
  const bottomRightY = cy + ringRadius;

  return (
    <svg
      style={{
        position: 'absolute',
        left: CANVAS.centerX - ringRadius,
        top: CANVAS.centerY - ringRadius,
        width: size,
        height: size,
        pointerEvents: 'none',
        overflow: 'visible',
      }}
    >
      <polygon
        points={`${topX},${topY} ${bottomLeftX},${bottomLeftY} ${bottomRightX},${bottomRightY}`}
        fill="none"
        stroke={COLORS.pulseRingColor}
        strokeWidth={2}
        opacity={opacity}
      />
    </svg>
  );
};
