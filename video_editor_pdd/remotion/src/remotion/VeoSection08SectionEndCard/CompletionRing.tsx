import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, type EndCardLayout } from './constants';

export const CompletionRing: React.FC<{ layout: EndCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  const { ringRadius, ringStroke, ringCenterX, ringCenterY } = layout.dimensions;
  const circumference = 2 * Math.PI * ringRadius;

  // Ring draws clockwise from 0° → 360° (frames 10-40)
  const ringProgress = interpolate(
    frame,
    [ANIMATION.ringDrawStart, ANIMATION.ringDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const strokeDashoffset = circumference * (1 - ringProgress);

  // SVG viewBox sized to fit the ring with padding
  const padding = ringStroke * 2;
  const svgSize = (ringRadius + padding) * 2;
  const center = svgSize / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: ringCenterX - svgSize / 2,
        top: ringCenterY - svgSize / 2,
        width: svgSize,
        height: svgSize,
      }}
    >
      <svg
        width={svgSize}
        height={svgSize}
        viewBox={`0 0 ${svgSize} ${svgSize}`}
      >
        <circle
          cx={center}
          cy={center}
          r={ringRadius}
          fill="none"
          stroke={COLORS.ring}
          strokeWidth={ringStroke}
          strokeDasharray={circumference}
          strokeDashoffset={strokeDashoffset}
          strokeLinecap="round"
          transform={`rotate(-90 ${center} ${center})`}
        />
      </svg>
    </div>
  );
};
