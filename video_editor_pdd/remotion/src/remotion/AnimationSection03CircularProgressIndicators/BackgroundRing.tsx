/**
 * BackgroundRing component - renders the static background ring for progress indicators
 */

import React from 'react';
import { interpolate, spring, useCurrentFrame, useVideoConfig } from 'remotion';

interface BackgroundRingProps {
  center: [number, number];
  radius: number;
  thickness: number;
  color: string;
}

export const BackgroundRing: React.FC<BackgroundRingProps> = ({
  center,
  radius,
  thickness,
  color,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const opacity = spring({
    frame,
    fps,
    config: {
      damping: 200,
    },
  });

  const [cx, cy] = center;
  const innerRadius = radius - thickness;

  return (
    <svg
      width={radius * 2 + 20}
      height={radius * 2 + 20}
      style={{
        position: 'absolute',
        left: cx - radius - 10,
        top: cy - radius - 10,
        opacity,
      }}
    >
      <circle
        cx={radius + 10}
        cy={radius + 10}
        r={radius - thickness / 2}
        fill="none"
        stroke={color}
        strokeWidth={thickness}
      />
    </svg>
  );
};
