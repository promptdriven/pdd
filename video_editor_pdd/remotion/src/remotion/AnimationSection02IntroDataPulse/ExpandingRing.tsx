import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS } from './constants';

interface ExpandingRingProps {
  targetRadius: number;
  strokeColor: string;
  ringOpacity: number;
  startFrame: number;
  endFrame: number;
}

export const ExpandingRing: React.FC<ExpandingRingProps> = ({
  targetRadius,
  strokeColor,
  ringOpacity,
  startFrame,
  endFrame,
}) => {
  const frame = useCurrentFrame();

  // Expand from 0 to target radius with easeOutQuart
  const radius = interpolate(frame, [startFrame, endFrame], [0, targetRadius], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(4)),
  });

  // Fade in opacity during expansion
  const opacity = interpolate(frame, [startFrame, startFrame + 10], [0, ringOpacity], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  if (frame < startFrame) return null;

  return (
    <svg
      width={CANVAS.width}
      height={CANVAS.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Glow layer */}
      <circle
        cx={CANVAS.centerX}
        cy={CANVAS.centerY}
        r={radius}
        fill="none"
        stroke={strokeColor}
        strokeWidth={6}
        opacity={opacity * 0.3}
        style={{ filter: 'blur(4px)' }}
      />
      {/* Main ring */}
      <circle
        cx={CANVAS.centerX}
        cy={CANVAS.centerY}
        r={radius}
        fill="none"
        stroke={strokeColor}
        strokeWidth={2}
        opacity={opacity}
      />
    </svg>
  );
};
