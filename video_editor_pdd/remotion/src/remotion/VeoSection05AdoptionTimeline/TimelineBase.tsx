import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, DIMENSIONS } from './constants';

interface TimelineBaseProps {
  x1: number;
  x2: number;
  y: number;
}

export const TimelineBase: React.FC<TimelineBaseProps> = ({ x1, x2, y }) => {
  const frame = useCurrentFrame();

  // Fade in over first 30 frames
  const opacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  return (
    <svg
      width={DIMENSIONS.width}
      height={DIMENSIONS.height}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        opacity,
      }}
    >
      <defs>
        <filter id="timelineGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation={DIMENSIONS.timeline.glowBlur} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Base timeline line */}
      <line
        x1={x1}
        y1={y}
        x2={x2}
        y2={y}
        stroke={COLORS.timelineBase}
        strokeWidth={DIMENSIONS.timeline.baseHeight}
      />

      {/* Glow effect */}
      <line
        x1={x1}
        y1={y}
        x2={x2}
        y2={y}
        stroke={COLORS.timelineProgress}
        strokeWidth={DIMENSIONS.timeline.baseHeight}
        opacity={0.3}
        filter="url(#timelineGlow)"
      />
    </svg>
  );
};
