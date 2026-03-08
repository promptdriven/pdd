import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, DIMENSIONS } from './constants';

interface ProgressLineProps {
  from: number;
  to: number;
  duration: number;
}

export const ProgressLine: React.FC<ProgressLineProps> = ({ from, to, duration }) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [0, duration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  const currentX = from + (to - from) * progress;

  return (
    <svg
      width={DIMENSIONS.width}
      height={DIMENSIONS.height}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
      }}
    >
      <defs>
        <filter id="progressGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation={15} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Progress line */}
      <line
        x1={from}
        y1={DIMENSIONS.timeline.y}
        x2={currentX}
        y2={DIMENSIONS.timeline.y}
        stroke={COLORS.timelineProgress}
        strokeWidth={DIMENSIONS.timeline.progressHeight}
        strokeLinecap="round"
      />

      {/* Glow effect */}
      <line
        x1={from}
        y1={DIMENSIONS.timeline.y}
        x2={currentX}
        y2={DIMENSIONS.timeline.y}
        stroke={COLORS.timelineGlow}
        strokeWidth={DIMENSIONS.timeline.progressHeight}
        strokeLinecap="round"
        opacity={0.5}
        filter="url(#progressGlow)"
      />
    </svg>
  );
};
