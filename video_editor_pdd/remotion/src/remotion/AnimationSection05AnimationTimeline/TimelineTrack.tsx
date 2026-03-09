import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { TRACK, COLORS, ANIMATION_TIMING } from './constants';

export const TimelineTrack: React.FC = () => {
  const frame = useCurrentFrame();

  const trackLength = TRACK.endX - TRACK.startX;

  // Track draws in from left to right (frame 0-20)
  const drawProgress = interpolate(
    frame,
    [ANIMATION_TIMING.trackDrawStart, ANIMATION_TIMING.trackDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  // Shimmer effect (frame 120-150): opacity oscillation
  const shimmerOpacity =
    frame >= ANIMATION_TIMING.fadeoutStart
      ? interpolate(
          Math.sin(((frame - ANIMATION_TIMING.fadeoutStart) / 30) * Math.PI * 4),
          [-1, 1],
          [0.8, 1]
        )
      : 1;

  const visibleWidth = trackLength * drawProgress;

  return (
    <svg
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
      }}
    >
      <line
        x1={TRACK.startX}
        y1={TRACK.y}
        x2={TRACK.startX + visibleWidth}
        y2={TRACK.y}
        stroke={COLORS.trackStroke}
        strokeWidth={TRACK.strokeWidth}
        opacity={shimmerOpacity}
      />
    </svg>
  );
};
