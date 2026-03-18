import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { TRIANGLE, TIMING } from './constants';

interface DrawEdgeProps {
  from: readonly [number, number];
  to: readonly [number, number];
  startFrame: number;
}

export const DrawEdge: React.FC<DrawEdgeProps> = ({ from, to, startFrame }) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [startFrame, startFrame + TIMING.edgeDrawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.bezier(0.42, 0, 0.58, 1), // easeInOut cubic
    },
  );

  if (drawProgress <= 0) return null;

  // Calculate the endpoint based on draw progress
  const currentToX = from[0] + (to[0] - from[0]) * drawProgress;
  const currentToY = from[1] + (to[1] - from[1]) * drawProgress;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Glow layer */}
      <line
        x1={from[0]}
        y1={from[1]}
        x2={currentToX}
        y2={currentToY}
        stroke={TRIANGLE.edgeColor}
        strokeWidth={TRIANGLE.edgeWidth + 4}
        strokeOpacity={TRIANGLE.glowOpacity}
        style={{ filter: `blur(${TRIANGLE.glowBlur}px)` }}
      />
      {/* Main edge */}
      <line
        x1={from[0]}
        y1={from[1]}
        x2={currentToX}
        y2={currentToY}
        stroke={TRIANGLE.edgeColor}
        strokeWidth={TRIANGLE.edgeWidth}
        strokeOpacity={TRIANGLE.edgeOpacity}
      />
    </svg>
  );
};
