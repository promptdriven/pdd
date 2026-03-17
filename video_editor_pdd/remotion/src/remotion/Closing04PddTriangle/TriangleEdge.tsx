import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';

interface TriangleEdgeProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  color: string;
  strokeOpacity: number;
  strokeWidth: number;
  glowBlur: number;
  glowOpacity: number;
  startFrame: number;
  drawDuration: number;
}

const TriangleEdge: React.FC<TriangleEdgeProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  color,
  strokeOpacity,
  strokeWidth,
  glowBlur,
  glowOpacity,
  startFrame,
  drawDuration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [startFrame, startFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.bezier(0.42, 0, 0.58, 1), // easeInOut(cubic)
    },
  );

  if (progress <= 0) return null;

  const dx = toX - fromX;
  const dy = toY - fromY;

  const currentToX = fromX + dx * progress;
  const currentToY = fromY + dy * progress;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id={`edge-glow-${fromX}-${toX}`}>
          <feGaussianBlur stdDeviation={glowBlur} />
        </filter>
      </defs>
      {/* Glow layer */}
      <line
        x1={fromX}
        y1={fromY}
        x2={currentToX}
        y2={currentToY}
        stroke={color}
        strokeWidth={strokeWidth + 4}
        strokeOpacity={glowOpacity}
        filter={`url(#edge-glow-${fromX}-${toX})`}
        strokeLinecap="round"
      />
      {/* Main edge */}
      <line
        x1={fromX}
        y1={fromY}
        x2={currentToX}
        y2={currentToY}
        stroke={color}
        strokeWidth={strokeWidth}
        strokeOpacity={strokeOpacity}
        strokeLinecap="round"
      />
    </svg>
  );
};

export default TriangleEdge;
