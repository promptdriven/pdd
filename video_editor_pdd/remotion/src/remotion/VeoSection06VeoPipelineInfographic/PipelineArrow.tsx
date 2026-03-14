import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { DIMENSIONS, POSITIONS } from './constants';

interface PipelineArrowProps {
  fromX: number;
  toX: number;
  gradientFrom: string;
  gradientTo: string;
  animStart: number;
  animEnd: number;
  scale?: number;
  gradientId: string;
}

export const PipelineArrow: React.FC<PipelineArrowProps> = ({
  fromX,
  toX,
  gradientFrom,
  gradientTo,
  animStart,
  animEnd,
  scale = 1,
  gradientId,
}) => {
  const frame = useCurrentFrame();
  const y = POSITIONS.arrowY;
  const strokeWidth = DIMENSIONS.arrowStrokeWidth * scale;
  const arrowHeadSize = DIMENSIONS.arrowHeadSize * scale;

  // Draw progress with easeInOutQuad
  const drawProgress = interpolate(frame, [animStart, animEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.quad),
  });

  const totalLength = toX - fromX;
  const lineLength = totalLength - arrowHeadSize;
  const dashOffset = lineLength * (1 - drawProgress);

  // Arrow tip appears at end of draw
  const arrowOpacity = drawProgress >= 0.9 ? 1 : 0;
  const tipX = toX;

  return (
    <svg
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '100%',
        height: '100%',
        pointerEvents: 'none',
      }}
    >
      <defs>
        <linearGradient id={gradientId} x1="0%" y1="0%" x2="100%" y2="0%">
          <stop offset="0%" stopColor={gradientFrom} />
          <stop offset="100%" stopColor={gradientTo} />
        </linearGradient>
      </defs>

      {/* Line with strokeDashoffset animation */}
      <line
        x1={fromX}
        y1={y}
        x2={fromX + lineLength}
        y2={y}
        stroke={`url(#${gradientId})`}
        strokeWidth={strokeWidth}
        strokeDasharray={lineLength}
        strokeDashoffset={dashOffset}
      />

      {/* Arrowhead */}
      <polygon
        points={`
          ${tipX},${y}
          ${tipX - arrowHeadSize},${y - arrowHeadSize / 2}
          ${tipX - arrowHeadSize},${y + arrowHeadSize / 2}
        `}
        fill={gradientTo}
        opacity={arrowOpacity}
      />
    </svg>
  );
};
