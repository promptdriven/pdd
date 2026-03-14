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
  gradientId: _gradientId,
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
  const visibleLineEndX = Math.min(fromX + lineLength, fromX + lineLength * drawProgress);

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
      <line
        x1={fromX}
        y1={y}
        x2={visibleLineEndX}
        y2={y}
        stroke={drawProgress >= 0.5 ? gradientTo : gradientFrom}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
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
