import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface PipelineArrowProps {
  width: number;
  height: number;
  fromX: number;
  toX: number;
  y: number;
  color: string;
  drawStart: number;
  drawEnd: number;
}

const ARROW_HEAD_SIZE = 10;
const STROKE_WIDTH = 2;

export const PipelineArrow: React.FC<PipelineArrowProps> = ({
  width,
  height,
  fromX,
  toX,
  y,
  color,
  drawStart,
  drawEnd,
}) => {
  const frame = useCurrentFrame();

  // Progress of the arrow drawing (0 to 1)
  const progress = interpolate(
    frame,
    [drawStart, drawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  if (progress <= 0) return null;

  const totalLength = toX - fromX;
  const currentEndX = fromX + totalLength * progress;

  // Only show arrowhead when arrow is mostly drawn
  const showArrowhead = progress > 0.8;
  const arrowheadOpacity = interpolate(
    progress,
    [0.8, 1],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <svg
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width,
        height,
        pointerEvents: 'none',
      }}
    >
      {/* Arrow line */}
      <line
        x1={fromX}
        y1={y}
        x2={currentEndX}
        y2={y}
        stroke={color}
        strokeWidth={STROKE_WIDTH}
      />
      {/* Arrowhead */}
      {showArrowhead && (
        <polygon
          points={`
            ${toX},${y}
            ${toX - ARROW_HEAD_SIZE},${y - ARROW_HEAD_SIZE / 2}
            ${toX - ARROW_HEAD_SIZE},${y + ARROW_HEAD_SIZE / 2}
          `}
          fill={color}
          opacity={arrowheadOpacity}
        />
      )}
    </svg>
  );
};
