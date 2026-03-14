import React from 'react';
import { DIMENSIONS, POSITIONS } from './constants';

interface PipelineArrowProps {
  fromX: number;
  toX: number;
  color: string;
  scale?: number;
  progress?: number;
}

const ARROW_HEAD_SIZE = 10;

export const PipelineArrow: React.FC<PipelineArrowProps> = ({
  fromX,
  toX,
  color,
  scale = 1,
  progress = 1,
}) => {
  const y = POSITIONS.arrowY;
  const arrowHeadSize = ARROW_HEAD_SIZE * scale;
  const visibleLineEndX = Math.min(
    toX - arrowHeadSize,
    fromX + (toX - fromX - arrowHeadSize) * progress,
  );

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
      {/* Dashed line */}
      <line
        x1={fromX}
        y1={y}
        x2={visibleLineEndX}
        y2={y}
        stroke={color}
        strokeWidth={DIMENSIONS.arrowStrokeWidth * scale}
        strokeDasharray={DIMENSIONS.arrowDashArray}
      />
      {/* Arrowhead */}
      <polygon
        points={`
          ${toX},${y}
          ${toX - arrowHeadSize},${y - arrowHeadSize / 2}
          ${toX - arrowHeadSize},${y + arrowHeadSize / 2}
        `}
        fill={color}
      />
    </svg>
  );
};
