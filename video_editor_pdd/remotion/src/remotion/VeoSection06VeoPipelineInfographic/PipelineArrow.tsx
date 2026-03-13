import React from 'react';
import { DIMENSIONS, POSITIONS } from './constants';

interface PipelineArrowProps {
  fromX: number;
  toX: number;
  color: string;
}

const ARROW_HEAD_SIZE = 10;

export const PipelineArrow: React.FC<PipelineArrowProps> = ({
  fromX,
  toX,
  color,
}) => {
  const y = POSITIONS.arrowY;

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
        x2={toX - ARROW_HEAD_SIZE}
        y2={y}
        stroke={color}
        strokeWidth={DIMENSIONS.arrowStrokeWidth}
        strokeDasharray={DIMENSIONS.arrowDashArray}
      />
      {/* Arrowhead */}
      <polygon
        points={`
          ${toX},${y}
          ${toX - ARROW_HEAD_SIZE},${y - ARROW_HEAD_SIZE / 2}
          ${toX - ARROW_HEAD_SIZE},${y + ARROW_HEAD_SIZE / 2}
        `}
        fill={color}
      />
    </svg>
  );
};
