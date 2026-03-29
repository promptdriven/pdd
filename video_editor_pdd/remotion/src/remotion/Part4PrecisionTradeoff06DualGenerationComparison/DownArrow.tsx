import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface DownArrowProps {
  x: number;
  topY: number;
  length: number;
  color: string;
  arrowOpacity: number;
  drawStart: number;
  drawDuration: number;
}

const DownArrow: React.FC<DownArrowProps> = ({
  x,
  topY,
  length,
  color,
  arrowOpacity,
  drawStart,
  drawDuration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [drawStart, drawStart + drawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const currentLength = length * progress;
  const arrowHeadSize = 6;

  return (
    <svg
      style={{
        position: 'absolute',
        left: x - 10,
        top: topY,
        width: 20,
        height: length + arrowHeadSize,
        overflow: 'visible',
      }}
    >
      {/* Shaft */}
      <line
        x1={10}
        y1={0}
        x2={10}
        y2={currentLength}
        stroke={color}
        strokeWidth={2}
        opacity={arrowOpacity}
      />
      {/* Arrowhead */}
      {progress > 0.5 && (
        <polygon
          points={`${10 - arrowHeadSize},${currentLength - arrowHeadSize} 10,${currentLength} ${10 + arrowHeadSize},${currentLength - arrowHeadSize}`}
          fill={color}
          opacity={arrowOpacity * progress}
        />
      )}
    </svg>
  );
};

export default DownArrow;
