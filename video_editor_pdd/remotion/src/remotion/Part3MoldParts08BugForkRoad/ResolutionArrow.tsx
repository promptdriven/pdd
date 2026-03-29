import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS_WIDTH, CANVAS_HEIGHT, ARROW_OPACITY } from './constants';

interface ResolutionArrowProps {
  x: number;
  fromY: number;
  toY: number;
  color: string;
  fadeStartFrame: number;
}

export const ResolutionArrow: React.FC<ResolutionArrowProps> = ({
  x,
  fromY,
  toY,
  color,
  fadeStartFrame,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeStartFrame, fadeStartFrame + 20],
    [0, ARROW_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const drawProgress = interpolate(
    frame,
    [fadeStartFrame, fadeStartFrame + 25],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const currentToY = fromY + (toY - fromY) * drawProgress;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <marker
          id={`resArrow-${color.replace('#', '')}`}
          markerWidth="8"
          markerHeight="6"
          refX="7"
          refY="3"
          orient="auto"
        >
          <path d="M 0 0 L 8 3 L 0 6 Z" fill={color} opacity={opacity} />
        </marker>
      </defs>
      <line
        x1={x}
        y1={fromY}
        x2={x}
        y2={currentToY}
        stroke={color}
        strokeWidth={2}
        opacity={opacity}
        strokeDasharray="6 4"
        markerEnd={drawProgress > 0.8 ? `url(#resArrow-${color.replace('#', '')})` : undefined}
      />
    </svg>
  );
};
