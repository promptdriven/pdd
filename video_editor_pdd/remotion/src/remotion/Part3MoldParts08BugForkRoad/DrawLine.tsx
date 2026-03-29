import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS_WIDTH, CANVAS_HEIGHT } from './constants';

interface DrawLineProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  color: string;
  strokeWidth: number;
  drawStartFrame: number;
  drawDuration: number;
}

export const DrawLine: React.FC<DrawLineProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  color,
  strokeWidth,
  drawStartFrame,
  drawDuration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [drawStartFrame, drawStartFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const dx = toX - fromX;
  const dy = toY - fromY;
  const length = Math.sqrt(dx * dx + dy * dy);

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <line
        x1={fromX}
        y1={fromY}
        x2={fromX + dx * progress}
        y2={fromY + dy * progress}
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
      />
      {/* Glow effect */}
      <line
        x1={fromX}
        y1={fromY}
        x2={fromX + dx * progress}
        y2={fromY + dy * progress}
        stroke={color}
        strokeWidth={strokeWidth + 4}
        strokeLinecap="round"
        opacity={0.15}
        filter="url(#lineGlow)"
      />
      <defs>
        <filter id="lineGlow">
          <feGaussianBlur stdDeviation="4" />
        </filter>
      </defs>
    </svg>
  );
};
