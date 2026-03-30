import React from 'react';
import {interpolate, useCurrentFrame, Easing} from 'remotion';

export interface ContrastLineProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  color: string;
  lineOpacity: number;
  drawDuration: number;
}

const ContrastLine: React.FC<ContrastLineProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  color,
  lineOpacity,
  drawDuration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [0, drawDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.quad),
  });

  const currentToX = fromX + (toX - fromX) * progress;
  const currentToY = fromY + (toY - fromY) * progress;

  if (progress <= 0) return null;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{position: 'absolute', top: 0, left: 0, pointerEvents: 'none'}}
    >
      <line
        x1={fromX}
        y1={fromY}
        x2={currentToX}
        y2={currentToY}
        stroke={color}
        strokeWidth={1}
        strokeDasharray="4 4"
        opacity={lineOpacity}
      />
    </svg>
  );
};

export default ContrastLine;
