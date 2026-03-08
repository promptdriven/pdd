import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { ARROW_STYLE, COLORS } from './constants';

interface AnimatedArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  drawStart: number;
  drawEnd: number;
}

export const AnimatedArrow: React.FC<AnimatedArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  drawStart,
  drawEnd,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [drawStart, drawEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.quad),
  });

  const lineLength = toX - fromX;
  const currentEndX = fromX + lineLength * progress;
  const { arrowheadSize } = ARROW_STYLE;

  // Only show arrowhead when arrow is nearly complete
  const showArrowhead = progress > 0.9;
  const arrowheadOpacity = interpolate(progress, [0.9, 1], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Main line */}
      <line
        x1={fromX}
        y1={fromY}
        x2={currentEndX}
        y2={toY}
        stroke={COLORS.arrowStroke}
        strokeWidth={ARROW_STYLE.strokeWidth}
        strokeLinecap="round"
      />

      {/* Arrowhead */}
      {showArrowhead && (
        <polygon
          points={`${toX},${toY} ${toX - arrowheadSize},${toY - arrowheadSize / 2} ${toX - arrowheadSize},${toY + arrowheadSize / 2}`}
          fill={COLORS.arrowStroke}
          opacity={arrowheadOpacity}
        />
      )}
    </svg>
  );
};
