import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS } from './constants';

interface PipelineArrowProps {
  fromX: number;
  toX: number;
  y: number;
  animStart: number;
  animEnd: number;
  pulseStart: number;
  pulseEnd: number;
  scale?: number;
}

export const PipelineArrow: React.FC<PipelineArrowProps> = ({
  fromX,
  toX,
  y,
  animStart,
  animEnd,
  pulseStart,
  pulseEnd,
  scale = 1,
}) => {
  const frame = useCurrentFrame();
  const strokeWidth = DIMENSIONS.arrowStrokeWidth * scale;
  const arrowHeadSize = DIMENSIONS.arrowHeadSize * scale;
  const pulseRadius = DIMENSIONS.pulseRadius * scale;

  // Draw progress with easeInOutCubic
  const drawProgress = interpolate(frame, [animStart, animEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  const totalLength = toX - fromX;
  const lineLength = totalLength - arrowHeadSize;
  const visibleLineEndX = fromX + lineLength * drawProgress;

  // Arrow tip appears at end of draw
  const arrowOpacity = drawProgress >= 0.9 ? 1 : 0;
  const tipX = toX;

  // Progress pulse: travels linearly along the arrow path
  const pulseProgress = interpolate(frame, [pulseStart, pulseEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const pulseX = fromX + totalLength * pulseProgress;
  const pulseVisible = frame >= pulseStart && frame <= pulseEnd;

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
      {/* Arrow line */}
      <line
        x1={fromX}
        y1={y}
        x2={visibleLineEndX}
        y2={y}
        stroke={COLORS.arrowStroke}
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
        fill={COLORS.arrowStroke}
        opacity={arrowOpacity}
      />

      {/* Progress pulse dot */}
      {pulseVisible && (
        <>
          {/* Glow effect */}
          <circle
            cx={pulseX}
            cy={y}
            r={pulseRadius * 2}
            fill={COLORS.pulseGlow}
            opacity={0.3}
          />
          {/* Core dot */}
          <circle
            cx={pulseX}
            cy={y}
            r={pulseRadius}
            fill={COLORS.pulseGlow}
          />
        </>
      )}
    </svg>
  );
};
