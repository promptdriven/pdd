import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const DottedArrow: React.FC = () => {
  const frame = useCurrentFrame();

  const lineLength = DIMENSIONS.arrowEndX - DIMENSIONS.arrowStartX;
  const arrowHeadSize = 12;

  const drawProgress = interpolate(
    frame,
    [ANIMATION_TIMING.arrowDrawStart, ANIMATION_TIMING.arrowDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  const dashArray = '8 6';
  const totalDashLength = lineLength;
  // Animate by shifting the dash offset from full length to 0
  const dashOffset = totalDashLength * (1 - drawProgress);

  const arrowOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.arrowDrawEnd - 5, ANIMATION_TIMING.arrowDrawEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  if (frame < ANIMATION_TIMING.arrowDrawStart) {
    return null;
  }

  return (
    <svg
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: DIMENSIONS.arrowEndX + arrowHeadSize + 4,
        height: DIMENSIONS.arrowY + 30,
      }}
    >
      {/* Dotted line */}
      <line
        x1={DIMENSIONS.arrowStartX}
        y1={DIMENSIONS.arrowY}
        x2={DIMENSIONS.arrowEndX}
        y2={DIMENSIONS.arrowY}
        stroke={COLORS.arrowStroke}
        strokeWidth={2}
        strokeDasharray={dashArray}
        strokeDashoffset={dashOffset}
      />
      {/* Arrowhead */}
      <polygon
        points={`
          ${DIMENSIONS.arrowEndX},${DIMENSIONS.arrowY}
          ${DIMENSIONS.arrowEndX - arrowHeadSize},${DIMENSIONS.arrowY - arrowHeadSize / 2}
          ${DIMENSIONS.arrowEndX - arrowHeadSize},${DIMENSIONS.arrowY + arrowHeadSize / 2}
        `}
        fill={COLORS.arrowStroke}
        opacity={arrowOpacity}
      />
    </svg>
  );
};
