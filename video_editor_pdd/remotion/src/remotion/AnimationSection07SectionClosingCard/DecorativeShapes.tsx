import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const DecorativeShapes: React.FC = () => {
  const frame = useCurrentFrame();

  const circleScale = interpolate(
    frame,
    [ANIMATION_TIMING.circlePopStart, ANIMATION_TIMING.circlePopEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  const squareScale = interpolate(
    frame,
    [ANIMATION_TIMING.squarePopStart, ANIMATION_TIMING.squarePopEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  return (
    <>
      {/* Blue circle */}
      <div
        style={{
          position: 'absolute',
          left: DIMENSIONS.circleX - DIMENSIONS.circleRadius,
          top: DIMENSIONS.shapesY - DIMENSIONS.circleRadius,
          width: DIMENSIONS.circleRadius * 2,
          height: DIMENSIONS.circleRadius * 2,
          borderRadius: '50%',
          backgroundColor: COLORS.circleBlue,
          transform: `scale(${circleScale})`,
        }}
      />
      {/* Green square */}
      <div
        style={{
          position: 'absolute',
          left: DIMENSIONS.squareX - DIMENSIONS.squareSize / 2,
          top: DIMENSIONS.shapesY - DIMENSIONS.squareSize / 2,
          width: DIMENSIONS.squareSize,
          height: DIMENSIONS.squareSize,
          backgroundColor: COLORS.squareGreen,
          transform: `scale(${squareScale})`,
        }}
      />
    </>
  );
};
