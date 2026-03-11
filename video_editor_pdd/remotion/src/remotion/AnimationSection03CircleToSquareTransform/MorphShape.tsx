import React from 'react';
import { useCurrentFrame, interpolate, interpolateColors, Easing } from 'remotion';
import { DIMENSIONS, COLORS, ANIMATION_TIMING } from './constants';

const CIRCLE_CLIP = [50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50];
const STAR_CLIP = [50, 0, 61, 35, 98, 35, 68, 57, 79, 91, 50, 70, 21, 91, 32, 57, 2, 35, 39, 35];

export const MorphShape: React.FC = () => {
  const frame = useCurrentFrame();

  // Interpolate each clip-path coordinate from circle to star during morph phase
  const clipPoints = CIRCLE_CLIP.map((circleVal, i) => {
    return interpolate(
      frame,
      [ANIMATION_TIMING.morphStart, ANIMATION_TIMING.morphEnd],
      [circleVal, STAR_CLIP[i]],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.cubic),
      }
    );
  });

  // Build polygon clip-path from interpolated points
  const clipPath = `polygon(${clipPoints[0]}% ${clipPoints[1]}%, ${clipPoints[2]}% ${clipPoints[3]}%, ${clipPoints[4]}% ${clipPoints[5]}%, ${clipPoints[6]}% ${clipPoints[7]}%, ${clipPoints[8]}% ${clipPoints[9]}%, ${clipPoints[10]}% ${clipPoints[11]}%, ${clipPoints[12]}% ${clipPoints[13]}%, ${clipPoints[14]}% ${clipPoints[15]}%, ${clipPoints[16]}% ${clipPoints[17]}%, ${clipPoints[18]}% ${clipPoints[19]}%)`;

  // Color: blue → green during morph phase (linear)
  const fillColor = interpolateColors(
    frame,
    [ANIMATION_TIMING.morphStart, ANIMATION_TIMING.morphEnd],
    [COLORS.circleBlue, COLORS.squareGreen]
  );

  // X position across phases
  const getPositionX = (): number => {
    // Hold + Morph: stay centered
    if (frame < ANIMATION_TIMING.slideStart) {
      return DIMENSIONS.centerX;
    }

    // Slide: center → overshoot position (easeOutCubic carries through settle)
    if (frame < ANIMATION_TIMING.settleStart) {
      return interpolate(
        frame,
        [ANIMATION_TIMING.slideStart, ANIMATION_TIMING.slideEnd],
        [DIMENSIONS.centerX, DIMENSIONS.finalX],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.cubic),
        }
      );
    }

    // Settle: overshoot bounce — slide to 1300, then ease back to 1280
    if (frame < ANIMATION_TIMING.settleEnd) {
      const settleMid = (ANIMATION_TIMING.settleStart + ANIMATION_TIMING.settleEnd) / 2;

      if (frame < settleMid) {
        return interpolate(
          frame,
          [ANIMATION_TIMING.settleStart, settleMid],
          [DIMENSIONS.finalX, DIMENSIONS.overshootX],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );
      }

      return interpolate(
        frame,
        [settleMid, ANIMATION_TIMING.settleEnd],
        [DIMENSIONS.overshootX, DIMENSIONS.finalX],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.cubic),
        }
      );
    }

    // Final hold
    return DIMENSIONS.finalX;
  };

  const posX = getPositionX();

  const shapeSize = DIMENSIONS.shapeWidth;

  return (
    <div
      style={{
        position: 'absolute',
        width: shapeSize,
        height: shapeSize,
        backgroundColor: fillColor,
        clipPath,
        left: posX - shapeSize / 2,
        top: DIMENSIONS.centerY - shapeSize / 2,
      }}
    />
  );
};
