import React from 'react';
import { useCurrentFrame, interpolate, interpolateColors, Easing } from 'remotion';
import { DIMENSIONS, COLORS, ANIMATION_TIMING } from './constants';

export const MorphShape: React.FC = () => {
  const frame = useCurrentFrame();

  // Border-radius: 50% (circle) → 0% (square) during morph phase
  const borderRadiusPercent = interpolate(
    frame,
    [ANIMATION_TIMING.morphStart, ANIMATION_TIMING.morphEnd],
    [50, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Color: blue → yellow during morph phase (linear)
  const fillColor = interpolateColors(
    frame,
    [ANIMATION_TIMING.morphStart, ANIMATION_TIMING.morphEnd],
    [COLORS.circleBlue, COLORS.squareYellow]
  );

  // X position across phases
  const getPositionX = (): number => {
    // Hold + Morph: stay centered
    if (frame < ANIMATION_TIMING.slideStart) {
      return DIMENSIONS.centerX;
    }

    // Slide: center → overshoot position (easeOutCubic carries through settle)
    // We animate all the way to overshoot across slide+settle, then correct at end
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
        // First half: ease out to overshoot
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

      // Second half: ease back to final
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

  return (
    <div
      style={{
        position: 'absolute',
        width: DIMENSIONS.shapeSize,
        height: DIMENSIONS.shapeSize,
        backgroundColor: fillColor,
        borderRadius: `${borderRadiusPercent}%`,
        left: posX - DIMENSIONS.shapeSize / 2,
        top: DIMENSIONS.centerY - DIMENSIONS.shapeSize / 2,
      }}
    />
  );
};
