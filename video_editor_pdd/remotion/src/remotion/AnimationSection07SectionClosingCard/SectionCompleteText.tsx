import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION_TIMING, CANVAS } from './constants';

export const SectionCompleteText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.textFadeStart, ANIMATION_TIMING.textFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const translateY = interpolate(
    frame,
    [ANIMATION_TIMING.textFadeStart, ANIMATION_TIMING.textFadeEnd],
    [15, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: DIMENSIONS.textY,
        left: 0,
        width: CANVAS.width,
        display: 'flex',
        justifyContent: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.title.fontFamily,
          fontWeight: TYPOGRAPHY.title.fontWeight,
          fontSize: TYPOGRAPHY.title.fontSize,
          letterSpacing: TYPOGRAPHY.title.letterSpacing,
          color: COLORS.titleText,
          textTransform: 'uppercase',
        }}
      >
        SECTION COMPLETE
      </span>
    </div>
  );
};
