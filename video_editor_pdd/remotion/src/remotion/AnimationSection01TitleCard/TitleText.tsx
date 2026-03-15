import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION_TIMING, TEXT, CANVAS, POSITIONS } from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.titleFadeStart, ANIMATION_TIMING.titleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const scale = interpolate(
    frame,
    [ANIMATION_TIMING.titleFadeStart, ANIMATION_TIMING.titleFadeEnd],
    [ANIMATION_TIMING.titleScaleStart, ANIMATION_TIMING.titleScaleEnd],
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
        left: 0,
        top: 0,
        width: CANVAS.width,
        height: CANVAS.height,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'flex-start',
        paddingTop: POSITIONS.titleY - TYPOGRAPHY.title.fontSize * 0.6,
      }}
    >
      <div
        style={{
          fontFamily: TYPOGRAPHY.title.fontFamily,
          fontSize: TYPOGRAPHY.title.fontSize,
          fontWeight: TYPOGRAPHY.title.fontWeight,
          color: COLORS.titleWhite,
          lineHeight: 1.2,
          opacity,
          transform: `scale(${scale})`,
        }}
      >
        {TEXT.title}
      </div>
    </div>
  );
};
