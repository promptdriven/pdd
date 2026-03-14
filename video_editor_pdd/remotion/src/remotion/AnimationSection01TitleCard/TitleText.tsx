import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION_TIMING, TEXT, CANVAS } from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.titleFadeStart, ANIMATION_TIMING.titleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const scale = interpolate(
    frame,
    [ANIMATION_TIMING.titleFadeStart, ANIMATION_TIMING.titleFadeEnd],
    [ANIMATION_TIMING.titleScaleStart, ANIMATION_TIMING.titleScaleEnd],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
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
        alignItems: 'center',
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
          transform: `scale(${scale}) translateY(${DIMENSIONS.titleOffsetY}px)`,
        }}
      >
        {TEXT.title}
      </div>
    </div>
  );
};
