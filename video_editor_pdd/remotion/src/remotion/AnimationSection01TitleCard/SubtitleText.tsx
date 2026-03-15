import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION_TIMING, TEXT, CANVAS, POSITIONS } from './constants';

export const SubtitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const duration = ANIMATION_TIMING.subtitleFadeEnd - ANIMATION_TIMING.subtitleFadeStart;

  const opacity = interpolate(
    frame,
    [0, duration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [0, duration],
    [POSITIONS.subtitleDrift, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: POSITIONS.subtitleY,
        width: CANVAS.width,
        textAlign: 'center',
        fontFamily: TYPOGRAPHY.subtitle.fontFamily,
        fontSize: TYPOGRAPHY.subtitle.fontSize,
        fontWeight: TYPOGRAPHY.subtitle.fontWeight,
        color: COLORS.subtitleSlate,
        lineHeight: 1.5,
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {TEXT.subtitle}
    </div>
  );
};
