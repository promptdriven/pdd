import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TEXT, TIMING } from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  // Frames 16-24: Fade in (opacity 0->1) with easeOutCubic
  const opacity = interpolate(
    frame,
    [TIMING.textStart, TIMING.textEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Frames 16-24: Slide up from +16px -> 0px
  const translateY = interpolate(
    frame,
    [TIMING.textStart, TIMING.textEnd],
    [TEXT.translateY, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: TEXT.y,
        width: '100%',
        textAlign: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: TEXT.fontFamily,
        fontSize: TEXT.fontSize,
        fontWeight: TEXT.fontWeight,
        color: COLORS.text,
        lineHeight: 1.2,
      }}
    >
      {TEXT.content}
    </div>
  );
};
