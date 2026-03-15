import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, TEXT, TIMING } from './constants';

export const CompleteText: React.FC = () => {
  const frame = useCurrentFrame();

  // Text fades in over frames 18-28 with easeOutQuad
  const opacity = interpolate(
    frame,
    [TIMING.textStart, TIMING.textEnd],
    [0, TEXT.maxOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Slight scale up from 0.95 to 1.0 with easeOutQuad
  const scale = interpolate(
    frame,
    [TIMING.textStart, TIMING.textEnd],
    [TEXT.scaleFrom, TEXT.scaleTo],
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
        top: TEXT.y,
        width: CANVAS.width,
        textAlign: 'center',
        opacity,
        transform: `scale(${scale})`,
        color: COLORS.text,
        fontSize: TEXT.fontSize,
        fontFamily: TEXT.fontFamily,
        fontWeight: TEXT.fontWeight,
      }}
    >
      {TEXT.content}
    </div>
  );
};
