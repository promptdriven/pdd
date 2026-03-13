import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, TYPOGRAPHY, ANIMATION_TIMING } from './constants';

export const CompleteText: React.FC = () => {
  const frame = useCurrentFrame();

  // Text fades in over frames 6-12 with easeOutQuad
  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.textFadeStart, ANIMATION_TIMING.textFadeEnd],
    [0, 1],
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
        top: DIMENSIONS.textCenterY,
        width: CANVAS.width,
        textAlign: 'center',
        opacity,
        color: COLORS.text,
        fontSize: TYPOGRAPHY.text.fontSize,
        fontFamily: TYPOGRAPHY.text.fontFamily,
        fontWeight: TYPOGRAPHY.text.fontWeight,
      }}
    >
      Section Complete
    </div>
  );
};
