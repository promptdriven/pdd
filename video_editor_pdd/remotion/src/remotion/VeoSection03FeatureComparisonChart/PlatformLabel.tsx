import React from 'react';
import { useCurrentFrame } from 'remotion';
import { interpolate, Easing } from 'remotion';
import { CHART_DIMENSIONS, TYPOGRAPHY, ANIMATION_TIMING } from './constants';

interface PlatformLabelProps {
  y: number;
  text: string;
}

export const PlatformLabel: React.FC<PlatformLabelProps> = ({ y, text }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, ANIMATION_TIMING.LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.bezier(0.42, 0, 0.58, 1), // easeInOutQuad
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: CHART_DIMENSIONS.LABEL_X,
        top: y,
        fontFamily: TYPOGRAPHY.PLATFORM_LABEL.FONT_FAMILY,
        fontWeight: TYPOGRAPHY.PLATFORM_LABEL.FONT_WEIGHT,
        fontSize: TYPOGRAPHY.PLATFORM_LABEL.FONT_SIZE,
        color: TYPOGRAPHY.PLATFORM_LABEL.COLOR,
        opacity,
      }}
    >
      {text}
    </div>
  );
};
