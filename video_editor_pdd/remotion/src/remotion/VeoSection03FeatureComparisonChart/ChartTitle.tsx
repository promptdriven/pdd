import React from 'react';
import { useCurrentFrame } from 'remotion';
import { interpolate, Easing } from 'remotion';
import { CANVAS, TYPOGRAPHY } from './constants';

interface ChartTitleProps {
  text: string;
}

export const ChartTitle: React.FC<ChartTitleProps> = ({ text }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.bezier(0.42, 0, 0.58, 1), // easeInOutQuad
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 100,
        width: CANVAS.WIDTH,
        textAlign: 'center',
        fontFamily: TYPOGRAPHY.TITLE.FONT_FAMILY,
        fontWeight: TYPOGRAPHY.TITLE.FONT_WEIGHT,
        fontSize: TYPOGRAPHY.TITLE.FONT_SIZE,
        color: TYPOGRAPHY.TITLE.COLOR,
        opacity,
      }}
    >
      {text}
    </div>
  );
};
