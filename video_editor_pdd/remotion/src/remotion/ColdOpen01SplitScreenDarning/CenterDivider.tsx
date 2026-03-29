import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  DIVIDER_LINE_WIDTH,
  DIVIDER_MAX_OPACITY,
  DIVIDER_COLOR,
  FADE_IN_END,
} from './constants';

/**
 * Vertical center divider that fades in over the first FADE_IN_END frames.
 * Renders as a thin white line centered in the 40px divider gap.
 */
const CenterDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, FADE_IN_END], [0, DIVIDER_MAX_OPACITY], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const centerX = (CANVAS_WIDTH - DIVIDER_LINE_WIDTH) / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: centerX,
        top: 0,
        width: DIVIDER_LINE_WIDTH,
        height: CANVAS_HEIGHT,
        backgroundColor: DIVIDER_COLOR,
        opacity,
      }}
    />
  );
};

export default CenterDivider;
