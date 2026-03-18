import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  LINE_DRAW_START,
  LINE_DRAW_END,
  LINE_COLOR,
  LINE_OPACITY,
  LINE_WIDTH_PX,
  LINE_Y,
} from './constants';

/**
 * A thin horizontal line that draws outward from the center beneath the question text.
 */
export const AccentLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Line draws from center outward over 15 frames (75–90)
  const lineProgress = interpolate(
    frame,
    [LINE_DRAW_START, LINE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const halfWidth = (LINE_WIDTH_PX / 2) * lineProgress;
  const centerX = 1920 / 2;

  return (
    <div
      style={{
        position: 'absolute',
        top: LINE_Y,
        left: centerX - halfWidth,
        width: halfWidth * 2,
        height: 1,
        backgroundColor: LINE_COLOR,
        opacity: LINE_OPACITY * lineProgress,
      }}
    />
  );
};

export default AccentLine;
