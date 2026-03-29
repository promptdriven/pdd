import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CANVAS_WIDTH,
  LINE_Y,
  LINE_X_START,
  LINE_X_END,
  LINE_COLOR,
  LINE_OPACITY,
  LINE_WIDTH,
  LINE_DRAW_START,
  LINE_DRAW_END,
} from './constants';

/**
 * A horizontal line that draws from center outward.
 * Appears starting at LINE_DRAW_START frame.
 */
export const HorizontalLine: React.FC = () => {
  const frame = useCurrentFrame();

  const lineLength = LINE_X_END - LINE_X_START;
  const centerX = (LINE_X_START + LINE_X_END) / 2;

  // Line draws from center outward over LINE_DRAW_START..LINE_DRAW_END
  const drawProgress = interpolate(
    frame,
    [LINE_DRAW_START, LINE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  const halfDrawn = (lineLength / 2) * drawProgress;
  const currentX1 = centerX - halfDrawn;
  const currentX2 = centerX + halfDrawn;

  if (drawProgress <= 0) return null;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={LINE_Y + 2}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
      }}
    >
      <line
        x1={currentX1}
        y1={LINE_Y}
        x2={currentX2}
        y2={LINE_Y}
        stroke={LINE_COLOR}
        strokeWidth={LINE_WIDTH}
        opacity={LINE_OPACITY}
      />
    </svg>
  );
};

export default HorizontalLine;
