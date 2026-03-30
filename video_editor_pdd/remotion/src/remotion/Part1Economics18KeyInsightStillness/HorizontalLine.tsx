import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  LINE_COLOR,
  LINE_OPACITY,
  LINE_Y,
  LINE_X_START,
  LINE_X_END,
  LINE_CENTER_X,
  LINE_WIDTH_PX,
  LINE_DRAW_START,
  LINE_DRAW_DURATION,
} from './constants';

/**
 * A thin horizontal line that draws outward from center.
 * Appears at LINE_DRAW_START and persists for the rest of the composition.
 */
export const HorizontalLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Progress of the draw animation (0 → 1)
  const drawProgress = interpolate(
    frame,
    [LINE_DRAW_START, LINE_DRAW_START + LINE_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  // Half-width grows from 0 to full extent
  const halfSpan = ((LINE_X_END - LINE_X_START) / 2) * drawProgress;
  const currentLeft = LINE_CENTER_X - halfSpan;
  const currentWidth = halfSpan * 2;

  if (drawProgress <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: LINE_Y,
        left: currentLeft,
        width: currentWidth,
        height: LINE_WIDTH_PX,
        backgroundColor: LINE_COLOR,
        opacity: LINE_OPACITY,
      }}
    />
  );
};

export default HorizontalLine;
