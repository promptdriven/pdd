import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import {
  SCAN_LINE_COLOR,
  CANVAS_HEIGHT,
  SCAN_LINE_START_FRAME,
  SCAN_LINE_DURATION,
} from './constants';

/**
 * A subtle 1px horizontal scan line that scrolls vertically
 * across the screen to reinforce the "screen" feeling.
 * Active from frame 60 to 150.
 */
export const ScanLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Only render during scan line window
  if (frame < SCAN_LINE_START_FRAME) {
    return null;
  }

  const localFrame = frame - SCAN_LINE_START_FRAME;

  // Linear scroll from top to bottom
  const y = interpolate(localFrame, [0, SCAN_LINE_DURATION], [0, CANVAS_HEIGHT], {
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: y,
        width: '100%',
        height: 1,
        backgroundColor: SCAN_LINE_COLOR,
        opacity: 0.02,
        pointerEvents: 'none',
      }}
    />
  );
};
