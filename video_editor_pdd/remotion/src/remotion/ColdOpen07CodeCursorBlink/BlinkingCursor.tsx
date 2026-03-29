import React from 'react';
import { useCurrentFrame } from 'remotion';

// ============================================================
// BlinkingCursor — a block cursor that blinks on/off every 15 frames
// Positioned at line 23, column 4 of the code editor
// ============================================================

const GUTTER_WIDTH = 60;
const CODE_PADDING_LEFT = 16;
const CODE_PADDING_TOP = 40;
const LINE_HEIGHT = 22;
const CURSOR_COLOR = '#CDD6F4';
const CURSOR_BLINK_FRAMES = 15;
const CURSOR_LINE = 23;
const CURSOR_COLUMN = 4;
const CURSOR_WIDTH = 8.4;  // approx char width at 14px monospace
const CURSOR_HEIGHT = 18;

export const BlinkingCursor: React.FC = () => {
  const frame = useCurrentFrame();

  // Step function: on for 15 frames, off for 15 frames
  const blinkCycle = Math.floor(frame / CURSOR_BLINK_FRAMES);
  const isVisible = blinkCycle % 2 === 0;

  // Position: line 23 (0-indexed = 22), column 4
  const top = CODE_PADDING_TOP + (CURSOR_LINE - 1) * LINE_HEIGHT + (LINE_HEIGHT - CURSOR_HEIGHT) / 2;
  const left = GUTTER_WIDTH + CODE_PADDING_LEFT + (CURSOR_COLUMN - 1) * CURSOR_WIDTH;

  return (
    <div
      style={{
        position: 'absolute',
        top,
        left,
        width: CURSOR_WIDTH,
        height: CURSOR_HEIGHT,
        backgroundColor: CURSOR_COLOR,
        opacity: isVisible ? 0.85 : 0,
        borderRadius: 1,
      }}
    />
  );
};

export default BlinkingCursor;
