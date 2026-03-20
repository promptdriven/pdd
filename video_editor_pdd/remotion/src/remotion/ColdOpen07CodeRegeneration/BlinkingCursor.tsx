import React from 'react';
import { useCurrentFrame } from 'remotion';
import {
  GUTTER_WIDTH,
  CODE_LEFT_PADDING,
  CODE_TOP_PADDING,
  LINE_HEIGHT,
  CODE_FONT_SIZE,
  CURSOR_COLOR,
  CURSOR_BLINK_RATE,
} from './constants';

interface BlinkingCursorProps {
  /** 0-indexed line where the cursor sits */
  line: number;
  /** 0-indexed column */
  column: number;
}

export const BlinkingCursor: React.FC<BlinkingCursorProps> = ({
  line,
  column,
}) => {
  const frame = useCurrentFrame();
  const charWidth = CODE_FONT_SIZE * 0.6;
  const visible = Math.floor(frame / CURSOR_BLINK_RATE) % 2 === 0;

  if (!visible) return null;

  const x = GUTTER_WIDTH + CODE_LEFT_PADDING + column * charWidth;
  const y = CODE_TOP_PADDING + line * LINE_HEIGHT;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y + 2,
        width: 2,
        height: LINE_HEIGHT - 4,
        backgroundColor: CURSOR_COLOR,
      }}
    />
  );
};
