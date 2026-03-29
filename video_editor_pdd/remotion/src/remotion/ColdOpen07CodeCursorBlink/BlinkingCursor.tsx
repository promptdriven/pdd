import React from "react";
import { useCurrentFrame } from "remotion";
import {
  CODE_FONT,
  CODE_FONT_SIZE,
  CODE_LEFT_PADDING,
  CURSOR_BLINK_FRAMES,
  CURSOR_COLOR,
  GUTTER_WIDTH,
  LINE_HEIGHT,
  TOP_PADDING,
} from "./constants";

interface BlinkingCursorProps {
  line: number; // 1-based
  column: number;
  startFrame?: number; // frame when cursor starts blinking (after fade-in)
}

export const BlinkingCursor: React.FC<BlinkingCursorProps> = ({
  line,
  column,
  startFrame = 0,
}) => {
  const frame = useCurrentFrame();

  // Step function blink: 15 frames on, 15 frames off (500ms each at 30fps)
  const blinkFrame = frame - startFrame;
  const isVisible = blinkFrame < 0 ? true : Math.floor(blinkFrame / CURSOR_BLINK_FRAMES) % 2 === 0;

  // Approximate character width for monospace font at 14px
  const charWidth = CODE_FONT_SIZE * 0.6;

  // Position the cursor
  const top = TOP_PADDING + (line - 1) * LINE_HEIGHT;
  // 3px for border-left + gutter + padding + column offset
  const left = 3 + GUTTER_WIDTH + CODE_LEFT_PADDING + (column - 1) * charWidth;

  return (
    <div
      style={{
        position: "absolute",
        top,
        left,
        width: charWidth,
        height: LINE_HEIGHT - 4,
        marginTop: 2,
        backgroundColor: CURSOR_COLOR,
        opacity: isVisible ? 0.85 : 0,
        borderRadius: 1,
      }}
    />
  );
};

export default BlinkingCursor;
