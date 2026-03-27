import React from "react";
import { useCurrentFrame } from "remotion";
import {
  CURSOR_COLOR,
  CURSOR_BLINK_FRAMES,
  LINE_HEIGHT,
  FONT_SIZE,
  GUTTER_WIDTH,
  CODE_LEFT_PADDING,
  EDITOR_TOP_PADDING,
} from "./constants";

interface BlinkingCursorProps {
  line: number;   // 1-indexed
  column: number; // 0-indexed character position
}

export const BlinkingCursor: React.FC<BlinkingCursorProps> = ({
  line,
  column,
}) => {
  const frame = useCurrentFrame();

  // Hard on/off blink: 15 frames on, 15 frames off
  const cycleFrame = frame % (CURSOR_BLINK_FRAMES * 2);
  const isVisible = cycleFrame < CURSOR_BLINK_FRAMES;

  // Approximate character width for monospace at FONT_SIZE (14px)
  const charWidth = FONT_SIZE * 0.6;

  const top = EDITOR_TOP_PADDING + (line - 1) * LINE_HEIGHT;
  const left = GUTTER_WIDTH + CODE_LEFT_PADDING + column * charWidth;

  return (
    <div
      style={{
        position: "absolute",
        top,
        left,
        width: charWidth,
        height: LINE_HEIGHT,
        backgroundColor: CURSOR_COLOR,
        opacity: isVisible ? 0.85 : 0,
        borderRadius: 1,
        pointerEvents: "none",
      }}
    />
  );
};

export default BlinkingCursor;
