import React from "react";
import { useCurrentFrame } from "remotion";
import {
  CURSOR_COLOR,
  CURSOR_WIDTH,
  CURSOR_HEIGHT,
  CURSOR_BLINK_MS,
  FPS,
  CODE_LINE_HEIGHT,
  GUTTER_WIDTH,
  TITLE_BAR_HEIGHT,
  TAB_BAR_HEIGHT,
  CODE_FONT_SIZE,
} from "./constants";

interface BlinkingCursorProps {
  scrollOffset: number;
}

const BlinkingCursor: React.FC<BlinkingCursorProps> = ({ scrollOffset }) => {
  const frame = useCurrentFrame();

  // Convert blink timing from ms to frames
  const blinkCycleFrames = (CURSOR_BLINK_MS * 2 * FPS) / 1000;
  const blinkOnFrames = (CURSOR_BLINK_MS * FPS) / 1000;

  // Determine if cursor is visible in this frame
  const posInCycle = frame % blinkCycleFrames;
  const isVisible = posInCycle < blinkOnFrames;

  // Position: line 1, after "def process_order(order, user, config):"
  // The cursor sits at the end of the function signature
  const cursorLeft = GUTTER_WIDTH + 16 + CODE_FONT_SIZE * 0.6 * 44; // approx char width * chars
  const cursorTop =
    TITLE_BAR_HEIGHT + TAB_BAR_HEIGHT + 8 - scrollOffset;

  return (
    <div
      style={{
        position: "absolute",
        left: cursorLeft,
        top: cursorTop,
        width: CURSOR_WIDTH,
        height: CURSOR_HEIGHT,
        backgroundColor: CURSOR_COLOR,
        opacity: isVisible ? 1 : 0,
        zIndex: 10,
      }}
    />
  );
};

export default BlinkingCursor;
