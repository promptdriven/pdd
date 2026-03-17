import React from "react";
import { useCurrentFrame } from "remotion";
import {
  TYPEWRITER_START,
  TYPEWRITER_CHAR_DELAY,
  TITLE_COLOR,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_LINE1_Y,
  TITLE_LINE1_TEXT,
} from "./constants";

export const TypewriterText: React.FC = () => {
  const frame = useCurrentFrame();

  const elapsed = Math.max(0, frame - TYPEWRITER_START);
  const charsVisible = Math.min(
    Math.floor(elapsed / TYPEWRITER_CHAR_DELAY),
    TITLE_LINE1_TEXT.length
  );

  const visibleText = TITLE_LINE1_TEXT.slice(0, charsVisible);

  // Show cursor blinking during typing
  const showCursor =
    charsVisible < TITLE_LINE1_TEXT.length && elapsed > 0 && frame % 6 < 4;

  return (
    <div
      style={{
        position: "absolute",
        top: TITLE_LINE1_Y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        fontFamily: "'Inter', sans-serif",
        fontWeight: TITLE_FONT_WEIGHT,
        fontSize: TITLE_FONT_SIZE,
        color: TITLE_COLOR,
        textAlign: "center" as const,
        whiteSpace: "nowrap" as const,
      }}
    >
      {visibleText}
      {showCursor && (
        <span style={{ opacity: 0.7, marginLeft: 2 }}>|</span>
      )}
    </div>
  );
};

export default TypewriterText;
