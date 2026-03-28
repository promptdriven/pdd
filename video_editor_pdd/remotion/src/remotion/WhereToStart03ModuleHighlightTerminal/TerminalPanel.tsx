import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TERMINAL_BG,
  GREEN_ACCENT,
  TEXT_LIGHT,
  CANVAS_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_Y,
  TERMINAL_SLIDE_START,
  TERMINAL_SLIDE_DURATION,
  TYPE_START,
  CHAR_DELAY,
  COMMAND_TEXT,
} from "./constants";

/**
 * Terminal panel that slides up from the bottom and types out the command.
 * Includes a blinking cursor.
 */
export const TerminalPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Slide up from bottom
  const slideOffset = interpolate(
    frame,
    [TERMINAL_SLIDE_START, TERMINAL_SLIDE_START + TERMINAL_SLIDE_DURATION],
    [TERMINAL_HEIGHT, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Number of characters visible
  const charsVisible =
    frame < TYPE_START
      ? 0
      : Math.min(
          Math.floor((frame - TYPE_START) / CHAR_DELAY),
          COMMAND_TEXT.length
        );

  const typedText = COMMAND_TEXT.substring(0, charsVisible);
  const isTypingDone = charsVisible >= COMMAND_TEXT.length;

  // Blinking cursor: visible every 15 frames
  const cursorVisible =
    frame >= TERMINAL_SLIDE_START + TERMINAL_SLIDE_DURATION &&
    Math.floor(frame / 15) % 2 === 0;

  // Processing indicator after typing completes
  const showProcessing =
    isTypingDone && frame < TYPE_START + COMMAND_TEXT.length * CHAR_DELAY + 30;
  const processingDots =
    showProcessing
      ? ".".repeat(Math.floor(((frame - (TYPE_START + COMMAND_TEXT.length * CHAR_DELAY)) % 12) / 4) + 1)
      : "";

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: TERMINAL_Y + slideOffset,
        width: CANVAS_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        borderTop: "1px solid rgba(90, 170, 110, 0.3)",
        padding: "20px 40px",
        display: "flex",
        flexDirection: "column",
        justifyContent: "flex-start",
      }}
    >
      {/* Command line */}
      <div
        style={{
          fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
          fontSize: 16,
          lineHeight: "24px",
          display: "flex",
          alignItems: "center",
        }}
      >
        {/* Prompt character */}
        <span style={{ color: GREEN_ACCENT, marginRight: 10 }}>$</span>

        {/* Typed text */}
        <span style={{ color: TEXT_LIGHT }}>{typedText}</span>

        {/* Cursor */}
        <span
          style={{
            display: "inline-block",
            width: 9,
            height: 18,
            backgroundColor: cursorVisible ? GREEN_ACCENT : "transparent",
            marginLeft: 1,
            verticalAlign: "middle",
          }}
        />
      </div>

      {/* Processing output after command completes */}
      {isTypingDone && (
        <div
          style={{
            fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
            fontSize: 14,
            color: GREEN_ACCENT,
            opacity: 0.7,
            marginTop: 8,
          }}
        >
          {showProcessing
            ? `Generating prompt${processingDots}`
            : "✓ auth_handler.prompt.md created"}
        </div>
      )}
    </div>
  );
};

export default TerminalPanel;
