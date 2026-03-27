import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TITLE_COLOR,
  TITLE_FONT_SIZE,
  CANVAS_W,
  FADEOUT_START,
  FADEOUT_DURATION,
} from "./constants";

interface TypeWriterTextProps {
  text: string;
  /** Frame (relative to Sequence) at which typing starts */
  startFrame: number;
  /** Frames per character reveal */
  framesPerChar: number;
  y: number;
  offsetX?: number;
}

/**
 * Character-by-character typewriter reveal for a single line of text.
 */
export const TypeWriterText: React.FC<TypeWriterTextProps> = ({
  text,
  startFrame,
  framesPerChar,
  y,
  offsetX = 0,
}) => {
  const frame = useCurrentFrame();

  const totalChars = text.length;
  const typingEnd = startFrame + totalChars * framesPerChar;

  // Number of visible characters
  const visibleChars = Math.floor(
    interpolate(frame, [startFrame, typingEnd], [0, totalChars], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    })
  );

  const displayText = text.slice(0, visibleChars);

  // Blinking cursor while typing (disappears after typing is done + 15 frames)
  const cursorVisible =
    frame >= startFrame &&
    frame < typingEnd + 15 &&
    Math.floor((frame - startFrame) / 8) % 2 === 0;

  // Fade-out at end
  const fadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  if (frame < startFrame) return null;

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        width: CANVAS_W,
        display: "flex",
        justifyContent: "center",
        opacity: fadeOut,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: TITLE_FONT_SIZE,
          fontWeight: 700,
          color: TITLE_COLOR,
          letterSpacing: "2px",
          marginLeft: offsetX,
          whiteSpace: "pre",
        }}
      >
        {displayText}
        {cursorVisible && (
          <span style={{ opacity: 0.6, fontWeight: 400 }}>|</span>
        )}
      </span>
    </div>
  );
};

export default TypeWriterText;
