import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  NOZZLE_OPENING_Y,
  MOLD_INNER_LEFT,
  MOLD_INNER_TOP,
  MOLD_INNER_W,
  PROMPT_TEXT,
  PHASE_TEXT_STREAM_START,
} from "./constants";

const CHAR_DELAY = 2; // frames per character
const CHARS_PER_LINE = 50;

/**
 * Streams prompt text character-by-character from the nozzle into the cavity.
 * Characters transition from amber to teal as they "enter" the mold.
 */
export const TextStream: React.FC = () => {
  const frame = useCurrentFrame();
  const streamFrame = frame - PHASE_TEXT_STREAM_START;

  if (streamFrame < 0) return null;

  const totalChars = PROMPT_TEXT.length;
  const charsVisible = Math.min(
    Math.floor(streamFrame / CHAR_DELAY),
    totalChars
  );

  // Split text into lines for display
  const lines: string[] = [];
  let remaining = PROMPT_TEXT.substring(0, charsVisible);
  while (remaining.length > 0) {
    if (remaining.length <= CHARS_PER_LINE) {
      lines.push(remaining);
      break;
    }
    // Break at last space before limit
    const breakIdx = remaining.lastIndexOf(" ", CHARS_PER_LINE);
    const splitAt = breakIdx > 0 ? breakIdx + 1 : CHARS_PER_LINE;
    lines.push(remaining.substring(0, splitAt));
    remaining = remaining.substring(splitAt);
  }

  // Text starts at nozzle and flows down into cavity
  const startY = NOZZLE_OPENING_Y + 10;
  const textAreaTop = MOLD_INNER_TOP + 20;

  // Progress: how far text has "fallen" into the cavity
  const fallProgress = interpolate(
    streamFrame,
    [0, totalChars * CHAR_DELAY],
    [0, 1],
    { extrapolateRight: "clamp" }
  );

  // Transform: amber at top → teal deeper in cavity
  const textY = startY + fallProgress * (textAreaTop - startY + 40);

  // Color transition as text enters cavity
  const colorProgress = interpolate(
    streamFrame,
    [totalChars * CHAR_DELAY * 0.3, totalChars * CHAR_DELAY],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.sin) }
  );

  // Interpolate color components
  const r = Math.round(217 + (13 - 217) * colorProgress);
  const g = Math.round(148 + (148 - 148) * colorProgress);
  const b = Math.round(74 + (136 - 74) * colorProgress);
  const textColor = `rgb(${r}, ${g}, ${b})`;

  return (
    <div
      style={{
        position: "absolute",
        left: MOLD_INNER_LEFT + 20,
        top: textY,
        width: MOLD_INNER_W - 40,
        overflow: "hidden",
      }}
    >
      {lines.map((line, i) => (
        <div
          key={i}
          style={{
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 12,
            color: textColor,
            lineHeight: 1.6,
            whiteSpace: "pre",
            opacity: 0.9,
          }}
        >
          {line}
        </div>
      ))}
    </div>
  );
};
