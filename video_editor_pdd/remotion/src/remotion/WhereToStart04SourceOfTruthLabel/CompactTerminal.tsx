import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_RADIUS,
  TERMINAL_BG,
  TEXT_LIGHT,
  GREEN_ACCENT,
  TERMINAL_FADE_START,
  TERMINAL_FADE_DURATION,
  CMD_GENERATE_START,
  CMD_GENERATE_TEXT,
  CMD_TEST_START,
  CMD_TEST_TEXT,
  CHECKMARK_START,
  CHECKMARK_DURATION,
  CHECKMARK_TEXT,
} from "./constants";

const CHAR_FRAMES = 3; // 3 frames per character

interface TypedLineProps {
  text: string;
  startFrame: number;
  color: string;
  prefix?: string;
}

const TypedLine: React.FC<TypedLineProps> = ({ text, startFrame, color, prefix = "$ " }) => {
  const frame = useCurrentFrame();
  const elapsed = Math.max(0, frame - startFrame);
  const charsVisible = Math.min(Math.floor(elapsed / CHAR_FRAMES), text.length);

  if (frame < startFrame) return null;

  return (
    <div
      style={{
        fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
        fontSize: 13,
        color,
        lineHeight: "20px",
        whiteSpace: "nowrap",
      }}
    >
      <span style={{ opacity: 0.5 }}>{prefix}</span>
      {text.slice(0, charsVisible)}
      {charsVisible < text.length && (
        <span
          style={{
            display: "inline-block",
            width: 7,
            height: 14,
            backgroundColor: color,
            opacity: frame % 16 < 8 ? 0.8 : 0,
            verticalAlign: "middle",
            marginLeft: 1,
          }}
        />
      )}
    </div>
  );
};

export const CompactTerminal: React.FC = () => {
  const frame = useCurrentFrame();

  // Terminal container fade in (frames 0-15)
  const containerOpacity = interpolate(
    frame,
    [TERMINAL_FADE_START, TERMINAL_FADE_START + TERMINAL_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Checkmark scale-in with back easing
  const checkmarkVisible = frame >= CHECKMARK_START;
  const checkmarkScale = checkmarkVisible
    ? interpolate(
        frame,
        [CHECKMARK_START, CHECKMARK_START + CHECKMARK_DURATION],
        [0.3, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.7)) }
      )
    : 0;

  const checkmarkOpacity = checkmarkVisible
    ? interpolate(
        frame,
        [CHECKMARK_START, CHECKMARK_START + 5],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  return (
    <div
      style={{
        position: "absolute",
        left: TERMINAL_X - TERMINAL_WIDTH / 2,
        top: TERMINAL_Y,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT + 20, // extra room for 3 lines
        borderRadius: TERMINAL_RADIUS,
        backgroundColor: TERMINAL_BG,
        opacity: containerOpacity,
        padding: "10px 14px",
        display: "flex",
        flexDirection: "column",
        justifyContent: "center",
        gap: 2,
        border: "1px solid rgba(148, 163, 184, 0.1)",
      }}
    >
      {/* Line 1: pdd generate */}
      <TypedLine
        text={CMD_GENERATE_TEXT}
        startFrame={CMD_GENERATE_START}
        color={TEXT_LIGHT}
      />

      {/* Line 2: pdd test */}
      <TypedLine
        text={CMD_TEST_TEXT}
        startFrame={CMD_TEST_START}
        color={TEXT_LIGHT}
      />

      {/* Line 3: Checkmark result */}
      {checkmarkVisible && (
        <div
          style={{
            fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
            fontSize: 13,
            color: GREEN_ACCENT,
            lineHeight: "20px",
            whiteSpace: "nowrap",
            transform: `scale(${checkmarkScale})`,
            transformOrigin: "left center",
            opacity: checkmarkOpacity,
          }}
        >
          {CHECKMARK_TEXT}
        </div>
      )}
    </div>
  );
};
