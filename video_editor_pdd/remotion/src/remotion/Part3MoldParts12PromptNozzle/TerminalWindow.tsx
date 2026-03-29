import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  TERMINAL_GREEN,
  TERMINAL_BG,
  TERMINAL_BORDER,
  TERMINAL_X,
  TERMINAL_Y,
  TERMINAL_W,
  TERMINAL_H,
  PHASE_DRAIN_START,
  PHASE_SECOND_FILL_START,
} from "./constants";

const COMMAND = "$ pdd generate user_parser.prompt";
const HASH_1 = " → 0xa3f7d2";
const HASH_2 = " → 0x91cb4e";
const CURSOR_BLINK_RATE = 15; // frames per blink cycle

export const TerminalWindow: React.FC = () => {
  const frame = useCurrentFrame();

  // Terminal fades in at PHASE_DRAIN_START (frame 300)
  const terminalOpacity = interpolate(
    frame,
    [PHASE_DRAIN_START, PHASE_DRAIN_START + 15],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // First command types in at frame 300
  const cmd1Start = PHASE_DRAIN_START;
  const cmd1CharFrame = frame - cmd1Start;
  const cmd1Chars = Math.min(
    Math.max(0, Math.floor(cmd1CharFrame / 1.5)),
    COMMAND.length
  );
  const showHash1 = cmd1Chars >= COMMAND.length && frame > cmd1Start + COMMAND.length * 1.5 + 10;

  // Second command types in at frame 360
  const cmd2Start = PHASE_SECOND_FILL_START;
  const cmd2CharFrame = frame - cmd2Start;
  const cmd2Chars = Math.min(
    Math.max(0, Math.floor(cmd2CharFrame / 1.5)),
    COMMAND.length
  );
  const showCmd2 = frame >= cmd2Start;
  const showHash2 = showCmd2 && cmd2Chars >= COMMAND.length && frame > cmd2Start + COMMAND.length * 1.5 + 10;

  // Blinking cursor
  const cursorVisible = Math.floor(frame / CURSOR_BLINK_RATE) % 2 === 0;

  return (
    <div
      style={{
        position: "absolute",
        left: TERMINAL_X,
        top: TERMINAL_Y,
        width: TERMINAL_W,
        height: TERMINAL_H,
        backgroundColor: TERMINAL_BG,
        border: `1px solid ${TERMINAL_BORDER}`,
        borderRadius: 6,
        padding: 10,
        opacity: terminalOpacity,
        overflow: "hidden",
      }}
    >
      {/* Terminal title bar */}
      <div
        style={{
          display: "flex",
          gap: 4,
          marginBottom: 8,
        }}
      >
        <div style={{ width: 8, height: 8, borderRadius: "50%", backgroundColor: "#FF5F56" }} />
        <div style={{ width: 8, height: 8, borderRadius: "50%", backgroundColor: "#FFBD2E" }} />
        <div style={{ width: 8, height: 8, borderRadius: "50%", backgroundColor: "#27C93F" }} />
      </div>

      {/* Command 1 */}
      <div
        style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 11,
          color: TERMINAL_GREEN,
          lineHeight: 1.5,
          whiteSpace: "pre",
        }}
      >
        {COMMAND.substring(0, cmd1Chars)}
        {showHash1 && (
          <span style={{ color: "#79C0FF" }}>{HASH_1}</span>
        )}
      </div>

      {/* Command 2 */}
      {showCmd2 && (
        <div
          style={{
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 11,
            color: TERMINAL_GREEN,
            lineHeight: 1.5,
            whiteSpace: "pre",
          }}
        >
          {COMMAND.substring(0, cmd2Chars)}
          {showHash2 && (
            <span style={{ color: "#79C0FF" }}>{HASH_2}</span>
          )}
          {!showHash2 && cursorVisible && (
            <span style={{ color: TERMINAL_GREEN }}>▋</span>
          )}
        </div>
      )}
    </div>
  );
};
