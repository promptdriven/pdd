import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CMD_FONT_SIZE,
  CMD_FONT_WEIGHT,
  PROMPT_COLOR,
  PROMPT_OPACITY,
  FRAMES_PER_CHAR,
  PULSE_CYCLE_FRAMES,
  PULSE_MIN_OPACITY,
  PULSE_MAX_OPACITY,
} from "./constants";

interface TerminalLineProps {
  command: string;
  color: string;
  y?: number;
  framesPerChar?: number;
  pulseOnHold?: boolean;
  pulseStartFrame?: number;
}

export const TerminalLine: React.FC<TerminalLineProps> = ({
  command,
  color,
  y = 0,
  framesPerChar = FRAMES_PER_CHAR,
  pulseOnHold = false,
  pulseStartFrame = 0,
}) => {
  const frame = useCurrentFrame();
  const totalTypeFrames = command.length * framesPerChar;
  const charsVisible = Math.min(
    Math.floor(frame / framesPerChar),
    command.length
  );
  const displayedCommand = command.slice(0, charsVisible);
  const showCursor = charsVisible < command.length;
  const typingComplete = frame >= totalTypeFrames;

  // Pulse effect for the teal command once it's done typing and hold begins
  let lineOpacity = 1;
  if (pulseOnHold && typingComplete && pulseStartFrame > 0) {
    // frame in the Sequence context, pulseStartFrame is relative to Sequence start
    const holdFrame = frame - totalTypeFrames;
    if (holdFrame >= 0) {
      // Cycle using sine wave
      const cycleProgress = (holdFrame % PULSE_CYCLE_FRAMES) / PULSE_CYCLE_FRAMES;
      lineOpacity = interpolate(
        Math.sin(cycleProgress * Math.PI * 2),
        [-1, 1],
        [PULSE_MIN_OPACITY, PULSE_MAX_OPACITY],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );
    }
  }

  return (
    <div
      style={{
        position: "absolute",
        top: y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        opacity: lineOpacity,
      }}
    >
      <span
        style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: CMD_FONT_SIZE,
          fontWeight: CMD_FONT_WEIGHT,
          whiteSpace: "pre",
        }}
      >
        <span style={{ color: PROMPT_COLOR, opacity: PROMPT_OPACITY }}>
          ${" "}
        </span>
        <span style={{ color }}>{displayedCommand}</span>
        {showCursor && (
          <span
            style={{
              display: "inline-block",
              width: 2,
              height: CMD_FONT_SIZE * 0.8,
              backgroundColor: color,
              marginLeft: 1,
              verticalAlign: "middle",
              opacity: 0.7,
            }}
          />
        )}
      </span>
    </div>
  );
};
