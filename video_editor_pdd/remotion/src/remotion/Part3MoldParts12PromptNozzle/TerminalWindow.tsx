import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import { TERMINAL_GREEN, PHASE_DRAIN_START } from "./constants";

const TERMINAL_X = 1450;
const TERMINAL_Y = 900;
const TERMINAL_W = 420;
const TERMINAL_H = 100;
const TERMINAL_BORDER_RADIUS = 6;

interface TerminalLine {
  text: string;
  frame: number;
}

const LINES: TerminalLine[] = [
  { text: "$ pdd generate user_parser.prompt", frame: 300 },
  { text: "  → output: a3f7c2d", frame: 330 },
  { text: "$ pdd generate user_parser.prompt", frame: 360 },
  { text: "  → output: e1b94f8", frame: 390 },
];

export const TerminalWindow: React.FC = () => {
  const frame = useCurrentFrame();

  // Terminal fades in at frame 300
  const terminalOpacity = interpolate(
    frame,
    [PHASE_DRAIN_START, PHASE_DRAIN_START + 15],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  if (frame < PHASE_DRAIN_START) return null;

  const visibleLines = LINES.filter((line) => frame >= line.frame);

  return (
    <div
      style={{
        position: "absolute",
        left: TERMINAL_X,
        top: TERMINAL_Y,
        width: TERMINAL_W,
        height: TERMINAL_H,
        backgroundColor: "#0D1117",
        border: "1px solid #30363D",
        borderRadius: TERMINAL_BORDER_RADIUS,
        padding: "8px 12px",
        opacity: terminalOpacity,
        overflow: "hidden",
      }}
    >
      {/* Title bar dots */}
      <div
        style={{
          display: "flex",
          gap: 5,
          marginBottom: 6,
        }}
      >
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: "50%",
            backgroundColor: "#FF5F57",
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: "50%",
            backgroundColor: "#FEBC2E",
          }}
        />
        <div
          style={{
            width: 8,
            height: 8,
            borderRadius: "50%",
            backgroundColor: "#28C840",
          }}
        />
      </div>

      {/* Terminal lines */}
      {visibleLines.map((line, i) => {
        const lineAge = frame - line.frame;
        const charCount = Math.min(
          Math.floor(lineAge * 2),
          line.text.length
        );
        const displayText = line.text.slice(0, charCount);

        return (
          <div
            key={i}
            style={{
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 11,
              color: line.text.startsWith("$") ? TERMINAL_GREEN : "#8B949E",
              lineHeight: "16px",
              whiteSpace: "pre",
            }}
          >
            {displayText}
          </div>
        );
      })}
    </div>
  );
};
