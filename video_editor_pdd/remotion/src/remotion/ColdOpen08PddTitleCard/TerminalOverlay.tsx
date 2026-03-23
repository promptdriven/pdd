import React from "react";
import {
  TERMINAL_BG,
  TERMINAL_BORDER,
  TERMINAL_BORDER_RADIUS,
  TERMINAL_CMD_COLOR,
  TERMINAL_HEIGHT,
  TERMINAL_PROMPT_COLOR,
  TERMINAL_STATS_COLOR,
  TERMINAL_WIDTH,
  TERMINAL_X,
  TERMINAL_Y,
} from "./constants";

interface TerminalOverlayProps {
  opacity: number;
}

export const TerminalOverlay: React.FC<TerminalOverlayProps> = ({ opacity }) => {
  // Position: bottom-right corner. x/y from spec are center-ish references;
  // we position via right/bottom for simplicity.
  const right = 1920 - TERMINAL_X - TERMINAL_WIDTH / 2;
  const top = TERMINAL_Y - TERMINAL_HEIGHT / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: TERMINAL_X - TERMINAL_WIDTH / 2,
        top,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        border: `1px solid ${TERMINAL_BORDER}`,
        borderRadius: TERMINAL_BORDER_RADIUS,
        opacity,
        padding: "10px 14px",
        display: "flex",
        flexDirection: "column",
        justifyContent: "center",
        gap: 4,
        fontFamily: "'JetBrains Mono', 'Fira Code', 'Consolas', monospace",
        fontSize: 11,
      }}
    >
      {/* Prompt line */}
      <div style={{ display: "flex", gap: 6 }}>
        <span style={{ color: TERMINAL_PROMPT_COLOR }}>$</span>
        <span style={{ color: TERMINAL_CMD_COLOR }}>pdd generate</span>
      </div>

      {/* Output line */}
      <div style={{ display: "flex", gap: 6 }}>
        <span style={{ color: TERMINAL_PROMPT_COLOR }}>&#10003;</span>
        <span style={{ color: TERMINAL_PROMPT_COLOR }}>UserService.ts regenerated</span>
        <span style={{ color: TERMINAL_STATS_COLOR }}>(18 lines, 3 tests passing)</span>
      </div>
    </div>
  );
};
