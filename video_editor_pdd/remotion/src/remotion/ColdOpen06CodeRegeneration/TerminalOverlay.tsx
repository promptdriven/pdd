import React from "react";
import {
  TERMINAL_BG,
  TERMINAL_OPACITY,
  TERMINAL_GREEN,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_BORDER_RADIUS,
  TERMINAL_FONT_SIZE,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

interface TerminalOverlayProps {
  /** Command text to display. */
  command: string;
  /** 0–1 opacity for fade-in. */
  opacity: number;
}

/**
 * Small terminal widget in the bottom-right corner showing the pdd command.
 */
const TerminalOverlay: React.FC<TerminalOverlayProps> = ({
  command,
  opacity,
}) => {
  return (
    <div
      style={{
        position: "absolute",
        left: CANVAS_WIDTH - TERMINAL_WIDTH - 32,
        top: CANVAS_HEIGHT - TERMINAL_HEIGHT - 32,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        opacity: opacity * TERMINAL_OPACITY,
        borderRadius: TERMINAL_BORDER_RADIUS,
        display: "flex",
        alignItems: "center",
        paddingLeft: 16,
        paddingRight: 16,
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: TERMINAL_FONT_SIZE,
        color: TERMINAL_GREEN,
        boxShadow: "0 4px 24px rgba(0,0,0,0.5)",
      }}
    >
      <span style={{ opacity: 0.5 }}>$&nbsp;</span>
      <span>{command}</span>
      <span style={{ marginLeft: 8 }}>✓</span>
    </div>
  );
};

export default TerminalOverlay;
