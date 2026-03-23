import React from "react";
import { useCurrentFrame } from "remotion";

interface TerminalCursorProps {
  visible: boolean;
  color: string;
  width: number;
  height: number;
  blinkRate?: number; // frames per blink cycle
}

export const TerminalCursor: React.FC<TerminalCursorProps> = ({
  visible,
  color,
  width,
  height,
  blinkRate = 16,
}) => {
  const frame = useCurrentFrame();

  if (!visible) return null;

  // Blink: on for half the cycle, off for the other half
  const cyclePos = frame % blinkRate;
  const isOn = cyclePos < blinkRate / 2;

  return (
    <div
      style={{
        width,
        height,
        backgroundColor: color,
        opacity: isOn ? 0.95 : 0,
        borderRadius: 1,
        display: "inline-block",
        marginLeft: 4,
        verticalAlign: "middle",
        transition: "opacity 0.05s",
      }}
    />
  );
};

export default TerminalCursor;
