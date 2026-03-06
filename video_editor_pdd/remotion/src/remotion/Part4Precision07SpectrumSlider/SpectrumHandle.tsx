import React from "react";
import {
  BAR_X,
  BAR_Y,
  BAR_WIDTH,
  BAR_HEIGHT,
  HANDLE_SIZE,
  HANDLE_GLOW_RADIUS,
} from "./constants";

interface SpectrumHandleProps {
  /** Normalized position 0-1 along the bar */
  position: number;
  /** Scale of the handle (0 = invisible, 1 = full) */
  scale: number;
  /** Color of the glow and handle ring */
  glowColor: string;
  /** Overall opacity for fade out */
  opacity: number;
}

export const SpectrumHandle: React.FC<SpectrumHandleProps> = ({
  position,
  scale,
  glowColor,
  opacity,
}) => {
  const cx = BAR_X + position * BAR_WIDTH;
  const cy = BAR_Y + BAR_HEIGHT / 2;

  // Pulsing glow amplitude (using CSS animation isn't available, so we rely on parent passing glowColor)
  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        opacity,
        pointerEvents: "none",
      }}
    >
      {/* Outer glow */}
      <div
        style={{
          position: "absolute",
          left: cx - HANDLE_GLOW_RADIUS,
          top: cy - HANDLE_GLOW_RADIUS,
          width: HANDLE_GLOW_RADIUS * 2,
          height: HANDLE_GLOW_RADIUS * 2,
          borderRadius: "50%",
          backgroundColor: glowColor,
          opacity: 0.35 * scale,
          filter: "blur(16px)",
          transform: `scale(${scale})`,
        }}
      />

      {/* Handle dot */}
      <div
        style={{
          position: "absolute",
          left: cx - HANDLE_SIZE / 2,
          top: cy - HANDLE_SIZE / 2,
          width: HANDLE_SIZE,
          height: HANDLE_SIZE,
          borderRadius: "50%",
          backgroundColor: "#FFFFFF",
          boxShadow: `0 0 20px ${glowColor}, 0 0 40px ${glowColor}40`,
          transform: `scale(${scale})`,
          border: `2px solid ${glowColor}`,
        }}
      />
    </div>
  );
};
