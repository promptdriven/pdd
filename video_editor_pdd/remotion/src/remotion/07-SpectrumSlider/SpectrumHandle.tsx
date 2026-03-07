import React from "react";
import {
  BAR_Y,
  BAR_X_START,
  BAR_WIDTH,
  HANDLE_SIZE,
  HANDLE_GLOW_RADIUS,
  WHITE,
} from "./constants";

interface SpectrumHandleProps {
  /** Normalized position 0-1 along the bar */
  position: number;
  /** Scale factor (spring animated) */
  scale: number;
  /** Glow color (interpolated hex) */
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
  const x = BAR_X_START + position * BAR_WIDTH;

  // Pulse glow: subtle size oscillation
  return (
    <div
      style={{
        position: "absolute",
        left: x - HANDLE_GLOW_RADIUS,
        top: BAR_Y - HANDLE_GLOW_RADIUS,
        width: HANDLE_GLOW_RADIUS * 2,
        height: HANDLE_GLOW_RADIUS * 2,
        opacity,
        transform: `scale(${scale})`,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
      }}
    >
      {/* Glow */}
      <div
        style={{
          position: "absolute",
          width: HANDLE_GLOW_RADIUS * 2,
          height: HANDLE_GLOW_RADIUS * 2,
          borderRadius: "50%",
          background: `radial-gradient(circle, ${glowColor}66 0%, ${glowColor}00 70%)`,
        }}
      />
      {/* Dot */}
      <div
        style={{
          position: "relative",
          width: HANDLE_SIZE,
          height: HANDLE_SIZE,
          borderRadius: "50%",
          backgroundColor: WHITE,
          boxShadow: `0 0 20px ${glowColor}, 0 0 40px ${glowColor}88`,
        }}
      />
    </div>
  );
};
