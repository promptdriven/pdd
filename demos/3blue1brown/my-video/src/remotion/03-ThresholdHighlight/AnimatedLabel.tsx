import React from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { BEATS, COLORS } from "./constants";

interface AnimatedLabelProps {
  text: string;
  targetX: number;
  targetY: number;
  offsetX?: number;
  offsetY?: number;
}

export const AnimatedLabel: React.FC<AnimatedLabelProps> = ({
  text,
  targetX,
  targetY,
  offsetX = 80,
  offsetY = -60,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // Label fade in with easeOutCubic
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABEL_FADE_START, BEATS.LABEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Connector line draws in
  const lineProgress = interpolate(
    frame,
    [BEATS.LABEL_FADE_START, BEATS.LABEL_FADE_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const labelX = targetX + offsetX;
  const labelY = targetY + offsetY;

  // Calculate connector line endpoints
  const lineEndX = targetX + lineProgress * (labelX - targetX - 40);
  const lineEndY = targetY + lineProgress * (labelY - targetY + 15);

  return (
    <>
      {/* Connector line */}
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        {lineProgress > 0 && (
          <line
            x1={targetX}
            y1={targetY}
            x2={lineEndX}
            y2={lineEndY}
            stroke={COLORS.MARKER}
            strokeWidth={2}
            strokeDasharray="6,4"
            opacity={labelOpacity * 0.7}
          />
        )}
      </svg>

      {/* Label text */}
      <div
        style={{
          position: "absolute",
          left: labelX,
          top: labelY,
          transform: "translate(-50%, -50%)",
          opacity: labelOpacity,
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 28,
          fontWeight: 700,
          color: COLORS.MARKER,
          textShadow: `0 0 20px ${COLORS.PULSE_GLOW}, 0 2px 10px rgba(0,0,0,0.8)`,
          whiteSpace: "nowrap",
          padding: "10px 20px",
          backgroundColor: "rgba(26, 26, 46, 0.8)",
          borderRadius: 8,
          border: `2px solid ${COLORS.PULSE_GLOW}`,
        }}
      >
        {text}
      </div>
    </>
  );
};
