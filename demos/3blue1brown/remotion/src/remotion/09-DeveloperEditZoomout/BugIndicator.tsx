import React from "react";
import { interpolate, Easing } from "remotion";
import { COLORS, ACTIVE_FILE, BUG_FILE, BEATS } from "./constants";

/**
 * Red pulsing bug indicator on a distant file, with a faint connection
 * line back to the recent edit (showing causation).
 */
export const BugIndicator: React.FC<{ frame: number }> = ({ frame }) => {
  if (frame < BEATS.BUG_START) return null;

  const progress = interpolate(
    frame,
    [BEATS.BUG_START, BEATS.BUG_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Pulse animation
  const pulse = 0.6 + 0.4 * Math.sin((frame - BEATS.BUG_START) * 0.2);
  const pulseRadius = 18 + 8 * Math.sin((frame - BEATS.BUG_START) * 0.15);

  // Connection line draw progress
  const lineProgress = interpolate(
    frame,
    [BEATS.BUG_START + 15, BEATS.BUG_START + 45],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Label fade
  const labelOpacity = interpolate(
    frame,
    [BEATS.BUG_START + 35, BEATS.BUG_START + 50],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const bugCx = BUG_FILE.x + BUG_FILE.w / 2;
  const bugCy = BUG_FILE.y + BUG_FILE.h / 2;
  const editCx = ACTIVE_FILE.x + ACTIVE_FILE.w / 2;
  const editCy = ACTIVE_FILE.y + ACTIVE_FILE.h / 2;

  // Interpolated line endpoint
  const lineEndX = editCx + (bugCx - editCx) * lineProgress;
  const lineEndY = editCy + (bugCy - editCy) * lineProgress;

  return (
    <g opacity={progress}>
      {/* Connection line (dashed, faint) */}
      {lineProgress > 0 && (
        <line
          x1={editCx}
          y1={editCy}
          x2={lineEndX}
          y2={lineEndY}
          stroke={COLORS.CONNECTION_LINE}
          strokeWidth={2}
          strokeDasharray="8,6"
        />
      )}

      {/* Outer glow pulse */}
      <circle
        cx={bugCx}
        cy={bugCy}
        r={pulseRadius}
        fill="none"
        stroke={COLORS.BUG_GLOW}
        strokeWidth={2.5}
        opacity={pulse * 0.5}
      />

      {/* Inner red dot */}
      <circle
        cx={bugCx}
        cy={bugCy}
        r={8}
        fill={COLORS.BUG_RED}
        opacity={pulse}
      />

      {/* "New issue" label */}
      {labelOpacity > 0 && (
        <g opacity={labelOpacity}>
          <rect
            x={bugCx + 16}
            y={bugCy - 10}
            width={80}
            height={20}
            rx={4}
            fill="rgba(244, 71, 71, 0.18)"
          />
          <text
            x={bugCx + 22}
            y={bugCy + 4}
            fontSize={12}
            fontFamily="sans-serif"
            fontWeight={600}
            fill={COLORS.BUG_RED}
          >
            New issue
          </text>
        </g>
      )}
    </g>
  );
};
