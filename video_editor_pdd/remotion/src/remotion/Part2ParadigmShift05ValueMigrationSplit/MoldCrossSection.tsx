import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  MOLD_WALL_COLOR,
  MOLD_CAVITY_COLOR,
  MOLD_DRAW_START,
  MOLD_DRAW_END,
} from "./constants";

const PANEL_WIDTH = 958;

export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [MOLD_DRAW_START, MOLD_DRAW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  const halfW = MOLD_WIDTH / 2;
  const halfH = MOLD_HEIGHT / 2;

  // Mold cavity shape — a simplified cross-section showing left wall, right wall, bottom,
  // with an open top (like a bucket/mold)
  const moldX = MOLD_CENTER_X - halfW;
  const moldY = MOLD_CENTER_Y - halfH + 60;
  const moldW = MOLD_WIDTH;
  const moldH = MOLD_HEIGHT - 120;

  // Mold path — U-shape for cross-section
  const moldPathLength = moldW + moldH * 2;
  const visibleLength = drawProgress * moldPathLength;

  return (
    <svg
      width={PANEL_WIDTH}
      height={1080}
      viewBox={`0 0 ${PANEL_WIDTH} 1080`}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Mold cavity fill */}
      <rect
        x={moldX + 20}
        y={moldY + 20}
        width={moldW - 40}
        height={moldH - 20}
        rx={4}
        fill={MOLD_CAVITY_COLOR}
        opacity={drawProgress * 0.3}
      />

      {/* Mold outer walls — left */}
      <rect
        x={moldX}
        y={moldY}
        width={20}
        height={moldH}
        rx={2}
        fill="none"
        stroke={MOLD_WALL_COLOR}
        strokeWidth={3}
        opacity={drawProgress * 0.5}
        strokeDasharray={moldPathLength}
        strokeDashoffset={moldPathLength - visibleLength}
      />
      {/* Mold outer walls — right */}
      <rect
        x={moldX + moldW - 20}
        y={moldY}
        width={20}
        height={moldH}
        rx={2}
        fill="none"
        stroke={MOLD_WALL_COLOR}
        strokeWidth={3}
        opacity={drawProgress * 0.5}
        strokeDasharray={moldPathLength}
        strokeDashoffset={moldPathLength - visibleLength}
      />
      {/* Mold outer walls — bottom */}
      <rect
        x={moldX}
        y={moldY + moldH - 20}
        width={moldW}
        height={20}
        rx={2}
        fill="none"
        stroke={MOLD_WALL_COLOR}
        strokeWidth={3}
        opacity={drawProgress * 0.5}
        strokeDasharray={moldPathLength}
        strokeDashoffset={moldPathLength - visibleLength}
      />

      {/* Mold filled walls */}
      <rect
        x={moldX}
        y={moldY}
        width={20}
        height={moldH}
        rx={2}
        fill={MOLD_WALL_COLOR}
        opacity={drawProgress * 0.3}
      />
      <rect
        x={moldX + moldW - 20}
        y={moldY}
        width={20}
        height={moldH}
        rx={2}
        fill={MOLD_WALL_COLOR}
        opacity={drawProgress * 0.3}
      />
      <rect
        x={moldX}
        y={moldY + moldH - 20}
        width={moldW}
        height={20}
        rx={2}
        fill={MOLD_WALL_COLOR}
        opacity={drawProgress * 0.3}
      />

      {/* Top cap / clamping plate hints */}
      <line
        x1={moldX - 20}
        y1={moldY - 5}
        x2={moldX + moldW + 20}
        y2={moldY - 5}
        stroke={MOLD_WALL_COLOR}
        strokeWidth={2}
        opacity={drawProgress * 0.25}
        strokeDasharray="8 4"
      />

      {/* Injection channel — small triangle at top center */}
      <polygon
        points={`${MOLD_CENTER_X - 10},${moldY - 5} ${MOLD_CENTER_X + 10},${moldY - 5} ${MOLD_CENTER_X},${moldY + 15}`}
        fill={MOLD_WALL_COLOR}
        opacity={drawProgress * 0.4}
      />

      {/* Cavity detail lines */}
      {drawProgress > 0.6 && (
        <g opacity={(drawProgress - 0.6) * 0.5}>
          <line
            x1={moldX + 40}
            y1={moldY + moldH / 3}
            x2={moldX + moldW - 40}
            y2={moldY + moldH / 3}
            stroke={MOLD_WALL_COLOR}
            strokeWidth={1}
            strokeDasharray="4 6"
            opacity={0.15}
          />
          <line
            x1={moldX + 40}
            y1={moldY + (moldH * 2) / 3}
            x2={moldX + moldW - 40}
            y2={moldY + (moldH * 2) / 3}
            stroke={MOLD_WALL_COLOR}
            strokeWidth={1}
            strokeDasharray="4 6"
            opacity={0.15}
          />
        </g>
      )}
    </svg>
  );
};
