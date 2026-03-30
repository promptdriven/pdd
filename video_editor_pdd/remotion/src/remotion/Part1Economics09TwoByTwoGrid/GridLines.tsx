import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

/**
 * GridLines draws the 2×2 grid outline (border + center cross),
 * axis labels, and subtle gradient arrows.
 * Lines animate from 0-length to full-length during GRID_DRAW_START..GRID_DRAW_END.
 * Axis labels fade in during the same window.
 */

// ── Inline constants (avoid cross-file imports per requirement) ──
const GRID_SIZE = 600;
const GRID_CENTER_X = 960;
const GRID_CENTER_Y = 480;
const GRID_LEFT = GRID_CENTER_X - GRID_SIZE / 2;
const GRID_TOP = GRID_CENTER_Y - GRID_SIZE / 2;
const GRID_RIGHT = GRID_LEFT + GRID_SIZE;
const GRID_BOTTOM = GRID_TOP + GRID_SIZE;
const MID_X = GRID_CENTER_X;
const MID_Y = GRID_CENTER_Y;

const DIVIDER_COLOR = "#334155";
const DIVIDER_WIDTH = 2;
const AXIS_LABEL_COLOR = "#94A3B8";
const AXIS_LABEL_SIZE = 16;

const DRAW_START = 0;
const DRAW_END = 45;

const X_LABELS = ["Greenfield", "Brownfield"];
const Y_LABELS = ["In-Distribution", "Out-of-Distribution"];

export const GridLines: React.FC = () => {
  const frame = useCurrentFrame();

  // progress 0→1 over draw window
  const drawProgress = interpolate(frame, [DRAW_START, DRAW_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Label opacity fades in over draw window
  const labelOpacity = interpolate(
    frame,
    [DRAW_START, DRAW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Helpers for line drawing from center outward
  const hHalf = (GRID_SIZE / 2) * drawProgress;
  const vHalf = (GRID_SIZE / 2) * drawProgress;

  return (
    <>
      {/* ── SVG grid lines ── */}
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Outer border — drawn from center of each edge outward */}
        {/* Top edge */}
        <line
          x1={MID_X - hHalf}
          y1={GRID_TOP}
          x2={MID_X + hHalf}
          y2={GRID_TOP}
          stroke={DIVIDER_COLOR}
          strokeWidth={DIVIDER_WIDTH}
        />
        {/* Bottom edge */}
        <line
          x1={MID_X - hHalf}
          y1={GRID_BOTTOM}
          x2={MID_X + hHalf}
          y2={GRID_BOTTOM}
          stroke={DIVIDER_COLOR}
          strokeWidth={DIVIDER_WIDTH}
        />
        {/* Left edge */}
        <line
          x1={GRID_LEFT}
          y1={MID_Y - vHalf}
          x2={GRID_LEFT}
          y2={MID_Y + vHalf}
          stroke={DIVIDER_COLOR}
          strokeWidth={DIVIDER_WIDTH}
        />
        {/* Right edge */}
        <line
          x1={GRID_RIGHT}
          y1={MID_Y - vHalf}
          x2={GRID_RIGHT}
          y2={MID_Y + vHalf}
          stroke={DIVIDER_COLOR}
          strokeWidth={DIVIDER_WIDTH}
        />

        {/* Horizontal center divider */}
        <line
          x1={MID_X - hHalf}
          y1={MID_Y}
          x2={MID_X + hHalf}
          y2={MID_Y}
          stroke={DIVIDER_COLOR}
          strokeWidth={DIVIDER_WIDTH}
        />
        {/* Vertical center divider */}
        <line
          x1={MID_X}
          y1={MID_Y - vHalf}
          x2={MID_X}
          y2={MID_Y + vHalf}
          stroke={DIVIDER_COLOR}
          strokeWidth={DIVIDER_WIDTH}
        />

        {/* ── Axis arrows (subtle gradient) ── */}
        <defs>
          <linearGradient id="arrowGradH" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor={AXIS_LABEL_COLOR} stopOpacity={0} />
            <stop offset="100%" stopColor={AXIS_LABEL_COLOR} stopOpacity={0.5} />
          </linearGradient>
          <linearGradient id="arrowGradV" x1="0%" y1="0%" x2="0%" y2="100%">
            <stop offset="0%" stopColor={AXIS_LABEL_COLOR} stopOpacity={0} />
            <stop offset="100%" stopColor={AXIS_LABEL_COLOR} stopOpacity={0.5} />
          </linearGradient>
          <marker
            id="arrowHeadH"
            markerWidth="8"
            markerHeight="6"
            refX="8"
            refY="3"
            orient="auto"
          >
            <path d="M0,0 L8,3 L0,6" fill={AXIS_LABEL_COLOR} opacity={0.4} />
          </marker>
          <marker
            id="arrowHeadV"
            markerWidth="8"
            markerHeight="6"
            refX="8"
            refY="3"
            orient="auto"
          >
            <path d="M0,0 L8,3 L0,6" fill={AXIS_LABEL_COLOR} opacity={0.4} />
          </marker>
        </defs>

        {/* Horizontal axis arrow (below grid) */}
        <line
          x1={GRID_LEFT}
          y1={GRID_BOTTOM + 30}
          x2={GRID_RIGHT}
          y2={GRID_BOTTOM + 30}
          stroke="url(#arrowGradH)"
          strokeWidth={1.5}
          markerEnd="url(#arrowHeadH)"
          opacity={labelOpacity}
        />

        {/* Vertical axis arrow (left of grid) */}
        <line
          x1={GRID_LEFT - 30}
          y1={GRID_TOP}
          x2={GRID_LEFT - 30}
          y2={GRID_BOTTOM}
          stroke="url(#arrowGradV)"
          strokeWidth={1.5}
          markerEnd="url(#arrowHeadV)"
          opacity={labelOpacity}
        />
      </svg>

      {/* ── X-axis labels ── */}
      {/* "Greenfield" — left side */}
      <div
        style={{
          position: "absolute",
          left: GRID_LEFT,
          top: GRID_BOTTOM + 42,
          width: GRID_SIZE / 2,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: AXIS_LABEL_SIZE,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: labelOpacity,
        }}
      >
        {X_LABELS[0]}
      </div>
      {/* "Brownfield" — right side */}
      <div
        style={{
          position: "absolute",
          left: MID_X,
          top: GRID_BOTTOM + 42,
          width: GRID_SIZE / 2,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: AXIS_LABEL_SIZE,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: labelOpacity,
        }}
      >
        {X_LABELS[1]}
      </div>

      {/* ── Y-axis labels ── */}
      {/* "In-Distribution" — top */}
      <div
        style={{
          position: "absolute",
          right: 1920 - GRID_LEFT + 16,
          top: GRID_TOP,
          height: GRID_SIZE / 2,
          display: "flex",
          alignItems: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: AXIS_LABEL_SIZE,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: labelOpacity,
          writingMode: "vertical-rl",
          textOrientation: "mixed",
          transform: "rotate(180deg)",
        }}
      >
        {Y_LABELS[0]}
      </div>
      {/* "Out-of-Distribution" — bottom */}
      <div
        style={{
          position: "absolute",
          right: 1920 - GRID_LEFT + 16,
          top: MID_Y,
          height: GRID_SIZE / 2,
          display: "flex",
          alignItems: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: AXIS_LABEL_SIZE,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: labelOpacity,
          writingMode: "vertical-rl",
          textOrientation: "mixed",
          transform: "rotate(180deg)",
        }}
      >
        {Y_LABELS[1]}
      </div>
    </>
  );
};

export default GridLines;
