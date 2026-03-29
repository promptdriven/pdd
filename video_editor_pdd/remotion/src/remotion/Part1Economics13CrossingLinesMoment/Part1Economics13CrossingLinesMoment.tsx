// Part1Economics13CrossingLinesMoment.tsx
// The "We Are Here" crossing-lines chart — generate cost plunges below both
// amber cost lines, marking the threshold where regeneration beats patching.
//
// Duration: 360 frames (12s @ 30fps)
// Phases:
//   0-60    Chart establishes; blue line visible up to ~2025
//   60-120  Blue line descends, crosses dashed amber (total cost w/ debt)
//   120-180 Blue line crosses solid amber (immediate patch cost)
//   180-240 "We are here." label fades in
//   240-360 Hold — deliberate stillness

import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";

import {
  BACKGROUND_COLOR,
  BLUE_LINE_COLOR,
  AMBER_SOLID_COLOR,
  AMBER_DASHED_COLOR,
  TOTAL_COST_DEBT_POINTS,
  IMMEDIATE_PATCH_POINTS,
  GENERATE_COST_POINTS,
  GENERATE_DESCENT_POINTS,
  GENERATE_VISIBLE_BEFORE_INDEX,
  CROSSING_1_X,
  CROSSING_1_Y,
  CROSSING_2_X,
  CROSSING_2_Y,
  FLASH_1_FRAME,
  FLASH_2_FRAME,
  FLASH_DURATION,
  PHASE_ESTABLISH_END,
  FONT_FAMILY,
  AXIS_LABEL_COLOR,
} from "./constants";

import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { RadialFlash } from "./RadialFlash";
import { WeAreHereLabel } from "./WeAreHereLabel";

export const defaultPart1Economics13CrossingLinesMomentProps = {};

export const Part1Economics13CrossingLinesMoment: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Legend Opacity ─────────────────────────────────────────────────
  // Fade legend in during first 30 frames
  const legendOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: "hidden",
      }}
    >
      {/* ── Chart Axes & Grid ──────────────────────────────────────── */}
      <ChartAxes />

      {/* ── Amber Dashed Line: Total Cost with Debt ────────────────── */}
      {/* Visible from frame 0, drawn instantly */}
      <AnimatedLine
        points={TOTAL_COST_DEBT_POINTS}
        color={AMBER_DASHED_COLOR}
        strokeWidth={2.5}
        dashed
        drawStartFrame={0}
        drawDuration={40}
        easeInDraw={false}
      />

      {/* ── Amber Solid Line: Immediate Patch Cost ─────────────────── */}
      {/* Visible from frame 0, drawn instantly */}
      <AnimatedLine
        points={IMMEDIATE_PATCH_POINTS}
        color={AMBER_SOLID_COLOR}
        strokeWidth={2.5}
        drawStartFrame={0}
        drawDuration={40}
        easeInDraw={false}
      />

      {/* ── Blue Line: Pre-crossing portion (up to ~2025) ──────────── */}
      {/* Already visible at frame 0 (establishing shot) */}
      <AnimatedLine
        points={GENERATE_COST_POINTS}
        color={BLUE_LINE_COLOR}
        strokeWidth={3}
        drawStartFrame={0}
        drawDuration={40}
        easeInDraw={false}
        staticPointCount={GENERATE_VISIBLE_BEFORE_INDEX + 1}
      />

      {/* ── Blue Line: Descent through both crossings ──────────────── */}
      {/* Draws from frame 60 to 180 (2 seconds per crossing phase) */}
      <AnimatedLine
        points={GENERATE_DESCENT_POINTS}
        color={BLUE_LINE_COLOR}
        strokeWidth={3}
        drawStartFrame={PHASE_ESTABLISH_END}
        drawDuration={120}
        easeInDraw
      />

      {/* ── Crossing Flash 1 (total cost debt) ─────────────────────── */}
      <RadialFlash
        cx={CROSSING_1_X}
        cy={CROSSING_1_Y}
        maxRadius={30}
        startFrame={FLASH_1_FRAME}
        duration={FLASH_DURATION}
      />

      {/* ── Crossing Flash 2 (immediate patch) ─────────────────────── */}
      <RadialFlash
        cx={CROSSING_2_X}
        cy={CROSSING_2_Y}
        maxRadius={22}
        startFrame={FLASH_2_FRAME}
        duration={FLASH_DURATION}
      />

      {/* ── "We are here." Label ───────────────────────────────────── */}
      <WeAreHereLabel />

      {/* ── Legend ──────────────────────────────────────────────────── */}
      <div
        style={{
          position: "absolute",
          top: 40,
          right: 80,
          display: "flex",
          flexDirection: "column",
          gap: 12,
          opacity: legendOpacity,
        }}
      >
        <LegendItem
          color={BLUE_LINE_COLOR}
          label="Cost to Generate"
          dashed={false}
        />
        <LegendItem
          color={AMBER_DASHED_COLOR}
          label="Total Cost (with debt)"
          dashed
        />
        <LegendItem
          color={AMBER_SOLID_COLOR}
          label="Immediate Patch Cost"
          dashed={false}
        />
      </div>
    </AbsoluteFill>
  );
};

// ── Legend Item ──────────────────────────────────────────────────────
interface LegendItemProps {
  color: string;
  label: string;
  dashed: boolean;
}

const LegendItem: React.FC<LegendItemProps> = ({ color, label, dashed }) => (
  <div style={{ display: "flex", alignItems: "center", gap: 10 }}>
    <svg width={36} height={4}>
      <line
        x1={0}
        y1={2}
        x2={36}
        y2={2}
        stroke={color}
        strokeWidth={2.5}
        strokeDasharray={dashed ? "6 4" : "none"}
      />
    </svg>
    <span
      style={{
        fontFamily: FONT_FAMILY,
        fontSize: 16,
        color: AXIS_LABEL_COLOR,
        fontWeight: 500,
      }}
    >
      {label}
    </span>
  </div>
);

export default Part1Economics13CrossingLinesMoment;
