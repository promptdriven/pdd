import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  Sequence,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  BLUE_LINE_COLOR,
  AMBER_SOLID_COLOR,
  AMBER_DASHED_COLOR,
  TOTAL_FRAMES,
  CHART_LEFT,
  CHART_RIGHT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN_YEAR,
  X_MAX_YEAR,
  Y_MAX,
  TOTAL_COST_DEBT_Y,
  IMMEDIATE_PATCH_Y,
  GENERATE_LINE_POINTS,
  CROSSING1_YEAR,
  CROSSING1_Y,
  CROSSING2_YEAR,
  CROSSING2_Y,
  BLUE_LINE_STROKE_WIDTH,
  AMBER_LINE_STROKE_WIDTH,
  FLASH1_RADIUS,
  FLASH2_RADIUS,
  FLASH1_FRAME,
  FLASH2_FRAME,
  PHASE_ESTABLISH_END,
  PHASE_CROSS1_START,
  PHASE_CROSS1_END,
  PHASE_CROSS2_START,
  PHASE_CROSS2_END,
  PHASE_LABEL_START,
} from "./constants";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { RadialFlash } from "./RadialFlash";
import { WeAreHereLabel } from "./WeAreHereLabel";
import { ChartLegend } from "./ChartLegend";

// ── Coordinate helpers ──────────────────────────────────────────────

function yearToX(year: number): number {
  return CHART_LEFT + ((year - X_MIN_YEAR) / (X_MAX_YEAR - X_MIN_YEAR)) * CHART_WIDTH;
}

function costToY(cost: number): number {
  return CHART_BOTTOM - (cost / Y_MAX) * CHART_HEIGHT;
}

// ── Amber line data ─────────────────────────────────────────────────

const TOTAL_COST_LINE: [number, number][] = [
  [X_MIN_YEAR, TOTAL_COST_DEBT_Y],
  [X_MAX_YEAR, TOTAL_COST_DEBT_Y + 5], // slight upward drift for realism
];

const IMMEDIATE_PATCH_LINE: [number, number][] = [
  [X_MIN_YEAR, IMMEDIATE_PATCH_Y],
  [X_MAX_YEAR, IMMEDIATE_PATCH_Y + 3], // slight upward drift
];

// ── Compute crossing points in pixel space ──────────────────────────

const crossing1Px = { x: yearToX(CROSSING1_YEAR), y: costToY(CROSSING1_Y) };
const crossing2Px = { x: yearToX(CROSSING2_YEAR), y: costToY(CROSSING2_Y) };

// ── Blue line reveal computation ────────────────────────────────────
// The blue line has GENERATE_LINE_POINTS.length points.
// We reveal them progressively:
//   Frame 0-60:   show points 0..5 (years 2020..2024.8 — above amber lines)
//   Frame 60-120: reveal points 5..7 (crossing total_cost_debt)
//   Frame 120-180: reveal points 7..9 (crossing immediate_patch, final)

const INITIAL_POINTS = 6; // points visible at frame 0 (indices 0..5)
const CROSS1_POINTS = 7; // through first crossing zone
const CROSS2_POINTS = GENERATE_LINE_POINTS.length; // all points

function getBlueRevealCount(frame: number): number {
  if (frame <= PHASE_ESTABLISH_END) {
    // Establish phase: show initial points
    return INITIAL_POINTS;
  }
  if (frame <= PHASE_CROSS1_END) {
    // First crossing: reveal to point 7
    const progress = interpolate(
      frame,
      [PHASE_CROSS1_START, PHASE_CROSS1_END],
      [INITIAL_POINTS, CROSS1_POINTS],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.in(Easing.quad),
      }
    );
    return progress;
  }
  if (frame <= PHASE_CROSS2_END) {
    // Second crossing: reveal remaining
    const progress = interpolate(
      frame,
      [PHASE_CROSS2_START, PHASE_CROSS2_END],
      [CROSS1_POINTS, CROSS2_POINTS],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.in(Easing.quad),
      }
    );
    return progress;
  }
  return CROSS2_POINTS;
}

// ── Main component ──────────────────────────────────────────────────

export const defaultPart1Economics13CrossingLinesMomentProps = {};

export const Part1Economics13CrossingLinesMoment: React.FC = () => {
  const frame = useCurrentFrame();

  const blueRevealCount = getBlueRevealCount(frame);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Chart axes & grid — visible from frame 0 */}
      <ChartAxes />

      {/* Legend */}
      <ChartLegend x={CHART_RIGHT - 320} y={CHART_BOTTOM + 50} />

      {/* Amber dashed line: Total cost with tech debt — fully visible from frame 0 */}
      <AnimatedLine
        points={TOTAL_COST_LINE}
        color={AMBER_DASHED_COLOR}
        strokeWidth={AMBER_LINE_STROKE_WIDTH}
        revealCount={TOTAL_COST_LINE.length}
        dashArray="10 6"
        opacity={0.85}
      />

      {/* Amber solid line: Immediate patch cost — fully visible from frame 0 */}
      <AnimatedLine
        points={IMMEDIATE_PATCH_LINE}
        color={AMBER_SOLID_COLOR}
        strokeWidth={AMBER_LINE_STROKE_WIDTH}
        revealCount={IMMEDIATE_PATCH_LINE.length}
        opacity={0.85}
      />

      {/* Blue "cost to generate" line — animates progressively */}
      <AnimatedLine
        points={GENERATE_LINE_POINTS}
        color={BLUE_LINE_COLOR}
        strokeWidth={BLUE_LINE_STROKE_WIDTH}
        revealCount={blueRevealCount}
      />

      {/* Radial flash at first crossing point */}
      <RadialFlash
        cx={crossing1Px.x}
        cy={crossing1Px.y}
        radius={FLASH1_RADIUS}
        triggerFrame={FLASH1_FRAME}
        duration={20}
      />

      {/* Radial flash at second crossing point */}
      <RadialFlash
        cx={crossing2Px.x}
        cy={crossing2Px.y}
        radius={FLASH2_RADIUS}
        triggerFrame={FLASH2_FRAME}
        duration={20}
      />

      {/* "We are here." label — appears at frame 180 */}
      <Sequence from={PHASE_LABEL_START} durationInFrames={TOTAL_FRAMES - PHASE_LABEL_START}>
        <WeAreHereLabel
          targetX={crossing2Px.x}
          targetY={crossing2Px.y}
          labelOffsetX={60}
          labelOffsetY={55}
        />
      </Sequence>

      {/* Amber line labels — visible from frame 0 */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        {/* Label for dashed amber line */}
        <text
          x={CHART_RIGHT + 10}
          y={costToY(TOTAL_COST_DEBT_Y + 2.5) + 5}
          fill={AMBER_DASHED_COLOR}
          fontFamily="Inter, system-ui, sans-serif"
          fontSize={14}
          fontWeight={500}
          opacity={0.9}
        >
          Total cost
        </text>
        <text
          x={CHART_RIGHT + 10}
          y={costToY(TOTAL_COST_DEBT_Y + 2.5) + 20}
          fill={AMBER_DASHED_COLOR}
          fontFamily="Inter, system-ui, sans-serif"
          fontSize={12}
          fontWeight={400}
          opacity={0.7}
        >
          (with debt)
        </text>

        {/* Label for solid amber line */}
        <text
          x={CHART_RIGHT + 10}
          y={costToY(IMMEDIATE_PATCH_Y + 1.5) + 5}
          fill={AMBER_SOLID_COLOR}
          fontFamily="Inter, system-ui, sans-serif"
          fontSize={14}
          fontWeight={500}
          opacity={0.9}
        >
          Patch cost
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default Part1Economics13CrossingLinesMoment;
