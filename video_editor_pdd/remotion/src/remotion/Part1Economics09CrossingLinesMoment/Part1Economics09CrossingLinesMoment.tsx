import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  AMBER_SOLID,
  AMBER_DASHED,
  BLUE_GENERATE,
  TOTAL_FRAMES,
  PATCH_COST_DATA,
  TOTAL_COST_DATA,
  GENERATE_COST_DATA,
  xToPixel,
  yToPixel,
  PHASE_CHART_IN,
  PHASE_CROSSING,
  PHASE_WE_ARE_HERE,
} from "./constants";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { ForkedLine } from "./ForkedLine";
import { CurvedArrow } from "./CurvedArrow";
import { CrossingPoint } from "./CrossingPoint";
import { Annotations } from "./Annotations";

export const defaultPart1Economics09CrossingLinesMomentProps = {};

/**
 * Section 1.8 — Crossing Lines Moment: Generation Beats Total Cost
 *
 * Triple-line chart with forked patch line, accumulation arrow,
 * and the "We are here." crossing-point moment.
 *
 * 750 frames @ 30fps = 25 seconds
 */
export const Part1Economics09CrossingLinesMoment: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall chart fade-in
  const chartOpacity = interpolate(
    frame,
    [PHASE_CHART_IN.start, PHASE_CHART_IN.end],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ─── Crossing point pixel coords ────────────────────────────────
  // The blue generation line crosses the solid amber (patch cost) line
  // around 2023-2024. We compute an approximate crossing near 2023.5
  // where generate cost ~3.5 meets the large-codebase-extended patch ~3.5
  // Actually, the blue line crosses the dashed total-cost line first (~2022)
  // then crosses below the solid patch line (~2024).
  // We place "We are here." at the second crossing (~2024, ~1.5h)
  const crossingX = xToPixel(2024);
  const crossingY = yToPixel(1.5);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: "Inter, sans-serif",
      }}
    >
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="Chart">
        {/* ─── Axes & Grid ─────────────────────────────────────── */}
        <ChartAxes />

        {/* ─── Original three lines (visible from frame 0) ─────── */}
        <div style={{ position: "absolute", inset: 0, opacity: chartOpacity }}>
          {/* Immediate patch cost — solid amber (pre-fork, 2015-2020) */}
          <AnimatedLine
            data={PATCH_COST_DATA}
            color={AMBER_SOLID}
            strokeWidth={2}
            drawStart={0}
            drawDuration={30}
            opacity={0.8}
          />

          {/* Total cost with debt — dashed amber */}
          <AnimatedLine
            data={TOTAL_COST_DATA}
            color={AMBER_DASHED}
            strokeWidth={2}
            dashed
            dashArray="6 4"
            drawStart={0}
            drawDuration={30}
            opacity={0.6}
          />

          {/* Generation cost — blue, draws with chart */}
          <AnimatedLine
            data={GENERATE_COST_DATA}
            color={BLUE_GENERATE}
            strokeWidth={3}
            drawStart={0}
            drawDuration={30}
            pulseAfterFrame={PHASE_CROSSING.start}
          />
        </div>

        {/* ─── Forked patch line (2020 fork) ───────────────────── */}
        <ForkedLine />

        {/* ─── Annotations (Same tools, METR, terminal) ────────── */}
        <Annotations />

        {/* ─── Accumulation arrow ──────────────────────────────── */}
        <CurvedArrow />

        {/* ─── "We are here." crossing point ───────────────────── */}
        <CrossingPoint cx={crossingX} cy={crossingY} />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics09CrossingLinesMoment;
