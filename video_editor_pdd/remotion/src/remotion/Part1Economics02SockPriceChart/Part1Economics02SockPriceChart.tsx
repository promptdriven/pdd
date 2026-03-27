import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate } from "remotion";
import "../_shared/load-inter-font";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { CrossingHighlight } from "./CrossingHighlight";
import {
  BG_COLOR,
  LABOR_COST_DATA,
  GARMENT_COST_DATA,
  LABOR_LINE_COLOR,
  GARMENT_LINE_COLOR,
  CHART_TOP,
  CHART_RIGHT,
  MORPH_START,
  MORPH_END,
} from "./constants";

export const defaultPart1Economics02SockPriceChartProps = {};

/**
 * Section 1.2: Sock Price vs. Labor Cost Chart
 *
 * An animated line chart showing the economic threshold that killed darning.
 * Two lines cross around 1962 — "The Threshold" where darning became irrational.
 */
export const Part1Economics02SockPriceChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Legend opacity — visible after axes draw in (frame 20+)
  const legendOpacity = interpolate(frame, [20, 35], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Overall chart opacity during morph (subtle)
  const morphOverlayOpacity = interpolate(
    frame,
    [MORPH_START + 60, MORPH_END],
    [0, 0.3],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* Chart axes and grid */}
      <ChartAxes />

      {/* Animated lines — both start drawing from frame 30 */}
      <AnimatedLine
        data={LABOR_COST_DATA}
        color={LABOR_LINE_COLOR}
        strokeWidth={3}
        fadeOutStart={MORPH_START}
        fadeOutEnd={MORPH_END}
      />
      <AnimatedLine
        data={GARMENT_COST_DATA}
        color={GARMENT_LINE_COLOR}
        strokeWidth={3}
      />

      {/* Crossing point highlight + zone labels */}
      <CrossingHighlight />

      {/* Legend — top right */}
      <div
        style={{
          position: "absolute",
          top: CHART_TOP + 10,
          right: 1920 - CHART_RIGHT + 20,
          opacity: legendOpacity,
          display: "flex",
          flexDirection: "column",
          gap: 10,
        }}
      >
        <LegendItem color={LABOR_LINE_COLOR} label="Labor cost" />
        <LegendItem color={GARMENT_LINE_COLOR} label="Garment cost (relative)" />
      </div>

      {/* Morph overlay — gentle fade at end */}
      {frame >= MORPH_START && (
        <AbsoluteFill
          style={{
            backgroundColor: BG_COLOR,
            opacity: morphOverlayOpacity,
            pointerEvents: "none",
          }}
        />
      )}
    </AbsoluteFill>
  );
};

const LegendItem: React.FC<{ color: string; label: string }> = ({
  color,
  label,
}) => (
  <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
    <div
      style={{
        width: 24,
        height: 3,
        backgroundColor: color,
        borderRadius: 2,
      }}
    />
    <span
      style={{
        fontFamily: "Inter, sans-serif",
        fontSize: 14,
        fontWeight: 400,
        color: "#94A3B8",
        opacity: 0.8,
      }}
    >
      {label}
    </span>
  </div>
);

export default Part1Economics02SockPriceChart;
