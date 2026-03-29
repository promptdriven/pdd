import React from "react";
import { AbsoluteFill, Sequence, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  BG_COLOR,
  LABOR_COST_DATA,
  GARMENT_COST_DATA,
  LABOR_LINE_COLOR,
  GARMENT_LINE_COLOR,
  LINE_STROKE_WIDTH,
  TOTAL_FRAMES,
  FONT_FAMILY,
  THRESHOLD_LABEL_COLOR,
  MORPH_START,
  MORPH_END,
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
} from "./constants";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { CrossingHighlight } from "./CrossingHighlight";
import { LineLegend } from "./LineLegend";

export const defaultPart1Economics02SockPriceChartProps = {};

/**
 * Section 1.2: Sock Price vs. Labor Cost Chart
 *
 * An animated line chart showing the economic threshold that killed darning.
 * Two lines (labor cost in amber, garment cost in blue) cross around 1962,
 * marking "The Threshold" where darning became irrational.
 *
 * Duration: 720 frames (24s @ 30fps)
 */
export const Part1Economics02SockPriceChart: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Title that appears at the very start ──
  const titleOpacity = interpolate(frame, [0, 15], [0.8, 0.8], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const titleFadeOut = interpolate(frame, [50, 80], [1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Morph-phase overlay ──
  const morphProgress = interpolate(frame, [MORPH_START, MORPH_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* ── Chart axes and grid (always present from frame 0) ── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ChartAxes />
      </Sequence>

      {/* ── Animated data lines ── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Labor cost line (amber) — fades out in morph phase */}
        <AnimatedLine
          data={LABOR_COST_DATA}
          color={LABOR_LINE_COLOR}
          strokeWidth={LINE_STROKE_WIDTH}
          fadeOutOnMorph
        />
        {/* Garment cost line (blue) — persists through morph */}
        <AnimatedLine
          data={GARMENT_COST_DATA}
          color={GARMENT_LINE_COLOR}
          strokeWidth={LINE_STROKE_WIDTH}
          fadeOutOnMorph={false}
        />
      </Sequence>

      {/* ── Crossing highlight + zone labels ── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <CrossingHighlight />
      </Sequence>

      {/* ── Legend ── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <LineLegend />
      </Sequence>

      {/* ── Opening title overlay ── */}
      <div
        style={{
          position: "absolute",
          top: CHART_TOP - 60,
          left: CHART_LEFT,
          right: 1920 - CHART_RIGHT,
          display: "flex",
          justifyContent: "center",
          opacity: titleOpacity * titleFadeOut,
          pointerEvents: "none",
        }}
      >
        <span
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 24,
            fontWeight: 600,
            color: THRESHOLD_LABEL_COLOR,
            letterSpacing: "0.05em",
          }}
        >
          Sock Price vs. Labor Cost
        </span>
      </div>

      {/* ── Morph-phase vignette/darken ── */}
      {morphProgress > 0 && (
        <AbsoluteFill
          style={{
            backgroundColor: BG_COLOR,
            opacity: morphProgress * 0.4,
            pointerEvents: "none",
          }}
        />
      )}
    </AbsoluteFill>
  );
};

export default Part1Economics02SockPriceChart;
