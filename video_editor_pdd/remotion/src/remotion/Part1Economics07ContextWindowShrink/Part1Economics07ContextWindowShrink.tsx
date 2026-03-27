import React from "react";
import { AbsoluteFill, Sequence, useCurrentFrame, interpolate, Easing } from "remotion";
import { BG_COLOR, TOTAL_FRAMES, MISMATCH_START_FRAME } from "./constants";
import { CodeBlockGrid } from "./CodeBlockGrid";
import { ContextWindowOverlay } from "./ContextWindowOverlay";
import { CoverageCounter } from "./CoverageCounter";
import { MismatchHighlights } from "./MismatchHighlights";

export const defaultPart1Economics07ContextWindowShrinkProps = {};

/**
 * Section 1.7: Context Window Shrink — Codebase Growth vs. Fixed Window
 *
 * Visualizes how a fixed-size AI context window covers less and less
 * of a growing codebase: 80% → 40% → 10% → 2%.
 *
 * Phase 1 (0-180): Small 4×4 grid, 80% coverage — AI sees almost everything
 * Phase 2 (180-540): Grid grows through 8×8, 16×16, 32×32 — window stays fixed
 * Phase 3 (720-1560): Red/green mismatch highlights — irrelevant code grabbed,
 *                      needed code missed
 */
export const Part1Economics07ContextWindowShrink: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Title label — visible from frame 0 */}
      <div
        style={{
          position: "absolute",
          left: 80,
          top: 60,
          fontFamily: "Inter, sans-serif",
          fontSize: 22,
          fontWeight: 600,
          color: "#E2E8F0",
          opacity: 0.9,
          letterSpacing: 0.5,
        }}
      >
        Codebase Growth vs. Fixed Context Window
      </div>

      {/* Growing code grid */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <CodeBlockGrid />
      </Sequence>

      {/* Fixed-size context window overlay */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ContextWindowOverlay />
      </Sequence>

      {/* Coverage counter (top-right) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <CoverageCounter />
      </Sequence>

      {/* Red/green mismatch highlights — Phase 3 */}
      <Sequence from={MISMATCH_START_FRAME} durationInFrames={TOTAL_FRAMES - MISMATCH_START_FRAME}>
        <MismatchHighlights />
      </Sequence>

      {/* Legend for Phase 3 highlights */}
      <Sequence from={MISMATCH_START_FRAME} durationInFrames={TOTAL_FRAMES - MISMATCH_START_FRAME}>
        <MismatchLegend />
      </Sequence>
    </AbsoluteFill>
  );
};

/**
 * Small legend in the bottom-right showing what red/green highlights mean.
 */
const MismatchLegend: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 30], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        right: 80,
        bottom: 80,
        opacity,
        display: "flex",
        flexDirection: "column",
        gap: 10,
      }}
    >
      <LegendItem color="#EF4444" label="Irrelevant code grabbed" />
      <LegendItem color="#5AAA6E" label="Needed code missed" />
    </div>
  );
};

const LegendItem: React.FC<{ color: string; label: string }> = ({ color, label }) => (
  <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
    <div
      style={{
        width: 14,
        height: 14,
        backgroundColor: color,
        borderRadius: 2,
        opacity: 0.6,
      }}
    />
    <span
      style={{
        fontFamily: "Inter, sans-serif",
        fontSize: 14,
        fontWeight: 500,
        color: "#CBD5E1",
      }}
    >
      {label}
    </span>
  </div>
);

export default Part1Economics07ContextWindowShrink;
