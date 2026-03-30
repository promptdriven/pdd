import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";

import { GridLines } from "./GridLines";
import { QuadrantFill } from "./QuadrantFill";

// ── Constants (inlined from constants.ts for reference, but using imports
//    would violate the "only import from remotion" rule — however the spec
//    says sub-components ARE allowed. We import our own sub-components.) ──

const BG_COLOR = "#0A0F1A";

// Grid geometry
const GRID_SIZE = 600;
const CELL_SIZE = 300;
const GRID_CENTER_X = 960;
const GRID_CENTER_Y = 480;
const GRID_LEFT = GRID_CENTER_X - GRID_SIZE / 2;
const GRID_TOP = GRID_CENTER_Y - GRID_SIZE / 2;

// Quadrant colors
const GREEN_QUADRANT = "#5AAA6E";
const RED_QUADRANT = "#EF4444";
const NEUTRAL_FILL = "#64748B";
const NEUTRAL_FILL_OPACITY = 0.06;

// Timing
const TOTAL_FRAMES = 630;
const GREEN_START = 45;
const RED_START = 150;
const INSIGHT_START = 390;
const INSIGHT_FADE_FRAMES = 30;

// Insight
const INSIGHT_TEXT =
  "Every study is correct. They just measured different quadrants.";
const INSIGHT_TEXT_COLOR = "#E2E8F0";
const INSIGHT_TEXT_SIZE = 16;
const INSIGHT_Y = 830;

// ── Default props ──
export const defaultPart1Economics09TwoByTwoGridProps = {};

// ── Main component ──
export const Part1Economics09TwoByTwoGrid: React.FC = () => {
  const frame = useCurrentFrame();

  // Insight text opacity
  const insightOpacity = interpolate(
    frame,
    [INSIGHT_START, INSIGHT_START + INSIGHT_FADE_FRAMES],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Neutral quadrant fill opacity (appears with grid)
  const neutralOpacity = interpolate(frame, [0, 45], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
        overflow: "hidden",
      }}
    >
      {/* ── Section title — visible from frame 0 ── */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 0,
          width: 1920,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 28,
          fontWeight: 600,
          color: "#E2E8F0",
          letterSpacing: "-0.02em",
        }}
      >
        Reconciling the Studies
      </div>

      {/* ── Neutral quadrant fills (top-right and bottom-left) ── */}
      {/* Top-right */}
      <div
        style={{
          position: "absolute",
          left: GRID_LEFT + CELL_SIZE,
          top: GRID_TOP,
          width: CELL_SIZE,
          height: CELL_SIZE,
          backgroundColor: NEUTRAL_FILL,
          opacity: NEUTRAL_FILL_OPACITY * neutralOpacity,
        }}
      />
      {/* Bottom-left */}
      <div
        style={{
          position: "absolute",
          left: GRID_LEFT,
          top: GRID_TOP + CELL_SIZE,
          width: CELL_SIZE,
          height: CELL_SIZE,
          backgroundColor: NEUTRAL_FILL,
          opacity: NEUTRAL_FILL_OPACITY * neutralOpacity,
        }}
      />

      {/* ── Grid lines + axis labels ── */}
      <GridLines />

      {/* ── Green quadrant (top-left): appears at frame 45 ── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <QuadrantFill
          position="top-left"
          color={GREEN_QUADRANT}
          fillOpacity={0.15}
          glowOpacity={0.3}
          label="GitHub study: +55%"
          labelColor={GREEN_QUADRANT}
          labelSize={20}
          animStartFrame={GREEN_START}
        />
      </Sequence>

      {/* ── Red quadrant (bottom-right): appears at frame 150 ── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <QuadrantFill
          position="bottom-right"
          color={RED_QUADRANT}
          fillOpacity={0.15}
          glowOpacity={0.3}
          label={`METR study: \u221219%`}
          labelColor={RED_QUADRANT}
          labelSize={20}
          animStartFrame={RED_START}
        />
      </Sequence>

      {/* ── Key insight text ── */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: INSIGHT_Y,
          width: 1920,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: INSIGHT_TEXT_SIZE,
          fontWeight: 400,
          color: INSIGHT_TEXT_COLOR,
          opacity: insightOpacity,
          padding: "0 200px",
          lineHeight: 1.5,
        }}
      >
        {INSIGHT_TEXT}
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics09TwoByTwoGrid;
