import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  SPLIT_X,
  SPLIT_LINE_COLOR,
  SPLIT_LINE_OPACITY,
  SPLIT_LINE_WIDTH,
  AMBER,
  BLUE,
  FONT_UI,
  PANEL_WIDTH,
  SPLIT_LINE_START,
  SPLIT_LINE_END,
  HEADER_START,
  HEADER_END,
} from "./constants";
import { LeftPanel } from "./LeftPanel";
import { RightPanel } from "./RightPanel";

export const defaultPart1Economics07SplitContextComparisonProps = {};

export const Part1Economics07SplitContextComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Split line fade in
  const splitLineOpacity = interpolate(
    frame,
    [SPLIT_LINE_START, SPLIT_LINE_END],
    [0, SPLIT_LINE_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Header fade in
  const headerOpacity = interpolate(
    frame,
    [HEADER_START, HEADER_END],
    [0, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Split divider line */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X - SPLIT_LINE_WIDTH / 2,
          top: 0,
          width: SPLIT_LINE_WIDTH,
          height: "100%",
          backgroundColor: SPLIT_LINE_COLOR,
          opacity: splitLineOpacity,
        }}
      />

      {/* Left panel header */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 50,
          width: PANEL_WIDTH,
          textAlign: "center",
          fontFamily: FONT_UI,
          fontSize: 14,
          fontWeight: 600,
          color: AMBER,
          opacity: headerOpacity,
          letterSpacing: 2,
          textTransform: "uppercase",
        }}
      >
        Agentic Patching
      </div>

      {/* Right panel header */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X + 2,
          top: 50,
          width: PANEL_WIDTH,
          textAlign: "center",
          fontFamily: FONT_UI,
          fontSize: 14,
          fontWeight: 600,
          color: BLUE,
          opacity: headerOpacity,
          letterSpacing: 2,
          textTransform: "uppercase",
        }}
      >
        PDD Regeneration
      </div>

      {/* Left panel — Agentic Patching */}
      <LeftPanel />

      {/* Right panel — PDD Regeneration */}
      <RightPanel />
    </AbsoluteFill>
  );
};

export default Part1Economics07SplitContextComparison;
