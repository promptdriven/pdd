import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { QuadrantGrid } from "./QuadrantGrid";
import { QuadrantContent } from "./QuadrantContent";
import { EnterpriseCircle } from "./EnterpriseCircle";
import {
  WIDTH,
  HEIGHT,
  BG_COLOR,
  SUMMARY_COLOR,
  FONT_FAMILY,
  SUMMARY_FADE_START,
  SUMMARY_FADE_END,
  CIRCLE_DRAW_START,
} from "./constants";

export const defaultPart1Economics06TwoByTwoGridProps = {};

export const Part1Economics06TwoByTwoGrid: React.FC = () => {
  const frame = useCurrentFrame();

  // Summary line fade-in
  const summaryOpacity = interpolate(
    frame,
    [SUMMARY_FADE_START, SUMMARY_FADE_END],
    [0, 0.7],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Enterprise circle visibility gate
  const showCircle = frame >= CIRCLE_DRAW_START;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Quadrant background fills and study labels */}
        <QuadrantContent />

        {/* Enterprise work dotted circle */}
        {showCircle && <EnterpriseCircle />}

        {/* Summary line */}
        <text
          x={WIDTH / 2}
          y={880}
          fill={SUMMARY_COLOR}
          fontSize={16}
          fontFamily={FONT_FAMILY}
          fontWeight={400}
          opacity={summaryOpacity}
          textAnchor="middle"
          dominantBaseline="middle"
        >
          Every study is correct. They just measured different quadrants.
        </text>
      </svg>

      {/* Grid lines and axis labels (rendered as separate SVG layer on top) */}
      <QuadrantGrid />
    </AbsoluteFill>
  );
};

export default Part1Economics06TwoByTwoGrid;
