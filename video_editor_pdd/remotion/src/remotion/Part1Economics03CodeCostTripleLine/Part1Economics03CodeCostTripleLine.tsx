import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  BLUE_LINE,
  AMBER_LINE,
  GENERATE_COST_DATA,
  PATCH_COST_DATA,
  TOTAL_COST_DATA,
  MORPH_END,
  BLUE_LINE_START,
  BLUE_LINE_DUR,
  AMBER_SOLID_START,
  AMBER_SOLID_DUR,
  AMBER_DASH_START,
  AMBER_DASH_DUR,
} from "./constants";
import { ChartAxes } from "./ChartAxes";
import { MilestoneMarkers } from "./MilestoneMarkers";
import { AnimatedLine } from "./AnimatedLine";
import { DebtShadedArea } from "./DebtShadedArea";

export const defaultPart1Economics03CodeCostTripleLineProps = {};

/**
 * Triple-line chart showing code cost: generate vs patch vs total (with debt).
 * 1050 frames @ 30fps = 35 seconds.
 *
 * All sub-components use absolute frame numbers via useCurrentFrame()
 * from the composition root — no Sequence wrappers that would offset the frame.
 */
export const Part1Economics03CodeCostTripleLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Title opacity: visible from frame 0, ramps to full by morph end
  const titleOpacity = interpolate(frame, [0, MORPH_END], [0.8, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.ease),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* Chart title — visible from frame 0 */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: 0,
          right: 0,
          textAlign: "center",
          color: "#E2E8F0",
          fontSize: 28,
          fontWeight: 600,
          opacity: titleOpacity,
          letterSpacing: "-0.02em",
        }}
      >
        Code Cost: Generate vs Patch vs Total
      </div>

      {/* Subtitle */}
      <div
        style={{
          position: "absolute",
          top: 80,
          left: 0,
          right: 0,
          textAlign: "center",
          color: "#94A3B8",
          fontSize: 14,
          opacity: titleOpacity * 0.6,
        }}
      >
        Developer Hours per Feature Unit, 2015–2025
      </div>

      {/* Axes — present from frame 0 */}
      <ChartAxes />

      {/* Milestone markers — fade in from frame 30 (handled internally) */}
      <MilestoneMarkers />

      {/* Blue line: Cost to generate — draws from frame 60 */}
      <AnimatedLine
        data={GENERATE_COST_DATA}
        color={BLUE_LINE}
        strokeWidth={3}
        label="Cost to generate"
        labelOpacity={0.7}
        startFrame={BLUE_LINE_START}
        drawDuration={BLUE_LINE_DUR}
      />

      {/* Amber solid: Immediate patch cost — draws from frame 180 */}
      <AnimatedLine
        data={PATCH_COST_DATA}
        color={AMBER_LINE}
        strokeWidth={3}
        label="Immediate patch cost"
        labelOpacity={0.7}
        startFrame={AMBER_SOLID_START}
        drawDuration={AMBER_SOLID_DUR}
      />

      {/* Amber dashed: Total cost with debt — draws from frame 300 */}
      <AnimatedLine
        data={TOTAL_COST_DATA}
        color={AMBER_LINE}
        strokeWidth={2}
        label="Total cost (with debt)"
        labelOpacity={0.5}
        startFrame={AMBER_DASH_START}
        drawDuration={AMBER_DASH_DUR}
        dashArray="8 4"
      />

      {/* Debt shaded area — fills from frame 420 (handled internally) */}
      <DebtShadedArea />

      {/* Legend in top-right corner */}
      <Legend frame={frame} />
    </AbsoluteFill>
  );
};

/** Small legend box showing the three line types */
const Legend: React.FC<{ frame: number }> = ({ frame }) => {
  const blueOpacity = interpolate(
    frame,
    [BLUE_LINE_START, BLUE_LINE_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const amberSolidOpacity = interpolate(
    frame,
    [AMBER_SOLID_START, AMBER_SOLID_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const amberDashOpacity = interpolate(
    frame,
    [AMBER_DASH_START, AMBER_DASH_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const items = [
    {
      color: BLUE_LINE,
      label: "Cost to generate",
      opacity: blueOpacity,
      dashed: false,
    },
    {
      color: AMBER_LINE,
      label: "Immediate patch cost",
      opacity: amberSolidOpacity,
      dashed: false,
    },
    {
      color: AMBER_LINE,
      label: "Total cost (with debt)",
      opacity: amberDashOpacity,
      dashed: true,
    },
  ];

  return (
    <div
      style={{
        position: "absolute",
        top: 150,
        right: 40,
        display: "flex",
        flexDirection: "column",
        gap: 8,
      }}
    >
      {items.map((item) => (
        <div
          key={item.label}
          style={{
            display: "flex",
            alignItems: "center",
            gap: 8,
            opacity: item.opacity,
          }}
        >
          <svg width={28} height={4}>
            <line
              x1={0}
              y1={2}
              x2={28}
              y2={2}
              stroke={item.color}
              strokeWidth={item.dashed ? 2 : 3}
              strokeDasharray={item.dashed ? "6 3" : undefined}
            />
          </svg>
          <span
            style={{
              color: item.color,
              fontSize: 11,
              fontFamily: "Inter, sans-serif",
              opacity: 0.7,
            }}
          >
            {item.label}
          </span>
        </div>
      ))}
    </div>
  );
};

export default Part1Economics03CodeCostTripleLine;
