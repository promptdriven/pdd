import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { AnimatedArea } from "./AnimatedArea";
import {
  COLORS,
  CHART_DATA,
  BEATS,
  CodeCostChartPropsType,
} from "./constants";

export const CodeCostChart: React.FC<CodeCostChartPropsType> = ({
  showTitle = true,
}) => {
  const frame = useCurrentFrame();

  // Title morph animation: fade out old title, fade in new title
  const oldTitleOpacity = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_START + 45],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const newTitleOpacity = interpolate(
    frame,
    [BEATS.MORPH_START + 45, BEATS.MORPH_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Split the data for the two-phase animation
  // Phase 1 (frame 150-360): Draw from 1970 to 2020
  // Phase 2 (frame 360-480): Draw from 2020 to 2024 (dramatic changes)
  const costToGeneratePhase1 = CHART_DATA.costToGenerate.filter(d => d.year <= 2020);
  const costToGeneratePhase2 = CHART_DATA.costToGenerate.filter(d => d.year >= 2020);

  const immediateCostPhase1 = CHART_DATA.immediateCostToPatch.filter(d => d.year <= 2020);
  const immediateCostPhase2 = CHART_DATA.immediateCostToPatch.filter(d => d.year >= 2020);

  const totalCostPhase1 = CHART_DATA.totalCostToPatch.filter(d => d.year <= 2020);
  const totalCostPhase2 = CHART_DATA.totalCostToPatch.filter(d => d.year >= 2020);

  // Annotation opacities
  const emphasisOpacity = interpolate(
    frame,
    [BEATS.EMPHASIS_START, BEATS.EMPHASIS_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const crossingOpacity = interpolate(
    frame,
    [BEATS.CROSSING_START, BEATS.CROSSING_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Legend opacity
  const legendOpacity = interpolate(
    frame,
    [BEATS.DRAW_LINE_END, BEATS.DRAW_LINE_END + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* Morphing title - old title fades out */}
      {showTitle && frame < BEATS.MORPH_END && (
        <div
          style={{
            position: "absolute",
            top: 30,
            left: "50%",
            transform: "translateX(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 42,
            fontWeight: 700,
            color: COLORS.TITLE,
            opacity: oldTitleOpacity,
            textShadow: "0 2px 10px rgba(0,0,0,0.5)",
          }}
        >
          The Economics of Sock Repair
        </div>
      )}

      {/* Morphing title - new title fades in */}
      {showTitle && (
        <div
          style={{
            position: "absolute",
            top: 30,
            left: "50%",
            transform: "translateX(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 42,
            fontWeight: 700,
            color: COLORS.TITLE,
            opacity: newTitleOpacity,
            textShadow: "0 2px 10px rgba(0,0,0,0.5)",
          }}
        >
          The Economics of Code
        </div>
      )}

      {/* Chart axes and grid */}
      <ChartAxes />

      {/* Tech Debt Shaded Area - Phase 1: 1970 to 2020 */}
      <AnimatedArea
        topData={totalCostPhase1}
        bottomData={immediateCostPhase1}
        fillColor={COLORS.AREA_TECH_DEBT}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
      />

      {/* Tech Debt Shaded Area - Phase 2: 2020 to 2024 */}
      <AnimatedArea
        topData={totalCostPhase2}
        bottomData={immediateCostPhase2}
        fillColor={COLORS.AREA_TECH_DEBT}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
      />

      {/* Cost to Generate line - Phase 1: 1970 to 2020 */}
      <AnimatedLine
        data={costToGeneratePhase1}
        color={COLORS.LINE_GENERATE}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
        strokeWidth={4}
      />

      {/* Cost to Generate line - Phase 2: 2020 to 2024 (dramatic drop) */}
      <AnimatedLine
        data={costToGeneratePhase2}
        color={COLORS.LINE_GENERATE}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
        strokeWidth={4}
        label="Cost to Generate"
      />

      {/* Immediate Cost to Patch - Phase 1: 1970 to 2020 */}
      <AnimatedLine
        data={immediateCostPhase1}
        color={COLORS.LINE_PATCH}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
        strokeWidth={4}
      />

      {/* Immediate Cost to Patch - Phase 2: 2020 to 2024 (also drops) */}
      <AnimatedLine
        data={immediateCostPhase2}
        color={COLORS.LINE_PATCH}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
        strokeWidth={4}
        label="Immediate Patch Cost"
      />

      {/* Total Cost of Patching (dashed) - Phase 1: 1970 to 2020 */}
      <AnimatedLine
        data={totalCostPhase1}
        color={COLORS.LINE_PATCH_TOTAL}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
        strokeWidth={3}
        dashed={true}
        showDot={false}
      />

      {/* Total Cost of Patching (dashed) - Phase 2: 2020 to 2024 (barely moves) */}
      <AnimatedLine
        data={totalCostPhase2}
        color={COLORS.LINE_PATCH_TOTAL}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
        strokeWidth={3}
        dashed={true}
        showDot={false}
        label="Total Cost (with debt)"
      />

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          top: 120,
          right: 40,
          opacity: legendOpacity,
          backgroundColor: "rgba(0, 0, 0, 0.4)",
          padding: "16px 20px",
          borderRadius: 8,
        }}
      >
        {/* Cost to Generate */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            marginBottom: 12,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 20,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 36,
              height: 4,
              backgroundColor: COLORS.LINE_GENERATE,
              marginRight: 12,
              borderRadius: 2,
            }}
          />
          Cost to Generate
        </div>

        {/* Immediate Patch Cost */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            marginBottom: 12,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 20,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 36,
              height: 4,
              backgroundColor: COLORS.LINE_PATCH,
              marginRight: 12,
              borderRadius: 2,
            }}
          />
          Immediate Patch Cost
        </div>

        {/* Total Cost with Debt (dashed) */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 20,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <svg width={36} height={4} style={{ marginRight: 12 }}>
            <line
              x1={0}
              y1={2}
              x2={36}
              y2={2}
              stroke={COLORS.LINE_PATCH_TOTAL}
              strokeWidth={4}
              strokeDasharray="8,4"
            />
          </svg>
          Total Cost with Debt
        </div>
      </div>

      {/* Emphasis annotations */}
      {frame >= BEATS.EMPHASIS_START && frame < BEATS.CROSSING_START && (
        <div
          style={{
            position: "absolute",
            bottom: 180,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: emphasisOpacity,
            textAlign: "center",
            backgroundColor: "rgba(0, 0, 0, 0.75)",
            padding: "24px 40px",
            borderRadius: 12,
          }}
        >
          <p
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 28,
              color: COLORS.LINE_PATCH,
              margin: 0,
              marginBottom: 8,
              fontWeight: 600,
            }}
          >
            AI made each patch faster...
          </p>
          <p
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 28,
              color: "#ffffff",
              margin: 0,
              fontWeight: 500,
            }}
          >
            ...but debt still accumulates
          </p>
        </div>
      )}

      {/* Crossing point annotation */}
      {frame >= BEATS.CROSSING_START && (
        <div
          style={{
            position: "absolute",
            bottom: 180,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: crossingOpacity,
            textAlign: "center",
            backgroundColor: "rgba(0, 0, 0, 0.75)",
            padding: "24px 40px",
            borderRadius: 12,
          }}
        >
          <p
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 24,
              color: "#ffffff",
              margin: 0,
              marginBottom: 12,
              fontWeight: 500,
            }}
          >
            Generate: <span style={{ color: COLORS.LINE_GENERATE, fontWeight: 700 }}>6 hrs</span>
            {" "}&nbsp;&nbsp;&nbsp;vs&nbsp;&nbsp;&nbsp;{" "}
            Total Patch: <span style={{ color: COLORS.LINE_PATCH, fontWeight: 700 }}>24 hrs</span>
          </p>
          <p
            style={{
              fontFamily: "Georgia, serif",
              fontSize: 32,
              color: "#ffffff",
              textShadow: "0 2px 10px rgba(0,0,0,0.8)",
              fontStyle: "italic",
              margin: 0,
            }}
          >
            "The crossover point has arrived."
          </p>
        </div>
      )}
    </AbsoluteFill>
  );
};
