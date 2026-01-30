import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { AnimatedArea } from "./AnimatedArea";
import {
  COLORS,
  CHART_DATA,
  BEATS,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  CodeCostChartPropsType,
} from "./constants";

export const CodeCostChart: React.FC<CodeCostChartPropsType> = ({
  showTitle = true,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  const getXPosition = (year: number) => {
    return CHART_MARGINS.left + ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth;
  };

  const getYPosition = (hours: number) => {
    return CHART_MARGINS.top + chartHeight - (hours / HOURS_RANGE.max) * chartHeight;
  };

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

  // Split data for two-phase animation
  // Phase 1 (frame 750-1500): Draw 2015 → 2020
  // Phase 2 (frame 1500-2700): Draw 2020 → 2025 (fork + dramatic changes)
  const costToGeneratePhase1 = CHART_DATA.costToGenerate.filter(d => d.year <= 2020);
  const costToGeneratePhase2 = CHART_DATA.costToGenerate.filter(d => d.year >= 2020);

  const totalCostPhase1 = CHART_DATA.totalCostLargeCodebase.filter(d => d.year <= 2020);
  const totalCostPhase2 = CHART_DATA.totalCostLargeCodebase.filter(d => d.year >= 2020);

  // "Same tools. Different codebase sizes." annotation - mid Phase 2
  const forkAnnotationOpacity = interpolate(
    frame,
    [BEATS.DRAW_LINE_MID + 300, BEATS.DRAW_LINE_MID + 360],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Curved arrow annotation - appears with delay during Phase 2
  const arrowOpacity = interpolate(
    frame,
    [BEATS.DRAW_LINE_MID + 600, BEATS.DRAW_LINE_MID + 660],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

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

  // Arrow coordinates: from small codebase (~3 hrs) to large codebase (~11 hrs) at ~2023.5
  const arrowX = getXPosition(2023.5);
  const arrowStartY = getYPosition(3);
  const arrowEndY = getYPosition(11);

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

      {/* Tech Debt Shaded Area - Phase 1: 2015 to 2020 */}
      <AnimatedArea
        topData={totalCostPhase1}
        bottomData={CHART_DATA.immediateCostBaseline}
        fillColor={COLORS.AREA_TECH_DEBT}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
      />

      {/* Tech Debt Shaded Area - Phase 2: 2020 to 2025 (above large codebase line) */}
      <AnimatedArea
        topData={totalCostPhase2}
        bottomData={CHART_DATA.immediateCostLargeCodebase}
        fillColor={COLORS.AREA_TECH_DEBT}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
      />

      {/* Cost to Generate - Phase 1: 2015 to 2020 */}
      <AnimatedLine
        data={costToGeneratePhase1}
        color={COLORS.LINE_GENERATE}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
        strokeWidth={4}
      />

      {/* Cost to Generate - Phase 2: 2020 to 2025 (dramatic drop) */}
      <AnimatedLine
        data={costToGeneratePhase2}
        color={COLORS.LINE_GENERATE}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
        strokeWidth={4}
        label="Cost to Generate"
      />

      {/* Immediate Cost to Patch - Phase 1: baseline 2015-2020 (single line) */}
      <AnimatedLine
        data={CHART_DATA.immediateCostBaseline}
        color={COLORS.LINE_PATCH}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
        strokeWidth={4}
      />

      {/* Immediate Patch - Phase 2: Small codebase fork (bright, drops to 1.5) */}
      <AnimatedLine
        data={CHART_DATA.immediateCostSmallCodebase}
        color={COLORS.LINE_PATCH}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
        strokeWidth={3}
        label="Small Codebase"
      />

      {/* Immediate Patch - Phase 2: Large codebase fork (dimmer, stays flat 10-12) */}
      <AnimatedLine
        data={CHART_DATA.immediateCostLargeCodebase}
        color={COLORS.LINE_PATCH}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
        strokeWidth={2}
        lineOpacity={0.7}
        label="Large Codebase"
      />

      {/* Total Cost of Patching (dashed) - Phase 1: 2015 to 2020 */}
      <AnimatedLine
        data={totalCostPhase1}
        color={COLORS.LINE_PATCH_TOTAL}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
        strokeWidth={3}
        dashed={true}
        showDot={false}
      />

      {/* Total Cost (dashed) - Phase 2: 2020 to 2025 (RISES to 33) */}
      <AnimatedLine
        data={totalCostPhase2}
        color={COLORS.LINE_PATCH_TOTAL}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
        strokeWidth={3}
        dashed={true}
        showDot={false}
        label="True Cost (with tech debt)"
      />

      {/* "Same tools. Different codebase sizes." annotation during Phase 2 */}
      {frame >= BEATS.DRAW_LINE_MID + 300 && frame < BEATS.EMPHASIS_START && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
            opacity: forkAnnotationOpacity,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 26,
            fontWeight: 600,
            color: "#ffffff",
            textShadow: "0 2px 10px rgba(0,0,0,0.8)",
            backgroundColor: "rgba(0, 0, 0, 0.6)",
            padding: "16px 32px",
            borderRadius: 8,
          }}
        >
          Same tools. Different codebase sizes.
        </div>
      )}

      {/* Curved arrow from small fork to large fork: "Every patch adds code" */}
      {frame >= BEATS.DRAW_LINE_MID + 600 && (
        <svg
          width={width}
          height={height}
          style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
        >
          <defs>
            <marker
              id="arrowhead"
              markerWidth="10"
              markerHeight="7"
              refX="10"
              refY="3.5"
              orient="auto"
            >
              <polygon
                points="0 0, 10 3.5, 0 7"
                fill={COLORS.LINE_PATCH}
                opacity={arrowOpacity}
              />
            </marker>
          </defs>
          <path
            d={`M ${arrowX} ${arrowStartY} C ${arrowX + 80} ${arrowStartY}, ${arrowX + 80} ${arrowEndY}, ${arrowX} ${arrowEndY}`}
            fill="none"
            stroke={COLORS.LINE_PATCH}
            strokeWidth={2}
            strokeDasharray="6,4"
            opacity={arrowOpacity}
            markerEnd="url(#arrowhead)"
          />
          <text
            x={arrowX + 90}
            y={(arrowStartY + arrowEndY) / 2}
            fill="#ffffff"
            fontSize={20}
            fontFamily="Inter, system-ui, sans-serif"
            fontWeight={500}
            opacity={arrowOpacity}
            textAnchor="start"
            dominantBaseline="middle"
          >
            Every patch adds code
          </text>
        </svg>
      )}

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          top: 300,
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
            marginBottom: 10,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
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

        {/* Immediate Patch - Small Codebase */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            marginBottom: 10,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 36,
              height: 3,
              backgroundColor: COLORS.LINE_PATCH,
              marginRight: 12,
              borderRadius: 2,
            }}
          />
          Patch (Small CB)
        </div>

        {/* Immediate Patch - Large Codebase */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            marginBottom: 10,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
            fontWeight: 500,
            color: "#ffffff",
            opacity: 0.7,
          }}
        >
          <div
            style={{
              width: 36,
              height: 2,
              backgroundColor: COLORS.LINE_PATCH,
              marginRight: 12,
              borderRadius: 2,
            }}
          />
          Patch (Large CB)
        </div>

        {/* Total Cost with Debt (dashed) */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
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
              strokeWidth={3}
              strokeDasharray="8,4"
            />
          </svg>
          True Cost (with tech debt)
        </div>
      </div>

      {/* Emphasis annotations */}
      {frame >= BEATS.EMPHASIS_START && frame < BEATS.CROSSING_START && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
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
            Small codebase: -55% (Peng et al., 2023)
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
            Large codebase: +19% slower (METR, 2025)
          </p>
          <p
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 28,
              color: COLORS.LINE_PATCH,
              margin: 0,
              marginTop: 8,
              fontWeight: 600,
            }}
          >
            Bug rate: +41% (Uplevel, 2024)
          </p>
        </div>
      )}

      {/* Crossing point annotation */}
      {frame >= BEATS.CROSSING_START && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
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
            Generate: <span style={{ color: COLORS.LINE_GENERATE, fontWeight: 700 }}>3 hrs</span>
            {" "}&nbsp;&nbsp;&nbsp;vs&nbsp;&nbsp;&nbsp;{" "}
            Large CB Total: <span style={{ color: COLORS.LINE_PATCH, fontWeight: 700 }}>33 hrs</span>
          </p>
          <p
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 22,
              color: "rgba(255, 255, 255, 0.8)",
              margin: 0,
              marginBottom: 12,
              fontWeight: 400,
            }}
          >
            Patching wins... if you stay small. But patching makes you grow.
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
            &ldquo;We are here.&rdquo;
          </p>
        </div>
      )}
    </AbsoluteFill>
  );
};
