import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame } from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
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
  // Phase 2 (frame 360-480): Draw from 2020 to 2024 (dramatic drop)
  const costToGeneratePhase1 = CHART_DATA.costToGenerate.filter(d => d.year <= 2020);
  const costToGeneratePhase2 = CHART_DATA.costToGenerate.filter(d => d.year >= 2020);

  // Cost to Patch draws across the full timeline in phase 1
  const costToPatchData = CHART_DATA.costToPatch;

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

      {/* Cost to Generate line - Phase 1: 1970 to 2020 */}
      <AnimatedLine
        data={costToGeneratePhase1}
        color={COLORS.LINE_GENERATE}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
        label=""
      />

      {/* Cost to Generate line - Phase 2: 2020 to 2024 (dramatic drop) */}
      <AnimatedLine
        data={costToGeneratePhase2}
        color={COLORS.LINE_GENERATE}
        startFrame={BEATS.DRAW_LINE_MID}
        endFrame={BEATS.DRAW_LINE_END}
        label="Cost to Generate"
      />

      {/* Cost to Patch line */}
      <AnimatedLine
        data={costToPatchData}
        color={COLORS.LINE_PATCH}
        startFrame={BEATS.DRAW_LINE_START}
        endFrame={BEATS.DRAW_LINE_MID}
        strokeWidth={4}
        label="Cost to Patch"
      />

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          top: 120,
          right: 60,
          opacity: interpolate(
            frame,
            [BEATS.DRAW_LINE_END, BEATS.DRAW_LINE_END + 30],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          ),
        }}
      >
        <div
          style={{
            display: "flex",
            alignItems: "center",
            marginBottom: 16,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 24,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 40,
              height: 5,
              backgroundColor: COLORS.LINE_GENERATE,
              marginRight: 16,
              borderRadius: 2,
            }}
          />
          Cost to Generate
        </div>
        <div
          style={{
            display: "flex",
            alignItems: "center",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 24,
            fontWeight: 500,
            color: "#ffffff",
          }}
        >
          <div
            style={{
              width: 40,
              height: 5,
              backgroundColor: COLORS.LINE_PATCH,
              marginRight: 16,
              borderRadius: 2,
            }}
          />
          Cost to Patch
        </div>
      </div>

      {/* Dramatic annotation for the 2020-2024 drop */}
      {frame >= BEATS.HOLD_START && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
            opacity: interpolate(
              frame,
              [BEATS.HOLD_START, BEATS.HOLD_START + 30],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            textAlign: "center",
            backgroundColor: "rgba(0, 0, 0, 0.7)",
            padding: "30px 50px",
            borderRadius: 12,
          }}
        >
          <p
            style={{
              fontFamily: "Georgia, serif",
              fontSize: 36,
              color: "#ffffff",
              textShadow: "0 2px 10px rgba(0,0,0,0.8)",
              fontStyle: "italic",
              maxWidth: 900,
              lineHeight: 1.5,
              margin: 0,
            }}
          >
            "The crossover point is approaching."
          </p>
        </div>
      )}
    </AbsoluteFill>
  );
};
