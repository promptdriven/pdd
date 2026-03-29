// Part1Economics06DebtLayersZoom.tsx — Main component
// Camera zooms into the debt area from a cost chart, then the monolithic amber
// area separates into two layers: Code Complexity (lower) and Context Rot (upper).
import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import { DebtLayer } from "./DebtLayer";
import {
  BACKGROUND_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  // Zoom
  ZOOM_START,
  ZOOM_END,
  ZOOM_ORIGIN_X,
  ZOOM_ORIGIN_Y,
  ZOOM_SCALE_FROM,
  ZOOM_SCALE_TO,
  // Split
  SPLIT_START,
  SPLIT_END,
  // Layers
  CODE_COMPLEXITY_COLOR,
  CODE_COMPLEXITY_FILL_OPACITY,
  CONTEXT_ROT_COLOR,
  CONTEXT_ROT_FILL_OPACITY,
  DEBT_AREA_COLOR,
  DEBT_AREA_OPACITY,
  // Layout
  LAYER_GAP,
  LAYER_AREA_TOP,
  LAYER_AREA_BOTTOM,
  LAYER_AREA_LEFT,
  LAYER_AREA_RIGHT,
  LAYER_MIDPOINT_RATIO,
  // Chart
  CHART_GRID_COLOR,
  CHART_GRID_OPACITY,
  CHART_AXIS_COLOR,
  CHART_AXIS_OPACITY,
  CHART_LINE_COLOR,
  YEAR_LABELS,
  // Typography
  LABEL_FONT_FAMILY,
} from "./constants";

// === Default props (required by spec) ===
export const defaultPart1Economics06DebtLayersZoomProps = {};

// === Simplified cost chart background (pre-zoom view) ===
const ChartBackground: React.FC = () => {
  // Simplified representation of the code cost chart that we're zooming into
  const chartLeft = 160;
  const chartRight = 1760;
  const chartTop = 120;
  const chartBottom = 860;
  const chartWidth = chartRight - chartLeft;
  const chartHeight = chartBottom - chartTop;

  // Generate cost curve points (generate vs patch with debt area)
  const generateCurve: string[] = [];
  const patchCurve: string[] = [];
  const numPoints = 100;

  for (let i = 0; i <= numPoints; i++) {
    const t = i / numPoints;
    const x = chartLeft + t * chartWidth;

    // Generate cost: starts low, rises steeply after 2023
    const genY =
      chartBottom - chartHeight * (0.15 + 0.05 * t + 0.6 * Math.pow(t, 3));
    generateCurve.push(`${x},${genY}`);

    // Patch cost: starts very low, rises even more steeply
    const patchY =
      chartBottom -
      chartHeight * (0.08 + 0.02 * t + 0.75 * Math.pow(t, 3.5));
    patchCurve.push(`${x},${patchY}`);
  }

  // Debt area: region between the two curves (right portion)
  const debtAreaPoints: string[] = [];
  for (let i = 40; i <= numPoints; i++) {
    debtAreaPoints.push(generateCurve[i]);
  }
  for (let i = numPoints; i >= 40; i--) {
    debtAreaPoints.push(patchCurve[i]);
  }

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Grid lines */}
      {[0.2, 0.4, 0.6, 0.8].map((frac) => (
        <line
          key={`h-${frac}`}
          x1={chartLeft}
          y1={chartTop + frac * chartHeight}
          x2={chartRight}
          y2={chartTop + frac * chartHeight}
          stroke={CHART_GRID_COLOR}
          strokeOpacity={CHART_GRID_OPACITY}
          strokeWidth={1}
        />
      ))}
      {YEAR_LABELS.map((_, idx) => {
        const x = chartLeft + ((idx + 0.5) / YEAR_LABELS.length) * chartWidth;
        return (
          <line
            key={`v-${idx}`}
            x1={x}
            y1={chartTop}
            x2={x}
            y2={chartBottom}
            stroke={CHART_GRID_COLOR}
            strokeOpacity={CHART_GRID_OPACITY}
            strokeWidth={1}
          />
        );
      })}

      {/* Axes */}
      <line
        x1={chartLeft}
        y1={chartBottom}
        x2={chartRight}
        y2={chartBottom}
        stroke={CHART_AXIS_COLOR}
        strokeOpacity={CHART_AXIS_OPACITY}
        strokeWidth={2}
      />
      <line
        x1={chartLeft}
        y1={chartTop}
        x2={chartLeft}
        y2={chartBottom}
        stroke={CHART_AXIS_COLOR}
        strokeOpacity={CHART_AXIS_OPACITY}
        strokeWidth={2}
      />

      {/* Year labels */}
      {YEAR_LABELS.map((year, idx) => {
        const x = chartLeft + ((idx + 0.5) / YEAR_LABELS.length) * chartWidth;
        return (
          <text
            key={year}
            x={x}
            y={chartBottom + 30}
            fill={CHART_AXIS_COLOR}
            fillOpacity={0.5}
            fontSize={14}
            fontFamily={LABEL_FONT_FAMILY}
            textAnchor="middle"
          >
            {year}
          </text>
        );
      })}

      {/* Debt area (shaded region between curves) */}
      <polygon
        points={debtAreaPoints.join(" ")}
        fill={DEBT_AREA_COLOR}
        fillOpacity={DEBT_AREA_OPACITY}
      />

      {/* Generate cost curve */}
      <polyline
        points={generateCurve.join(" ")}
        fill="none"
        stroke={CHART_LINE_COLOR}
        strokeWidth={2.5}
        strokeOpacity={0.8}
      />

      {/* Patch cost curve */}
      <polyline
        points={patchCurve.join(" ")}
        fill="none"
        stroke="#22C55E"
        strokeWidth={2.5}
        strokeOpacity={0.8}
      />
    </svg>
  );
};

// === Main Component ===
export const Part1Economics06DebtLayersZoom: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Phase 1: Camera zoom (frame 0-90) ---
  const zoomScale = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [ZOOM_SCALE_FROM, ZOOM_SCALE_TO],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Translate so zoom centers on ZOOM_ORIGIN
  const translateX = -(ZOOM_ORIGIN_X * (zoomScale - 1));
  const translateY = -(ZOOM_ORIGIN_Y * (zoomScale - 1));

  // Chart periphery fades as we zoom in
  const chartPeripheryOpacity = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // --- Phase 2: Layer separation (frame 90-180) ---
  const totalAreaHeight = LAYER_AREA_BOTTOM - LAYER_AREA_TOP;
  const lowerHeight = totalAreaHeight * LAYER_MIDPOINT_RATIO;
  const upperHeight = totalAreaHeight * (1 - LAYER_MIDPOINT_RATIO);

  // Split progress: 0 = merged, 1 = fully separated
  const splitProgress = interpolate(
    frame,
    [SPLIT_START, SPLIT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // When merged: both layers occupy the full area as one block
  // When split: lower layer moves down, upper layer moves up, gap appears
  const halfGap = (LAYER_GAP / 2) * splitProgress;
  const splitOffset = splitProgress * 20; // extra separation for visual clarity

  // Lower layer: starts at LAYER_AREA_TOP, ends at mid-gap
  const lowerLayerTop =
    LAYER_AREA_TOP +
    interpolate(splitProgress, [0, 1], [upperHeight, 0]) +
    halfGap;
  const lowerLayerHeight = interpolate(
    splitProgress,
    [0, 1],
    [totalAreaHeight, lowerHeight]
  );

  // Upper layer: starts at LAYER_AREA_TOP
  const upperLayerTop = LAYER_AREA_TOP - splitOffset;
  const upperLayerHeight = interpolate(
    splitProgress,
    [0, 1],
    [totalAreaHeight, upperHeight]
  );

  // Layer opacity transitions: merged = debt area opacity, split = individual opacities
  const lowerFillOpacity = interpolate(
    splitProgress,
    [0, 1],
    [DEBT_AREA_OPACITY, CODE_COMPLEXITY_FILL_OPACITY]
  );
  const upperFillOpacity = interpolate(
    splitProgress,
    [0, 1],
    [DEBT_AREA_OPACITY, CONTEXT_ROT_FILL_OPACITY]
  );

  // Upper layer color transitions from debt amber to context rot amber
  const showNoise = splitProgress > 0.3;

  const layerWidth = LAYER_AREA_RIGHT - LAYER_AREA_LEFT;

  // Monolithic pre-split opacity (fades as split begins)
  const monolithicOpacity = interpolate(
    splitProgress,
    [0, 0.15],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Split layers fade in
  const splitLayerOpacity = interpolate(
    splitProgress,
    [0, 0.2],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // --- Context Rot pulse effect during hold (frame 270+) ---
  const pulseOpacity =
    frame >= 270
      ? CONTEXT_ROT_FILL_OPACITY +
        0.02 * Math.sin((frame - 270) * 0.05)
      : upperFillOpacity;

  return (
    <AbsoluteFill style={{ backgroundColor: BACKGROUND_COLOR }}>
      {/* Zooming container */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: CANVAS_WIDTH,
          height: CANVAS_HEIGHT,
          transform: `translate(${translateX}px, ${translateY}px) scale(${zoomScale})`,
          transformOrigin: "0 0",
        }}
      >
        {/* Chart background (fades as we zoom) */}
        <div style={{ opacity: chartPeripheryOpacity }}>
          <ChartBackground />
        </div>

        {/* Monolithic debt area (visible before split) */}
        {monolithicOpacity > 0 && (
          <div
            style={{
              position: "absolute",
              top: LAYER_AREA_TOP,
              left: LAYER_AREA_LEFT,
              width: layerWidth,
              height: totalAreaHeight,
              backgroundColor: DEBT_AREA_COLOR,
              opacity: DEBT_AREA_OPACITY * monolithicOpacity,
              borderRadius: 4,
            }}
          />
        )}

        {/* Split layers */}
        <Sequence from={SPLIT_START}>
          {/* Lower layer — Code Complexity */}
          <DebtLayer
            top={lowerLayerTop}
            layerHeight={Math.max(lowerLayerHeight, 0)}
            left={LAYER_AREA_LEFT}
            layerWidth={layerWidth}
            fillColor={CODE_COMPLEXITY_COLOR}
            fillOpacity={lowerFillOpacity}
            label="Code Complexity"
            labelColor={CODE_COMPLEXITY_COLOR}
            layerOpacity={splitLayerOpacity}
          />

          {/* Upper layer — Context Rot */}
          <DebtLayer
            top={upperLayerTop}
            layerHeight={Math.max(upperLayerHeight, 0)}
            left={LAYER_AREA_LEFT}
            layerWidth={layerWidth}
            fillColor={CONTEXT_ROT_COLOR}
            fillOpacity={frame >= 270 ? pulseOpacity : upperFillOpacity}
            label="Context Rot"
            labelColor={CONTEXT_ROT_COLOR}
            showNoise={showNoise}
            layerOpacity={splitLayerOpacity}
          />
        </Sequence>

        {/* Hairline gap indicator between layers (visible after split) */}
        {splitProgress > 0.5 && (
          <div
            style={{
              position: "absolute",
              top:
                upperLayerTop +
                upperLayerHeight -
                1,
              left: LAYER_AREA_LEFT,
              width: layerWidth,
              height: LAYER_GAP,
              backgroundColor: BACKGROUND_COLOR,
              opacity: interpolate(
                splitProgress,
                [0.5, 0.8],
                [0, 1],
                {
                  extrapolateLeft: "clamp",
                  extrapolateRight: "clamp",
                }
              ),
            }}
          />
        )}
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics06DebtLayersZoom;
