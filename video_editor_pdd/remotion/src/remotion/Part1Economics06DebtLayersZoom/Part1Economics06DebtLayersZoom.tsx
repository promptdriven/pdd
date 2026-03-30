import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  // Zoom
  ZOOM_ORIGIN_X,
  ZOOM_ORIGIN_Y,
  ZOOM_FACTOR,
  ZOOM_START,
  ZOOM_END,
  // Split
  SPLIT_START,
  SPLIT_END,
  // Debt area geometry
  DEBT_AREA_TOP,
  DEBT_AREA_BOTTOM,
  DEBT_AREA_LEFT,
  DEBT_AREA_RIGHT,
  DEBT_AREA_COLOR,
  DEBT_AREA_OPACITY,
  SPLIT_Y,
  LAYER_GAP,
  // Layer colors
  CODE_COMPLEXITY_COLOR,
  CODE_COMPLEXITY_OPACITY,
  CONTEXT_ROT_COLOR,
  CONTEXT_ROT_OPACITY,
  // Labels
  LABEL_FADE_START,
  // Grid
  GRID_COLOR,
  GRID_OPACITY,
  YEAR_LABELS,
  LABEL_FONT_FAMILY,
} from "./constants";
import { DebtLayer } from "./DebtLayer";
import { NoiseTexture } from "./NoiseTexture";

// Default props (empty — component is self-contained)
export const defaultPart1Economics06DebtLayersZoomProps = {};

/**
 * Part1Economics06DebtLayersZoom
 *
 * Zooms into the debt area of a cost chart, then splits the monolithic amber
 * region into two distinct layers: "Code Complexity" (lower, darker amber)
 * and "Context Rot" (upper, lighter amber with noise texture).
 *
 * 540 frames @ 30fps = 18 seconds
 */
export const Part1Economics06DebtLayersZoom: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Zoom animation (frames 0-90) ──────────────────────────────────
  const zoomScale = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [1.0, ZOOM_FACTOR],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Translate so the zoom origin stays centered
  const translateX = -(ZOOM_ORIGIN_X * (zoomScale - 1));
  const translateY = -(ZOOM_ORIGIN_Y * (zoomScale - 1));

  // Fade out chart periphery during zoom
  const peripheryOpacity = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [1.0, 0.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // ── Layer separation animation (frames 90-180) ────────────────────
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

  // Monolithic area opacity — fades out as layers separate
  const monolithOpacity = interpolate(
    frame,
    [SPLIT_START, SPLIT_START + 30],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Layer visibility — fades in as split begins
  const layerVisibility = interpolate(
    frame,
    [SPLIT_START, SPLIT_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Compute layer positions with separation gap
  const debtAreaWidth = DEBT_AREA_RIGHT - DEBT_AREA_LEFT;
  const totalHeight = DEBT_AREA_BOTTOM - DEBT_AREA_TOP;
  const upperHeight = SPLIT_Y - DEBT_AREA_TOP; // Context Rot (upper)
  const lowerHeight = DEBT_AREA_BOTTOM - SPLIT_Y; // Code Complexity (lower)

  // Gap expands during split
  const currentGap = splitProgress * LAYER_GAP;

  // Upper layer moves up, lower layer moves down during split
  const upperShift = -splitProgress * (LAYER_GAP / 2 + 8);
  const lowerShift = splitProgress * (LAYER_GAP / 2 + 8);

  const upperTop = DEBT_AREA_TOP + upperShift;
  const lowerTop = SPLIT_Y + currentGap + lowerShift;

  // Show labels after frame 180
  const showLabels = frame >= LABEL_FADE_START;

  // ── Context Rot pulse (frames 270+) ───────────────────────────────
  const contextRotPulse =
    frame >= 270
      ? 1 + 0.02 * Math.sin((frame - 270) * 0.05)
      : 1;

  // ── Simulated chart elements (visible before zoom completes) ──────
  // These represent the chart from which we're zooming — simple lines/shapes

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Zoomed container */}
      <div
        style={{
          position: "absolute",
          width: CANVAS_WIDTH,
          height: CANVAS_HEIGHT,
          transform: `translate(${translateX}px, ${translateY}px) scale(${zoomScale})`,
          transformOrigin: "0 0",
        }}
      >
        {/* ── Chart background elements (fade with periphery) ────── */}
        <div style={{ opacity: peripheryOpacity }}>
          {/* Simulated chart axes */}
          <ChartAxes />
          {/* Year labels along bottom */}
          <YearLabels />
          {/* Chart title area */}
          <div
            style={{
              position: "absolute",
              top: 40,
              left: 100,
              fontFamily: LABEL_FONT_FAMILY,
              fontSize: 14,
              color: "#FFFFFF",
              opacity: 0.5,
              letterSpacing: "0.03em",
            }}
          >
            Code Cost: Generate vs. Patch
          </div>
        </div>

        {/* ── Grid lines (subtle, persist through zoom) ────────── */}
        <GridLines opacity={Math.max(0.02, peripheryOpacity * GRID_OPACITY)} />

        {/* ── Monolithic debt area (pre-split) ─────────────────── */}
        {monolithOpacity > 0 && (
          <div
            style={{
              position: "absolute",
              left: DEBT_AREA_LEFT,
              top: DEBT_AREA_TOP,
              width: debtAreaWidth,
              height: totalHeight,
              backgroundColor: DEBT_AREA_COLOR,
              opacity: DEBT_AREA_OPACITY * monolithOpacity,
              borderRadius: 2,
            }}
          />
        )}

        {/* ── Split layers ─────────────────────────────────────── */}
        {layerVisibility > 0 && (
          <div style={{ opacity: layerVisibility }}>
            {/* Upper layer — Context Rot */}
            <DebtLayer
              left={DEBT_AREA_LEFT}
              top={upperTop}
              width={debtAreaWidth}
              height={upperHeight}
              fillColor={CONTEXT_ROT_COLOR}
              fillOpacity={CONTEXT_ROT_OPACITY * contextRotPulse}
              label="Context Rot"
              labelColor={CONTEXT_ROT_COLOR}
              showLabel={showLabels}
            >
              <NoiseTexture
                width={debtAreaWidth}
                height={upperHeight}
              />
            </DebtLayer>

            {/* Lower layer — Code Complexity */}
            <DebtLayer
              left={DEBT_AREA_LEFT}
              top={lowerTop}
              width={debtAreaWidth}
              height={lowerHeight}
              fillColor={CODE_COMPLEXITY_COLOR}
              fillOpacity={CODE_COMPLEXITY_OPACITY}
              label="Code Complexity"
              labelColor={CODE_COMPLEXITY_COLOR}
              showLabel={showLabels}
            />
          </div>
        )}

        {/* ── Hairline crack between layers ─────────────────── */}
        {splitProgress > 0.1 && (
          <div
            style={{
              position: "absolute",
              left: DEBT_AREA_LEFT,
              top: SPLIT_Y + upperShift + upperHeight - 1,
              width: debtAreaWidth,
              height: currentGap + Math.abs(upperShift) + Math.abs(lowerShift),
              backgroundColor: BG_COLOR,
              opacity: interpolate(splitProgress, [0.1, 0.5], [0, 1], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }),
            }}
          />
        )}

        {/* ── Simulated cost curves (fade with periphery) ────── */}
        <div style={{ opacity: peripheryOpacity }}>
          <CostCurves />
        </div>
      </div>
    </AbsoluteFill>
  );
};

// ── Sub-components (chart scaffolding) ──────────────────────────────────

/** Simple chart axes: Y-axis left, X-axis bottom */
const ChartAxes: React.FC = () => (
  <>
    {/* Y-axis */}
    <div
      style={{
        position: "absolute",
        left: 180,
        top: 80,
        width: 2,
        height: 620,
        backgroundColor: GRID_COLOR,
        opacity: 0.15,
      }}
    />
    {/* X-axis */}
    <div
      style={{
        position: "absolute",
        left: 180,
        top: 700,
        width: 1560,
        height: 2,
        backgroundColor: GRID_COLOR,
        opacity: 0.15,
      }}
    />
  </>
);

/** Year labels along the X-axis */
const YearLabels: React.FC = () => (
  <>
    {YEAR_LABELS.map((year, i) => (
      <div
        key={year}
        style={{
          position: "absolute",
          left: 240 + i * 320,
          top: 715,
          fontFamily: LABEL_FONT_FAMILY,
          fontSize: 12,
          color: "#FFFFFF",
          opacity: 0.35,
        }}
      >
        {year}
      </div>
    ))}
  </>
);

/** Subtle grid lines */
const GridLines: React.FC<{ opacity: number }> = ({ opacity }) => (
  <>
    {[0, 1, 2, 3, 4].map((i) => (
      <div
        key={`hgrid-${i}`}
        style={{
          position: "absolute",
          left: 182,
          top: 200 + i * 120,
          width: 1556,
          height: 1,
          backgroundColor: GRID_COLOR,
          opacity,
        }}
      />
    ))}
    {[0, 1, 2, 3, 4].map((i) => (
      <div
        key={`vgrid-${i}`}
        style={{
          position: "absolute",
          left: 240 + i * 320,
          top: 80,
          width: 1,
          height: 620,
          backgroundColor: GRID_COLOR,
          opacity,
        }}
      />
    ))}
  </>
);

/** Simulated cost curves as simple SVG paths */
const CostCurves: React.FC = () => (
  <svg
    width={1920}
    height={1080}
    style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
  >
    {/* "Generate" cost curve — starts low, rises */}
    <path
      d="M 240,650 C 500,640 800,580 1100,480 C 1300,420 1500,300 1740,200"
      fill="none"
      stroke="#3B82F6"
      strokeWidth={2.5}
      opacity={0.6}
    />
    {/* "Patch" cost curve — starts high, drops, then rises */}
    <path
      d="M 240,300 C 500,350 700,500 900,520 C 1100,540 1300,560 1740,600"
      fill="none"
      stroke="#22C55E"
      strokeWidth={2.5}
      opacity={0.6}
    />
    {/* Debt area fill (amber, under the curves) — visible as context before zoom */}
    <path
      d="M 700,520 C 900,530 1100,500 1300,460 L 1740,350 L 1740,600 C 1500,570 1300,550 1100,540 C 900,530 800,525 700,520 Z"
      fill={DEBT_AREA_COLOR}
      opacity={0.08}
    />
  </svg>
);

export default Part1Economics06DebtLayersZoom;
