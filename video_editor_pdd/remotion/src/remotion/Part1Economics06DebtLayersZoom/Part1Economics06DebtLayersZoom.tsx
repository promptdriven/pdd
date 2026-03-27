import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import ChartBackdrop from "./ChartBackdrop";
import DebtLayer from "./DebtLayer";
import NoiseOverlay from "./NoiseOverlay";
import {
  BG_COLOR,
  CODE_COMPLEXITY_COLOR,
  CODE_COMPLEXITY_OPACITY,
  CONTEXT_ROT_COLOR,
  CONTEXT_ROT_OPACITY,
  UNIFIED_DEBT_COLOR,
  UNIFIED_DEBT_OPACITY,
  NOISE_COLOR,
  NOISE_OPACITY,
  NOISE_GRAIN_SIZE,
  NOISE_DRIFT_PX_PER_FRAME,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_FONT_FAMILY,
  AXIS_COLOR,
  AXIS_OPACITY,
  GRID_LINE_OPACITY,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CHART_LEFT,
  CHART_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  DEBT_AREA_X,
  DEBT_AREA_WIDTH,
  DEBT_AREA_Y_TOP,
  DEBT_AREA_Y_BOTTOM,
  ZOOM_ORIGIN_X,
  ZOOM_ORIGIN_Y,
  ZOOM_FACTOR,
  LAYER_GAP,
  ZOOM_START,
  ZOOM_END,
  SPLIT_START,
  SPLIT_END,
  LABEL_START,
  LABEL_FADE_DURATION,
  TEXTURE_START,
  TEXTURE_FADE_DURATION,
  YEAR_LABELS,
} from "./constants";

export const defaultPart1Economics06DebtLayersZoomProps = {};

/**
 * Section 1.6: Debt Layers Zoom — Code Complexity vs. Context Rot
 *
 * Camera zooms into the shaded debt area from the code cost chart.
 * The monolithic amber area separates into two distinct layers:
 *   - Lower: "Code Complexity" (darker amber)
 *   - Upper: "Context Rot" (lighter amber with noise texture)
 */
export const Part1Economics06DebtLayersZoom: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Phase 1: Camera zoom (frames 0-90) ──
  const zoomScale = interpolate(frame, [ZOOM_START, ZOOM_END], [1.0, ZOOM_FACTOR], {
    easing: Easing.inOut(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Translate so zoom centers on the target region
  const translateX = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [0, -(ZOOM_ORIGIN_X - CANVAS_WIDTH / 2) * (ZOOM_FACTOR - 1)],
    {
      easing: Easing.inOut(Easing.cubic),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );
  const translateY = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [0, -(ZOOM_ORIGIN_Y - CANVAS_HEIGHT / 2) * (ZOOM_FACTOR - 1)],
    {
      easing: Easing.inOut(Easing.cubic),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Chart periphery fades out during zoom
  const chartPeripheryOpacity = interpolate(frame, [ZOOM_START, ZOOM_END], [1, 0], {
    easing: Easing.inOut(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Phase 2: Layer separation (frames 90-180) ──
  // The unified debt area splits into two layers with a gap between them
  const splitProgress = interpolate(frame, [SPLIT_START, SPLIT_END], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Unified debt area dimensions (as seen after zoom)
  // These represent the debt region in the zoomed view
  const unifiedTop = 260;
  const unifiedHeight = 500;
  const unifiedLeft = 180;
  const unifiedWidth = 1560;

  // Split: lower layer stays mostly in place, upper layer moves up
  const finalLowerTop = unifiedTop + unifiedHeight * 0.52 + LAYER_GAP / 2;
  const finalLowerHeight = unifiedHeight * 0.44;
  const finalUpperTop = unifiedTop + unifiedHeight * 0.04;
  const finalUpperHeight = unifiedHeight * 0.48; // slightly taller — growing faster

  // Animate from unified block to split layers
  const lowerLayerTop = interpolate(
    splitProgress,
    [0, 1],
    [unifiedTop + unifiedHeight * 0.5, finalLowerTop],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const lowerLayerHeight = interpolate(
    splitProgress,
    [0, 1],
    [unifiedHeight * 0.5, finalLowerHeight],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const upperLayerTop = interpolate(
    splitProgress,
    [0, 1],
    [unifiedTop, finalUpperTop],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const upperLayerHeight = interpolate(
    splitProgress,
    [0, 1],
    [unifiedHeight * 0.5, finalUpperHeight],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Opacity transition: unified -> separate colors
  const lowerOpacity = interpolate(
    splitProgress,
    [0, 1],
    [UNIFIED_DEBT_OPACITY, CODE_COMPLEXITY_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const upperOpacity = interpolate(
    splitProgress,
    [0, 1],
    [UNIFIED_DEBT_OPACITY, CONTEXT_ROT_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Color transition for upper layer
  const upperColorProgress = interpolate(splitProgress, [0, 1], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Gap (hairline crack) between layers
  const gapOpacity = interpolate(splitProgress, [0.2, 0.5], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Phase 3: Labels fade in (frames 180-200) ──
  const labelOpacity = interpolate(
    frame,
    [LABEL_START, LABEL_START + LABEL_FADE_DURATION],
    [0, 0.9],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Noise texture fade-in
  const noiseOpacity = interpolate(
    frame,
    [TEXTURE_START, TEXTURE_START + TEXTURE_FADE_DURATION],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // ── Phase 4: Subtle pulse on Context Rot layer (frames 270+) ──
  const pulseOpacity =
    frame >= 270
      ? interpolate(
          Math.sin((frame - 270) * 0.05),
          [-1, 1],
          [CONTEXT_ROT_OPACITY * 0.85, CONTEXT_ROT_OPACITY * 1.15],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        )
      : upperOpacity;

  // Should we show the split layers? They appear once the split starts
  const showLayers = frame >= SPLIT_START;

  // Should we show the unified debt block? It's visible before the split completes
  // (the chart backdrop handles this via its debt area polygon)
  const showUnifiedDebt = frame < SPLIT_START;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Zooming container */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: CANVAS_WIDTH,
          height: CANVAS_HEIGHT,
          transform: `translate(${translateX}px, ${translateY}px) scale(${zoomScale})`,
          transformOrigin: `${ZOOM_ORIGIN_X}px ${ZOOM_ORIGIN_Y}px`,
        }}
      >
        {/* Chart backdrop — fades as we zoom in */}
        <ChartBackdrop
          opacity={chartPeripheryOpacity}
          chartLeft={CHART_LEFT}
          chartTop={CHART_TOP}
          chartWidth={CHART_WIDTH}
          chartHeight={CHART_HEIGHT}
          debtAreaX={DEBT_AREA_X}
          debtAreaWidth={DEBT_AREA_WIDTH}
          debtAreaYTop={DEBT_AREA_Y_TOP}
          debtAreaYBottom={DEBT_AREA_Y_BOTTOM}
          debtColor={UNIFIED_DEBT_COLOR}
          debtOpacity={UNIFIED_DEBT_OPACITY}
          axisColor={AXIS_COLOR}
          axisOpacity={AXIS_OPACITY}
          gridLineOpacity={GRID_LINE_OPACITY}
          yearLabels={YEAR_LABELS}
          fontFamily={LABEL_FONT_FAMILY}
        />

        {/* Unified debt area — visible before split */}
        {showUnifiedDebt && (
          <div
            style={{
              position: "absolute",
              top: DEBT_AREA_Y_TOP,
              left: DEBT_AREA_X,
              width: DEBT_AREA_WIDTH,
              height: DEBT_AREA_Y_BOTTOM - DEBT_AREA_Y_TOP,
              backgroundColor: UNIFIED_DEBT_COLOR,
              opacity: UNIFIED_DEBT_OPACITY,
              borderRadius: 4,
            }}
          />
        )}
      </div>

      {/* ── Post-zoom overlay: split layers ── */}
      {/* These render on top of the zoomed content, in screen space */}
      {showLayers && (
        <AbsoluteFill>
          {/* Hairline gap / crack between layers */}
          <div
            style={{
              position: "absolute",
              top: lowerLayerTop - LAYER_GAP,
              left: unifiedLeft,
              width: unifiedWidth,
              height: LAYER_GAP,
              backgroundColor: BG_COLOR,
              opacity: gapOpacity,
            }}
          />

          {/* Lower Layer — Code Complexity */}
          <DebtLayer
            top={lowerLayerTop}
            layerHeight={lowerLayerHeight}
            layerWidth={unifiedWidth}
            left={unifiedLeft}
            fillColor={CODE_COMPLEXITY_COLOR}
            fillOpacity={lowerOpacity}
            label="Code Complexity"
            labelColor={CODE_COMPLEXITY_COLOR}
            labelOpacity={labelOpacity}
            labelFontSize={LABEL_FONT_SIZE}
            labelFontWeight={LABEL_FONT_WEIGHT}
            fontFamily={LABEL_FONT_FAMILY}
          />

          {/* Upper Layer — Context Rot */}
          <DebtLayer
            top={upperLayerTop}
            layerHeight={upperLayerHeight}
            layerWidth={unifiedWidth}
            left={unifiedLeft}
            fillColor={
              upperColorProgress > 0.5 ? CONTEXT_ROT_COLOR : UNIFIED_DEBT_COLOR
            }
            fillOpacity={frame >= 270 ? pulseOpacity : upperOpacity}
            label="Context Rot"
            labelColor={CONTEXT_ROT_COLOR}
            labelOpacity={labelOpacity}
            labelFontSize={LABEL_FONT_SIZE}
            labelFontWeight={LABEL_FONT_WEIGHT}
            fontFamily={LABEL_FONT_FAMILY}
          >
            {/* Noise texture overlay — fades in during Phase 3 */}
            <NoiseOverlay
              width={unifiedWidth}
              height={upperLayerHeight}
              grainColor={NOISE_COLOR}
              grainOpacity={NOISE_OPACITY}
              grainSize={NOISE_GRAIN_SIZE}
              driftSpeed={NOISE_DRIFT_PX_PER_FRAME}
              opacity={noiseOpacity}
            />
          </DebtLayer>

          {/* Subtle description labels below each layer */}
          <div
            style={{
              position: "absolute",
              top: lowerLayerTop + lowerLayerHeight + 12,
              left: unifiedLeft,
              width: unifiedWidth,
              display: "flex",
              justifyContent: "center",
              opacity: labelOpacity * 0.7,
            }}
          >
            <span
              style={{
                fontFamily: LABEL_FONT_FAMILY,
                fontSize: 13,
                color: CODE_COMPLEXITY_COLOR,
                opacity: 0.7,
                letterSpacing: "0.03em",
              }}
            >
              spaghetti code · dependency tangles · unclear interfaces
            </span>
          </div>

          <div
            style={{
              position: "absolute",
              top: upperLayerTop - 28,
              left: unifiedLeft,
              width: unifiedWidth,
              display: "flex",
              justifyContent: "center",
              opacity: labelOpacity * 0.7,
            }}
          >
            <span
              style={{
                fontFamily: LABEL_FONT_FAMILY,
                fontSize: 13,
                color: CONTEXT_ROT_COLOR,
                opacity: 0.7,
                letterSpacing: "0.03em",
              }}
            >
              model performance degrades as codebase exceeds context window
            </span>
          </div>

          {/* Divider line between the two layers (visible rule) */}
          <div
            style={{
              position: "absolute",
              top: lowerLayerTop - LAYER_GAP / 2 - 1,
              left: unifiedLeft + 40,
              width: unifiedWidth - 80,
              height: 2,
              backgroundColor: "#FFFFFF",
              opacity: gapOpacity * 0.7,
              borderRadius: 1,
            }}
          />
        </AbsoluteFill>
      )}

      {/* ── Title overlay: visible throughout ── */}
      <Sequence from={0}>
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: 0,
            width: CANVAS_WIDTH,
            display: "flex",
            justifyContent: "center",
          }}
        >
          <div
            style={{
              fontFamily: LABEL_FONT_FAMILY,
              fontSize: 20,
              fontWeight: 600,
              color: "#FFFFFF",
              opacity: interpolate(frame, [0, 20], [0, 0.8], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }),
              letterSpacing: "0.08em",
              textTransform: "uppercase",
            }}
          >
            Two Kinds of Technical Debt
          </div>
        </div>
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics06DebtLayersZoom;
