import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  LABOR_COST_DATA,
  GARMENT_COST_DATA,
  LABOR_COLOR,
  GARMENT_COLOR,
  LINE_STROKE_WIDTH,
  TOTAL_FRAMES,
  MORPH_START,
  MORPH_END,
  FONT_FAMILY,
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
} from "./constants";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { CrossingHighlight } from "./CrossingHighlight";

export const defaultPart1Economics02SockPriceChartProps = {};

/**
 * Section 1.2: Sock Price vs. Labor Cost Chart
 *
 * An animated line chart showing the economic threshold that killed darning.
 * Two lines — labor cost (amber) and garment cost (blue) — cross around 1963,
 * marking the moment darning became economically irrational.
 *
 * Duration: 720 frames (24s @ 30fps)
 */
export const Part1Economics02SockPriceChart: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Chart title fade-in (visible from frame 0) ─────────────
  const titleOpacity = interpolate(frame, [0, 20], [0.6, 0.9], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Legend fade-in (after lines start) ─────────────────────
  const legendOpacity = interpolate(frame, [40, 70], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Morph/fade out transition (frame 600-720) ─────────────
  const morphFadeLabor = interpolate(
    frame,
    [MORPH_START, MORPH_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );
  const morphFadeGarment = interpolate(
    frame,
    [MORPH_START + 40, MORPH_END],
    [1, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: FONT_FAMILY,
      }}
    >
      {/* Chart title — visible immediately */}
      <div
        style={{
          position: "absolute",
          top: 30,
          left: CHART_LEFT,
          right: 1920 - CHART_RIGHT,
          textAlign: "center",
          color: "#E2E8F0",
          fontSize: 24,
          fontWeight: 700,
          fontFamily: FONT_FAMILY,
          opacity: titleOpacity,
          letterSpacing: "0.02em",
        }}
      >
        Sock Price vs. Labor Cost
      </div>

      {/* Axes and grid — start drawing from frame 0 */}
      <ChartAxes />

      {/* Legend box */}
      <div
        style={{
          position: "absolute",
          top: CHART_TOP + 10,
          right: 1920 - CHART_RIGHT + 30,
          display: "flex",
          flexDirection: "column",
          gap: 8,
          opacity: legendOpacity,
        }}
      >
        <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
          <div
            style={{
              width: 24,
              height: 3,
              backgroundColor: LABOR_COLOR,
              borderRadius: 2,
            }}
          />
          <span
            style={{
              color: LABOR_COLOR,
              fontSize: 13,
              fontWeight: 500,
              fontFamily: FONT_FAMILY,
            }}
          >
            Labor cost
          </span>
        </div>
        <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
          <div
            style={{
              width: 24,
              height: 3,
              backgroundColor: GARMENT_COLOR,
              borderRadius: 2,
            }}
          />
          <span
            style={{
              color: GARMENT_COLOR,
              fontSize: 13,
              fontWeight: 500,
              fontFamily: FONT_FAMILY,
            }}
          >
            Garment cost
          </span>
        </div>
      </div>

      {/* Animated lines — both start at frame 30 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div style={{ opacity: morphFadeLabor }}>
          <AnimatedLine
            data={LABOR_COST_DATA}
            color={LABOR_COLOR}
            strokeWidth={LINE_STROKE_WIDTH}
            label="Labor cost"
          />
        </div>
        <div style={{ opacity: morphFadeGarment }}>
          <AnimatedLine
            data={GARMENT_COST_DATA}
            color={GARMENT_COLOR}
            strokeWidth={LINE_STROKE_WIDTH}
            label="Garment cost"
          />
        </div>
      </Sequence>

      {/* Crossing point highlight + zone labels */}
      <CrossingHighlight />

      {/* Subtitle overlay area — narration sync hints */}
      {frame >= 0 && frame < 60 && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: 0,
            right: 0,
            textAlign: "center",
            color: "#E2E8F0",
            fontSize: 20,
            fontWeight: 500,
            fontFamily: FONT_FAMILY,
            opacity: interpolate(frame, [0, 10, 50, 60], [0, 0.88, 0.88, 0], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
            textShadow: "0 2px 8px rgba(0,0,0,0.6)",
          }}
        >
          This isn't nostalgia. It's economics.
        </div>
      )}

      {frame >= 60 && frame < 250 && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: 100,
            right: 100,
            textAlign: "center",
            color: "#E2E8F0",
            fontSize: 19,
            fontWeight: 400,
            fontFamily: FONT_FAMILY,
            opacity: interpolate(
              frame,
              [60, 75, 235, 250],
              [0, 0.82, 0.82, 0],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            textShadow: "0 2px 8px rgba(0,0,0,0.6)",
            lineHeight: 1.5,
          }}
        >
          In 1950, a wool sock cost real money relative to an hour of labor.
          <br />
          Darning made sense. You'd spend thirty minutes to save a dollar.
        </div>
      )}

      {frame >= 250 && frame < 500 && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: 100,
            right: 100,
            textAlign: "center",
            color: "#E2E8F0",
            fontSize: 19,
            fontWeight: 400,
            fontFamily: FONT_FAMILY,
            opacity: interpolate(
              frame,
              [250, 270, 480, 500],
              [0, 0.82, 0.82, 0],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            textShadow: "0 2px 8px rgba(0,0,0,0.6)",
            lineHeight: 1.5,
          }}
        >
          By the mid-1960s, the math flipped. A new sock cost less than the
          <br />
          time to repair the old one. Darning became irrational.
        </div>
      )}

      {/* Transition vignette during morph phase */}
      {frame >= MORPH_START && (
        <div
          style={{
            position: "absolute",
            inset: 0,
            background: `radial-gradient(ellipse at center, transparent 40%, ${BG_COLOR} 100%)`,
            opacity: interpolate(frame, [MORPH_START, MORPH_END], [0, 0.5], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
          }}
        />
      )}
    </AbsoluteFill>
  );
};

export default Part1Economics02SockPriceChart;
