import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  X_TICKS,
  Y_TICKS,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  GRID_COLOR,
  FONT_FAMILY,
} from "./constants";

/** Map a data-space x value to pixel x. */
export const xToPixel = (x: number): number =>
  CHART_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

/** Map a data-space y value to pixel y (inverted — higher y = higher on screen). */
export const yToPixel = (y: number): number =>
  CHART_BOTTOM - ((y - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade-in the whole chart over the first 60 frames
  const chartOpacity = interpolate(frame, [0, 60], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  return (
    <div style={{ position: "absolute", inset: 0, opacity: chartOpacity }}>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* ── Grid lines ─────────────────────────────── */}
        {Y_TICKS.map((tick) => {
          const py = yToPixel(tick);
          return (
            <line
              key={`grid-y-${tick}`}
              x1={CHART_LEFT}
              y1={py}
              x2={CHART_RIGHT}
              y2={py}
              stroke={GRID_COLOR}
              strokeWidth={1}
            />
          );
        })}
        {X_TICKS.map((tick) => {
          const px = xToPixel(tick);
          return (
            <line
              key={`grid-x-${tick}`}
              x1={px}
              y1={CHART_TOP}
              x2={px}
              y2={CHART_BOTTOM}
              stroke={GRID_COLOR}
              strokeWidth={1}
            />
          );
        })}

        {/* ── Axes ────────────────────────────────────── */}
        {/* X axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_RIGHT}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={2}
        />
        {/* Y axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP}
          x2={CHART_LEFT}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={2}
        />

        {/* ── X-axis labels ──────────────────────────── */}
        {X_TICKS.map((tick) => (
          <text
            key={`xlabel-${tick}`}
            x={xToPixel(tick)}
            y={CHART_BOTTOM + 32}
            textAnchor="middle"
            fill={AXIS_LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={14}
            fontWeight={400}
          >
            {tick}
          </text>
        ))}

        {/* ── Y-axis labels ──────────────────────────── */}
        {Y_TICKS.map((tick) => (
          <text
            key={`ylabel-${tick}`}
            x={CHART_LEFT - 16}
            y={yToPixel(tick) + 5}
            textAnchor="end"
            fill={AXIS_LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={13}
            fontWeight={400}
          >
            {tick.toFixed(1)}
          </text>
        ))}

        {/* ── Axis titles ────────────────────────────── */}
        <text
          x={CHART_LEFT + CHART_WIDTH / 2}
          y={CHART_BOTTOM + 64}
          textAnchor="middle"
          fill={AXIS_LABEL_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={15}
          fontWeight={500}
        >
          Year
        </text>
        <text
          x={CHART_LEFT - 60}
          y={CHART_TOP + CHART_HEIGHT / 2}
          textAnchor="middle"
          fill={AXIS_LABEL_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={15}
          fontWeight={500}
          transform={`rotate(-90, ${CHART_LEFT - 60}, ${CHART_TOP + CHART_HEIGHT / 2})`}
        >
          Relative Cost per Feature
        </text>

        {/* ── Chart title ────────────────────────────── */}
        <text
          x={CHART_LEFT + CHART_WIDTH / 2}
          y={CHART_TOP - 32}
          textAnchor="middle"
          fill="#E2E8F0"
          fontFamily={FONT_FAMILY}
          fontSize={22}
          fontWeight={700}
        >
          Code Cost: Generate vs. Patch
        </text>
      </svg>
    </div>
  );
};

export default ChartAxes;
