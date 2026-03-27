import React from "react";
import { interpolate, Easing } from "remotion";
import {
  INSET_WIDTH,
  INSET_HEIGHT,
  INSET_BG_COLOR,
  INSET_BORDER_COLOR,
  INSET_BORDER_RADIUS,
  TITLE_COLOR,
  AXIS_LABEL_COLOR,
  DEGRADATION_LABEL_COLOR,
  CHART_LEFT,
  CHART_TOP,
  CHART_RIGHT,
  CHART_BOTTOM,
  CHART_PLOT_WIDTH,
  CHART_PLOT_HEIGHT,
  PERFORMANCE_DATA,
  Y_TICKS,
  PHASE_INSET_FILL_START,
  PHASE_INSET_FILL_END,
  PHASE_LINE_DRAW_START,
  PHASE_LABELS_START,
} from "./constants";

/**
 * The inset performance-vs-context chart.
 * Includes border draw-in, background fill, title, axes, and labels.
 * The animated line is rendered by AnimatedLine (composed externally).
 */

interface InsetChartProps {
  /** Offset frame within the inset's local timeline */
  localFrame: number;
  children?: React.ReactNode;
}

export const InsetChart: React.FC<InsetChartProps> = ({
  localFrame,
  children,
}) => {
  // ── Border draw-in (0 → 60 frames, easeOut quad) ──────────────────
  const borderProgress = interpolate(localFrame, [0, 60], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // ── Background fill (60 → 90 frames) ──────────────────────────────
  const bgOpacity = interpolate(
    localFrame,
    [PHASE_INSET_FILL_START, PHASE_INSET_FILL_END],
    [0, 0.95],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // ── Title type-in (60 → 90 frames) ────────────────────────────────
  const titleText = "Performance vs. Context Length";
  const titleProgress = interpolate(
    localFrame,
    [PHASE_INSET_FILL_START, PHASE_INSET_FILL_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );
  const visibleChars = Math.floor(titleProgress * titleText.length);

  // ── Axes draw-in (90 → 120 frames) ────────────────────────────────
  const axesProgress = interpolate(
    localFrame,
    [PHASE_LINE_DRAW_START, PHASE_LINE_DRAW_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Labels fade-in (210 → 230 frames) ─────────────────────────────
  const labelsOpacity = interpolate(
    localFrame,
    [PHASE_LABELS_START, PHASE_LABELS_START + 20],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Border perimeter for the drawing effect
  const perimeterLength = 2 * (INSET_WIDTH + INSET_HEIGHT);

  return (
    <div
      style={{
        position: "relative",
        width: INSET_WIDTH,
        height: INSET_HEIGHT,
      }}
    >
      {/* Border draw-in via SVG */}
      <svg
        width={INSET_WIDTH}
        height={INSET_HEIGHT}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <rect
          x={0.5}
          y={0.5}
          width={INSET_WIDTH - 1}
          height={INSET_HEIGHT - 1}
          rx={INSET_BORDER_RADIUS}
          ry={INSET_BORDER_RADIUS}
          fill="none"
          stroke={INSET_BORDER_COLOR}
          strokeWidth={1}
          strokeDasharray={perimeterLength}
          strokeDashoffset={perimeterLength * (1 - borderProgress)}
        />
      </svg>

      {/* Background fill */}
      <div
        style={{
          position: "absolute",
          top: 1,
          left: 1,
          width: INSET_WIDTH - 2,
          height: INSET_HEIGHT - 2,
          backgroundColor: INSET_BG_COLOR,
          opacity: bgOpacity,
          borderRadius: INSET_BORDER_RADIUS - 1,
        }}
      />

      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 12,
          left: 16,
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 600,
          color: TITLE_COLOR,
          opacity: titleProgress,
          whiteSpace: "nowrap",
        }}
      >
        {titleText.slice(0, visibleChars)}
        {visibleChars < titleText.length && (
          <span style={{ opacity: 0.5 }}>|</span>
        )}
      </div>

      {/* Axes */}
      <svg
        width={INSET_WIDTH}
        height={INSET_HEIGHT}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Y-axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP}
          x2={CHART_LEFT}
          y2={CHART_TOP + CHART_PLOT_HEIGHT * axesProgress}
          stroke={AXIS_LABEL_COLOR}
          strokeWidth={1}
          opacity={0.5}
        />
        {/* X-axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_LEFT + CHART_PLOT_WIDTH * axesProgress}
          y2={CHART_BOTTOM}
          stroke={AXIS_LABEL_COLOR}
          strokeWidth={1}
          opacity={0.5}
        />

        {/* Y-axis ticks */}
        {Y_TICKS.map((tick) => {
          const tickY = CHART_BOTTOM - tick.value * CHART_PLOT_HEIGHT;
          return (
            <g key={tick.label} opacity={axesProgress}>
              <line
                x1={CHART_LEFT - 4}
                y1={tickY}
                x2={CHART_LEFT}
                y2={tickY}
                stroke={AXIS_LABEL_COLOR}
                strokeWidth={1}
                opacity={0.4}
              />
              {/* Grid line */}
              <line
                x1={CHART_LEFT}
                y1={tickY}
                x2={CHART_RIGHT}
                y2={tickY}
                stroke={AXIS_LABEL_COLOR}
                strokeWidth={0.5}
                opacity={0.15}
                strokeDasharray="4 4"
              />
              <text
                x={CHART_LEFT - 8}
                y={tickY + 3}
                textAnchor="end"
                fontFamily="Inter, sans-serif"
                fontSize={10}
                fill={AXIS_LABEL_COLOR}
                opacity={0.7}
              >
                {tick.label}
              </text>
            </g>
          );
        })}

        {/* X-axis labels */}
        {PERFORMANCE_DATA.map((dp) => {
          const tickX = CHART_LEFT + dp.x * CHART_PLOT_WIDTH;
          return (
            <g key={dp.label} opacity={axesProgress}>
              <line
                x1={tickX}
                y1={CHART_BOTTOM}
                x2={tickX}
                y2={CHART_BOTTOM + 4}
                stroke={AXIS_LABEL_COLOR}
                strokeWidth={1}
                opacity={0.4}
              />
              <text
                x={tickX}
                y={CHART_BOTTOM + 16}
                textAnchor="middle"
                fontFamily="Inter, sans-serif"
                fontSize={11}
                fill={AXIS_LABEL_COLOR}
              >
                {dp.label}
              </text>
            </g>
          );
        })}

        {/* Axis titles */}
        <text
          x={CHART_LEFT + CHART_PLOT_WIDTH / 2}
          y={CHART_BOTTOM + 32}
          textAnchor="middle"
          fontFamily="Inter, sans-serif"
          fontSize={11}
          fill={AXIS_LABEL_COLOR}
          opacity={axesProgress * 0.8}
        >
          Context length (tokens)
        </text>
        <text
          x={12}
          y={CHART_TOP + CHART_PLOT_HEIGHT / 2}
          textAnchor="middle"
          fontFamily="Inter, sans-serif"
          fontSize={11}
          fill={AXIS_LABEL_COLOR}
          opacity={axesProgress * 0.8}
          transform={`rotate(-90, 12, ${CHART_TOP + CHART_PLOT_HEIGHT / 2})`}
        >
          Model Performance
        </text>
      </svg>

      {/* Animated line (passed as children) */}
      {children}

      {/* Degradation labels */}
      <div
        style={{
          position: "absolute",
          bottom: 48,
          right: 20,
          opacity: labelsOpacity,
          textAlign: "right",
        }}
      >
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 12,
            color: DEGRADATION_LABEL_COLOR,
            opacity: 0.85,
          }}
        >
          14-85% degradation
        </div>
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 11,
            color: AXIS_LABEL_COLOR,
            marginTop: 2,
          }}
        >
          (EMNLP, 2025)
        </div>
      </div>
    </div>
  );
};

export default InsetChart;
