import React from "react";
import { interpolate, Easing } from "remotion";
import {
  DEBT_AREA_COLOR,
  CYCLE_ANNOTATION_COLOR,
  AXIS_LABEL_COLOR,
  TITLE_COLOR,
  DEBT_CHART_LEFT,
  DEBT_CHART_TOP,
  DEBT_CHART_WIDTH,
  DEBT_CHART_HEIGHT,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

interface DebtAreaChartProps {
  /** Global frame offset (starts at phase 7 = frame 720) */
  localFrame: number;
}

/**
 * Simplified "code cost chart" with a pulsing "Context Rot" debt area
 * and the "Faster patching → faster growth → faster rot" annotation.
 */
export const DebtAreaChart: React.FC<DebtAreaChartProps> = ({ localFrame }) => {
  // ── Fade in the chart (transition from inset fade-out) ─────────────
  const chartOpacity = interpolate(localFrame, [0, 60], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // ── Context Rot pulse (45-frame cycle, easeInOut sine) ─────────────
  const pulseCycle = (localFrame % 45) / 45;
  const pulseIntensity = interpolate(
    pulseCycle,
    [0, 0.5, 1],
    [0.15, 0.45, 0.15],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // ── Annotation fade-in (starts at 810 global = localFrame 90) ──────
  const annotationOpacity = interpolate(
    localFrame,
    [90, 110],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Chart layout
  const chartLeft = DEBT_CHART_LEFT;
  const chartTop = DEBT_CHART_TOP;
  const chartW = DEBT_CHART_WIDTH;
  const chartH = DEBT_CHART_HEIGHT;
  const chartRight = chartLeft + chartW;
  const chartBottom = chartTop + chartH;

  // Simulated cost line (rising curve)
  const costLinePoints = Array.from({ length: 50 }, (_, i) => {
    const t = i / 49;
    const x = chartLeft + t * chartW;
    const y = chartBottom - (0.1 + 0.6 * Math.pow(t, 1.8)) * chartH;
    return { x, y };
  });
  const costPath = costLinePoints
    .map((p, i) => `${i === 0 ? "M" : "L"} ${p.x} ${p.y}`)
    .join(" ");

  // Debt area: gap between the cost line and a baseline
  const baselinePoints = Array.from({ length: 50 }, (_, i) => {
    const t = i / 49;
    const x = chartLeft + t * chartW;
    const y = chartBottom - (0.05 + 0.2 * t) * chartH;
    return { x, y };
  });

  // Build the debt area polygon
  const debtAreaPath =
    costLinePoints.map((p, i) => `${i === 0 ? "M" : "L"} ${p.x} ${p.y}`).join(" ") +
    " " +
    [...baselinePoints].reverse().map((p) => `L ${p.x} ${p.y}`).join(" ") +
    " Z";

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        opacity: chartOpacity,
      }}
    >
      <svg width={CANVAS_WIDTH} height={CANVAS_HEIGHT}>
        {/* Axes */}
        <line
          x1={chartLeft}
          y1={chartTop}
          x2={chartLeft}
          y2={chartBottom}
          stroke={AXIS_LABEL_COLOR}
          strokeWidth={1}
          opacity={0.4}
        />
        <line
          x1={chartLeft}
          y1={chartBottom}
          x2={chartRight}
          y2={chartBottom}
          stroke={AXIS_LABEL_COLOR}
          strokeWidth={1}
          opacity={0.4}
        />

        {/* Y-axis label */}
        <text
          x={chartLeft - 50}
          y={chartTop + chartH / 2}
          textAnchor="middle"
          fontFamily="Inter, sans-serif"
          fontSize={13}
          fill={AXIS_LABEL_COLOR}
          opacity={0.7}
          transform={`rotate(-90, ${chartLeft - 50}, ${chartTop + chartH / 2})`}
        >
          Cumulative Cost
        </text>

        {/* X-axis label */}
        <text
          x={chartLeft + chartW / 2}
          y={chartBottom + 40}
          textAnchor="middle"
          fontFamily="Inter, sans-serif"
          fontSize={13}
          fill={AXIS_LABEL_COLOR}
          opacity={0.7}
        >
          Time (months)
        </text>

        {/* Debt area (pulsing) */}
        <path
          d={debtAreaPath}
          fill={DEBT_AREA_COLOR}
          opacity={pulseIntensity}
        />

        {/* Debt area border */}
        <path
          d={debtAreaPath}
          fill="none"
          stroke={DEBT_AREA_COLOR}
          strokeWidth={1.5}
          opacity={0.4 + pulseIntensity}
        />

        {/* Cost line */}
        <path
          d={costPath}
          fill="none"
          stroke="#60A5FA"
          strokeWidth={2}
          opacity={0.8}
        />

        {/* Baseline */}
        <path
          d={baselinePoints
            .map((p, i) => `${i === 0 ? "M" : "L"} ${p.x} ${p.y}`)
            .join(" ")}
          fill="none"
          stroke="#94A3B8"
          strokeWidth={1.5}
          strokeDasharray="6 4"
          opacity={0.5}
        />

        {/* Context Rot label on the debt area */}
        <text
          x={chartLeft + chartW * 0.65}
          y={chartBottom - chartH * 0.35}
          textAnchor="middle"
          fontFamily="Inter, sans-serif"
          fontSize={16}
          fontWeight={600}
          fill={DEBT_AREA_COLOR}
          opacity={0.6 + pulseIntensity * 0.8}
        >
          Context Rot
        </text>
      </svg>

      {/* Chart title */}
      <div
        style={{
          position: "absolute",
          top: chartTop - 50,
          left: chartLeft,
          fontFamily: "Inter, sans-serif",
          fontSize: 20,
          fontWeight: 600,
          color: TITLE_COLOR,
          opacity: 0.9,
        }}
      >
        Code Maintenance Cost Over Time
      </div>

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          top: chartTop - 20,
          right: CANVAS_WIDTH - chartRight,
          display: "flex",
          gap: 20,
          fontFamily: "Inter, sans-serif",
          fontSize: 12,
          color: AXIS_LABEL_COLOR,
        }}
      >
        <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
          <div
            style={{
              width: 16,
              height: 3,
              backgroundColor: "#60A5FA",
              borderRadius: 1,
            }}
          />
          Actual Cost
        </div>
        <div style={{ display: "flex", alignItems: "center", gap: 6 }}>
          <div
            style={{
              width: 16,
              height: 3,
              backgroundColor: DEBT_AREA_COLOR,
              borderRadius: 1,
            }}
          />
          Technical Debt
        </div>
      </div>

      {/* Cycle annotation */}
      <div
        style={{
          position: "absolute",
          bottom: CANVAS_HEIGHT - chartBottom + 70,
          left: chartLeft + chartW * 0.4,
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontStyle: "italic",
          color: CYCLE_ANNOTATION_COLOR,
          opacity: annotationOpacity,
          textShadow: "0 0 12px rgba(245, 158, 11, 0.3)",
        }}
      >
        Faster patching → faster growth → faster rot
      </div>
    </div>
  );
};

export default DebtAreaChart;
