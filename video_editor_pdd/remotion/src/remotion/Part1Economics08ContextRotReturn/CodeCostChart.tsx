import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

// All constants inlined to avoid cross-file imports per spec requirement

const CHART_LEFT = 120;
const CHART_RIGHT = 1800;
const CHART_TOP = 100;
const CHART_BOTTOM = 800;
const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

const GRID_COLOR = "#1E293B";
const GRID_OPACITY = 0.06;
const AXIS_COLOR = "#475569";
const IDEAL_LINE_COLOR = "#22C55E";
const ACTUAL_LINE_COLOR = "#EF4444";
const DEBT_FILL_START = "rgba(239, 68, 68, 0.08)";
const DEBT_FILL_END = "rgba(239, 68, 68, 0.25)";

/**
 * Simplified code cost chart showing ideal vs actual cost curves,
 * with the "debt" area between them shaded.
 * The Context Rot layer sits in the upper portion of the debt area.
 */
const CodeCostChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Chart data: idealY and actualY as functions of normalized x [0,1]
  const sampleCount = 60;
  const idealPoints: string[] = [];
  const actualPoints: string[] = [];
  const debtPolygonPoints: string[] = [];

  for (let i = 0; i <= sampleCount; i++) {
    const t = i / sampleCount;
    const x = CHART_LEFT + t * CHART_WIDTH;

    // Ideal: gentle upward slope (linear-ish)
    const idealY = CHART_BOTTOM - (t * 0.3 + 0.05) * CHART_HEIGHT;

    // Actual: accelerating curve (debt grows)
    const actualY =
      CHART_BOTTOM -
      (t * 0.3 + 0.05 + Math.pow(t, 2.2) * 0.45) * CHART_HEIGHT;

    idealPoints.push(`${x},${idealY}`);
    actualPoints.push(`${x},${actualY}`);
  }

  // Build debt polygon (area between ideal and actual)
  const debtTop: string[] = [];
  const debtBottom: string[] = [];
  for (let i = 0; i <= sampleCount; i++) {
    const t = i / sampleCount;
    const x = CHART_LEFT + t * CHART_WIDTH;
    const idealY = CHART_BOTTOM - (t * 0.3 + 0.05) * CHART_HEIGHT;
    const actualY =
      CHART_BOTTOM -
      (t * 0.3 + 0.05 + Math.pow(t, 2.2) * 0.45) * CHART_HEIGHT;
    debtTop.push(`${x},${actualY}`);
    debtBottom.unshift(`${x},${idealY}`);
  }
  const debtPath = [...debtTop, ...debtBottom].join(" ");

  // Grid lines
  const hGridCount = 6;
  const vGridCount = 10;

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
      }}
    >
      <svg width={1920} height={1080}>
        {/* Horizontal grid lines */}
        {Array.from({ length: hGridCount + 1 }).map((_, i) => {
          const y = CHART_TOP + (i / hGridCount) * CHART_HEIGHT;
          return (
            <line
              key={`hgrid-${i}`}
              x1={CHART_LEFT}
              y1={y}
              x2={CHART_RIGHT}
              y2={y}
              stroke={GRID_COLOR}
              strokeOpacity={GRID_OPACITY}
              strokeWidth={1}
            />
          );
        })}

        {/* Vertical grid lines */}
        {Array.from({ length: vGridCount + 1 }).map((_, i) => {
          const x = CHART_LEFT + (i / vGridCount) * CHART_WIDTH;
          return (
            <line
              key={`vgrid-${i}`}
              x1={x}
              y1={CHART_TOP}
              x2={x}
              y2={CHART_BOTTOM}
              stroke={GRID_COLOR}
              strokeOpacity={GRID_OPACITY}
              strokeWidth={1}
            />
          );
        })}

        {/* Debt gradient */}
        <defs>
          <linearGradient
            id="debtGradient"
            x1="0"
            y1="0"
            x2="1"
            y2="0"
          >
            <stop offset="0%" stopColor={DEBT_FILL_START} />
            <stop offset="100%" stopColor={DEBT_FILL_END} />
          </linearGradient>
        </defs>

        {/* Debt area (shaded between curves) */}
        <polygon
          points={debtPath}
          fill="url(#debtGradient)"
        />

        {/* Axes */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_RIGHT}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={2}
        />
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP}
          x2={CHART_LEFT}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={2}
        />

        {/* Ideal cost line */}
        <polyline
          points={idealPoints.join(" ")}
          fill="none"
          stroke={IDEAL_LINE_COLOR}
          strokeWidth={2.5}
          strokeOpacity={0.7}
        />

        {/* Actual cost line */}
        <polyline
          points={actualPoints.join(" ")}
          fill="none"
          stroke={ACTUAL_LINE_COLOR}
          strokeWidth={2.5}
          strokeOpacity={0.85}
        />

        {/* Axis labels */}
        <text
          x={CHART_LEFT + CHART_WIDTH / 2}
          y={CHART_BOTTOM + 50}
          textAnchor="middle"
          fill="#94A3B8"
          fontSize={14}
          fontFamily="Inter, sans-serif"
        >
          Project Timeline
        </text>
        <text
          x={CHART_LEFT - 50}
          y={CHART_TOP + CHART_HEIGHT / 2}
          textAnchor="middle"
          fill="#94A3B8"
          fontSize={14}
          fontFamily="Inter, sans-serif"
          transform={`rotate(-90, ${CHART_LEFT - 50}, ${CHART_TOP + CHART_HEIGHT / 2})`}
        >
          Cost per Change
        </text>

        {/* "Context Rot" label on the debt area */}
        <text
          x={CHART_LEFT + CHART_WIDTH * 0.7}
          y={CHART_TOP + CHART_HEIGHT * 0.45}
          textAnchor="middle"
          fill="#EF4444"
          fontSize={18}
          fontWeight={600}
          fontFamily="Inter, sans-serif"
          opacity={0.85}
        >
          Context Rot
        </text>

        {/* Legend items */}
        <circle cx={CHART_RIGHT - 250} cy={CHART_TOP + 20} r={5} fill={IDEAL_LINE_COLOR} />
        <text
          x={CHART_RIGHT - 238}
          y={CHART_TOP + 25}
          fill="#94A3B8"
          fontSize={12}
          fontFamily="Inter, sans-serif"
        >
          Ideal cost
        </text>
        <circle cx={CHART_RIGHT - 250} cy={CHART_TOP + 44} r={5} fill={ACTUAL_LINE_COLOR} />
        <text
          x={CHART_RIGHT - 238}
          y={CHART_TOP + 49}
          fill="#94A3B8"
          fontSize={12}
          fontFamily="Inter, sans-serif"
        >
          Actual cost
        </text>
      </svg>
    </div>
  );
};

export default CodeCostChart;
