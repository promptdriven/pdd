import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  AXIS_COLOR,
  LABEL_COLOR,
  CHART_LEFT,
  CHART_TOP,
  CHART_RIGHT,
  CHART_BOTTOM,
  AXES_DURATION,
  FONT_FAMILY,
  AXIS_TICK_FONT_SIZE,
  AXIS_TITLE_FONT_SIZE,
  X_TICKS,
  X_MIN,
  X_MAX,
  CHART_WIDTH,
} from "./constants";

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(frame, [0, AXES_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const labelOpacity = interpolate(frame, [10, AXES_DURATION], [0, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // X-axis draws from left to right
  const xAxisEndX = CHART_LEFT + (CHART_RIGHT - CHART_LEFT) * drawProgress;
  // Y-axis draws from bottom to top
  const yAxisEndY = CHART_BOTTOM - (CHART_BOTTOM - CHART_TOP) * drawProgress;

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* X-axis line */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={xAxisEndX}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={1.5}
        />

        {/* Y-axis line */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_LEFT}
          y2={yAxisEndY}
          stroke={AXIS_COLOR}
          strokeWidth={1.5}
        />

        {/* X-axis tick labels */}
        {X_TICKS.map((tick) => {
          const xPos =
            CHART_LEFT + ((tick - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
          const tickLabel = tick === 50 ? "50+" : String(tick);
          return (
            <g key={`xtick-${tick}`} opacity={labelOpacity}>
              <line
                x1={xPos}
                y1={CHART_BOTTOM}
                x2={xPos}
                y2={CHART_BOTTOM + 6}
                stroke={AXIS_COLOR}
                strokeWidth={1}
              />
              <text
                x={xPos}
                y={CHART_BOTTOM + 24}
                textAnchor="middle"
                fill={LABEL_COLOR}
                fontFamily={FONT_FAMILY}
                fontSize={AXIS_TICK_FONT_SIZE}
                fontWeight={400}
              >
                {tickLabel}
              </text>
            </g>
          );
        })}

        {/* Y-axis tick labels: "Low" at bottom, "High" at top */}
        <g opacity={labelOpacity}>
          <text
            x={CHART_LEFT - 16}
            y={CHART_BOTTOM - 10}
            textAnchor="end"
            fill={LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={AXIS_TICK_FONT_SIZE}
            fontWeight={400}
          >
            Low
          </text>
          <text
            x={CHART_LEFT - 16}
            y={CHART_TOP + 16}
            textAnchor="end"
            fill={LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={AXIS_TICK_FONT_SIZE}
            fontWeight={400}
          >
            High
          </text>
        </g>

        {/* X-axis title */}
        <text
          x={(CHART_LEFT + CHART_RIGHT) / 2}
          y={CHART_BOTTOM + 56}
          textAnchor="middle"
          fill={LABEL_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={AXIS_TITLE_FONT_SIZE}
          fontWeight={600}
          opacity={labelOpacity}
        >
          Number of Tests
        </text>

        {/* Y-axis title (rotated) */}
        <text
          x={CHART_LEFT - 70}
          y={(CHART_TOP + CHART_BOTTOM) / 2}
          textAnchor="middle"
          fill={LABEL_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={AXIS_TITLE_FONT_SIZE}
          fontWeight={600}
          opacity={labelOpacity}
          transform={`rotate(-90, ${CHART_LEFT - 70}, ${(CHART_TOP + CHART_BOTTOM) / 2})`}
        >
          Required Prompt Precision
        </text>
      </svg>
    </AbsoluteFill>
  );
};
