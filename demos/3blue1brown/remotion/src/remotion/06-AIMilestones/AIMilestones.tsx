import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { MilestoneMarker } from "./MilestoneMarker";
import {
  COLORS,
  CHART_MARGINS,
  YEAR_RANGE,
  COST_RANGE,
  COST_DATA,
  MILESTONES,
  BEATS,
  AIMilestonesPropsType,
} from "./constants";

export const AIMilestones: React.FC<AIMilestonesPropsType> = ({
  showTitle = true,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  // Zoom animation progress
  const zoomProgress = interpolate(
    frame,
    [BEATS.ZOOM_START, BEATS.ZOOM_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Background elements fade to 30% during zoom
  const backgroundOpacity = interpolate(
    frame,
    [BEATS.ZOOM_START, BEATS.ZOOM_END],
    [1, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Helper functions for positioning
  const getXPosition = (year: number) => {
    return (
      CHART_MARGINS.left +
      ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth
    );
  };

  const getYPosition = (cost: number) => {
    return (
      CHART_MARGINS.top +
      chartHeight -
      (cost / COST_RANGE.max) * chartHeight
    );
  };

  // Get Y position on the cost curve for a given year
  const getCostAtYear = (year: number): number => {
    // Find the two data points that bracket this year
    for (let i = 0; i < COST_DATA.length - 1; i++) {
      if (year >= COST_DATA[i].year && year <= COST_DATA[i + 1].year) {
        const t = (year - COST_DATA[i].year) / (COST_DATA[i + 1].year - COST_DATA[i].year);
        return COST_DATA[i].cost + t * (COST_DATA[i + 1].cost - COST_DATA[i].cost);
      }
    }
    return COST_DATA[COST_DATA.length - 1].cost;
  };

  // Build the cost line path
  const buildCostLinePath = () => {
    if (COST_DATA.length < 2) return "";

    let path = `M ${getXPosition(COST_DATA[0].year)} ${getYPosition(COST_DATA[0].cost)}`;
    for (let i = 1; i < COST_DATA.length; i++) {
      path += ` L ${getXPosition(COST_DATA[i].year)} ${getYPosition(COST_DATA[i].cost)}`;
    }
    return path;
  };

  // Line draw animation
  const lineDrawProgress = interpolate(
    frame,
    [BEATS.ZOOM_END, BEATS.ZOOM_END + 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Calculate milestone positions with staggered label placement
  const getMilestoneY = (year: number) => {
    const cost = getCostAtYear(year);
    return getYPosition(cost);
  };

  // Assign label positions to avoid overlap
  const getLabelPosition = (index: number): "top" | "bottom" | "left" | "right" => {
    // Alternate between top and bottom for visual balance
    // Special handling for the three 2023 models
    const positions: ("top" | "bottom" | "left" | "right")[] = [
      "top",     // GPT-3 (2020)
      "top",     // Codex (2021)
      "top",     // GPT-4 (2023)
      "bottom",  // Claude (2023)
      "right",   // Gemini (2023)
    ];
    return positions[index] || "top";
  };

  const getLabelOffsetY = (index: number): number => {
    // Add vertical offset for 2023 models to avoid collision
    const offsets = [0, 0, -15, 15, 0];
    return offsets[index] || 0;
  };

  // Year ticks for x-axis
  const yearTicks = [2020, 2021, 2022, 2023, 2024];

  // Title fade in
  const titleOpacity = interpolate(
    frame,
    [0, 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* Title */}
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
            opacity: titleOpacity,
            textShadow: "0 2px 10px rgba(0,0,0,0.5)",
          }}
        >
          AI Milestones: The Acceleration
        </div>
      )}

      {/* Chart container with zoom effect */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          transform: `scale(${1 + zoomProgress * 0.15})`,
          transformOrigin: "center center",
        }}
      >
        {/* Grid and axes (fade during zoom) */}
        <svg
          width={width}
          height={height}
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            opacity: backgroundOpacity,
          }}
        >
          {/* Horizontal grid lines */}
          {[0, 30, 60, 90, 120].map((cost) => (
            <line
              key={`h-grid-${cost}`}
              x1={CHART_MARGINS.left}
              y1={getYPosition(cost)}
              x2={width - CHART_MARGINS.right}
              y2={getYPosition(cost)}
              stroke={COLORS.GRID}
              strokeWidth={1}
              strokeDasharray="5,5"
              opacity={0.5}
            />
          ))}

          {/* Vertical grid lines */}
          {yearTicks.map((year) => (
            <line
              key={`v-grid-${year}`}
              x1={getXPosition(year)}
              y1={CHART_MARGINS.top}
              x2={getXPosition(year)}
              y2={height - CHART_MARGINS.bottom}
              stroke={COLORS.GRID}
              strokeWidth={1}
              strokeDasharray="5,5"
              opacity={0.5}
            />
          ))}

          {/* X-axis */}
          <line
            x1={CHART_MARGINS.left}
            y1={height - CHART_MARGINS.bottom}
            x2={width - CHART_MARGINS.right}
            y2={height - CHART_MARGINS.bottom}
            stroke={COLORS.AXIS}
            strokeWidth={2}
          />

          {/* Y-axis */}
          <line
            x1={CHART_MARGINS.left}
            y1={CHART_MARGINS.top}
            x2={CHART_MARGINS.left}
            y2={height - CHART_MARGINS.bottom}
            stroke={COLORS.AXIS}
            strokeWidth={2}
          />
        </svg>

        {/* Axis labels (fade during zoom) */}
        <div style={{ opacity: backgroundOpacity }}>
          {/* Year labels */}
          {yearTicks.map((year) => (
            <div
              key={`year-${year}`}
              style={{
                position: "absolute",
                left: getXPosition(year),
                top: height - CHART_MARGINS.bottom + 20,
                transform: "translateX(-50%)",
                fontFamily: "Inter, system-ui, sans-serif",
                fontSize: 28,
                fontWeight: 500,
                color: COLORS.AXIS_LABEL,
              }}
            >
              {year}
            </div>
          ))}

          {/* Y-axis label */}
          <div
            style={{
              position: "absolute",
              left: 0,
              top: 0,
              width: 70,
              height: "100%",
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
            }}
          >
            <div
              style={{
                transform: "rotate(-90deg)",
                fontFamily: "Inter, system-ui, sans-serif",
                fontSize: 24,
                fontWeight: 600,
                color: COLORS.AXIS_LABEL,
                whiteSpace: "nowrap",
              }}
            >
              Cost Index (2020 = 100)
            </div>
          </div>
        </div>

        {/* The falling cost line */}
        <svg
          width={width}
          height={height}
          style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
        >
          <defs>
            {/* Gradient for the line */}
            <linearGradient id="costLineGradient" x1="0%" y1="0%" x2="100%" y2="0%">
              <stop offset="0%" stopColor={COLORS.LINE_COST} />
              <stop offset="100%" stopColor="#60A5FA" />
            </linearGradient>

            {/* Glow effect for the line */}
            <filter id="lineGlow" x="-20%" y="-20%" width="140%" height="140%">
              <feGaussianBlur in="SourceGraphic" stdDeviation="4" result="blur" />
              <feMerge>
                <feMergeNode in="blur" />
                <feMergeNode in="SourceGraphic" />
              </feMerge>
            </filter>
          </defs>

          {/* Cost line with draw animation */}
          <path
            d={buildCostLinePath()}
            fill="none"
            stroke="url(#costLineGradient)"
            strokeWidth={5}
            strokeLinecap="round"
            strokeLinejoin="round"
            strokeDasharray={2000}
            strokeDashoffset={2000 * (1 - lineDrawProgress)}
            filter="url(#lineGlow)"
          />
        </svg>

        {/* Milestone markers */}
        {MILESTONES.map((milestone, index) => (
          <MilestoneMarker
            key={milestone.id}
            x={getXPosition(milestone.year)}
            y={getMilestoneY(milestone.year)}
            name={milestone.name}
            color={milestone.color}
            startFrame={milestone.startFrame}
            labelPosition={getLabelPosition(index)}
            labelOffsetY={getLabelOffsetY(index)}
          />
        ))}
      </div>

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          top: 100,
          right: 40,
          opacity: interpolate(
            frame,
            [BEATS.RAPID_MARKERS_END, BEATS.RAPID_MARKERS_END + 30],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          ),
          backgroundColor: "rgba(0, 0, 0, 0.4)",
          padding: "16px 24px",
          borderRadius: 12,
        }}
      >
        <div
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
            fontWeight: 600,
            color: COLORS.TITLE,
            marginBottom: 12,
          }}
        >
          AI Model Releases
        </div>
        {MILESTONES.map((milestone) => (
          <div
            key={milestone.id}
            style={{
              display: "flex",
              alignItems: "center",
              marginBottom: 8,
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 16,
              fontWeight: 500,
              color: "#ffffff",
            }}
          >
            <div
              style={{
                width: 14,
                height: 14,
                borderRadius: "50%",
                backgroundColor: milestone.color,
                marginRight: 12,
                boxShadow: `0 0 8px ${milestone.color}60`,
              }}
            />
            {milestone.name} ({milestone.year})
          </div>
        ))}
      </div>

      {/* Subtitle during hold phase */}
      {frame >= BEATS.HOLD_START && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: interpolate(
              frame,
              [BEATS.HOLD_START, BEATS.HOLD_START + 30],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            textAlign: "center",
            backgroundColor: "rgba(0, 0, 0, 0.6)",
            padding: "20px 40px",
            borderRadius: 12,
          }}
        >
          <p
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 28,
              color: "#ffffff",
              textShadow: "0 2px 8px rgba(0,0,0,0.8)",
              margin: 0,
            }}
          >
            Each release accelerated the decline
          </p>
        </div>
      )}
    </AbsoluteFill>
  );
};
