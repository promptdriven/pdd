import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { DebtLayerSeparation } from "./DebtLayerSeparation";
import { ContextWindowVisualization } from "./ContextWindowVisualization";
import { SplitViewMismatch } from "./SplitViewMismatch";
import { InGridMismatch } from "./InGridMismatch";
import { PerformanceGraphInset } from "./PerformanceGraphInset";
import {
  COLORS,
  BEATS,
  ContextRotPropsType,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  CHART_DATA,
  interpolateHours,
} from "./constants";

// Toggle between split-screen and in-grid mismatch visualization
// Set to true for spec-compliant in-grid approach, false for split-screen comparison
const USE_IN_GRID_MISMATCH = true;

export const ContextRot: React.FC<ContextRotPropsType> = ({
  showTitle = true,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // Determine which phase we're in
  const isPart1 = frame < BEATS.MORPH_TO_GRID_START; // 0-300: Debt layers
  const isPart2 = frame >= BEATS.MORPH_TO_GRID_START && frame < BEATS.SPLIT_VIEW_START; // 300-900: Context window
  const isPart2Split = frame >= BEATS.SPLIT_VIEW_START && frame < BEATS.RETURN_TO_CHART_START; // 900-1020: Split view
  const isPart3Chart = frame >= BEATS.RETURN_TO_CHART_START; // 1020-1350: Return to chart

  // Phase transition opacities
  const part1Opacity = interpolate(
    frame,
    [BEATS.MORPH_TO_GRID_START - 60, BEATS.MORPH_TO_GRID_START],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const part2Opacity = interpolate(
    frame,
    [BEATS.MORPH_TO_GRID_START, BEATS.MORPH_TO_GRID_END, BEATS.SPLIT_VIEW_START - 30, BEATS.SPLIT_VIEW_START],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const part3ChartOpacity = interpolate(
    frame,
    [BEATS.RETURN_TO_CHART_START, BEATS.RETURN_TO_CHART_END - 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Title animation
  const titleOpacity = interpolate(
    frame,
    [0, 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Get current title based on phase
  const getCurrentTitle = () => {
    if (frame < BEATS.MORPH_TO_GRID_START) {
      return "Context Rot: The AI-Specific Problem";
    } else if (frame < BEATS.SPLIT_VIEW_START) {
      return ""; // ContextWindowVisualization has its own title
    } else if (frame < BEATS.RETURN_TO_CHART_START) {
      return ""; // SplitViewMismatch has its own title
    } else {
      return "The Consequence";
    }
  };

  // Helper functions for chart positioning
  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  const getXPosition = (year: number) => {
    return (
      CHART_MARGINS.left +
      ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth
    );
  };

  const getYPosition = (hours: number) => {
    return (
      CHART_MARGINS.top +
      chartHeight -
      (hours / HOURS_RANGE.max) * chartHeight
    );
  };

  // Context rot pulse in part 3
  const contextRotPulse = frame >= BEATS.RETURN_TO_CHART_START
    ? Math.sin((frame - BEATS.RETURN_TO_CHART_START) * 0.1) * 0.3 + 0.7
    : 1;

  // Generate line pulse in solution setup
  const generateLinePulse = frame >= BEATS.SETUP_SOLUTION_START
    ? Math.sin((frame - BEATS.SETUP_SOLUTION_START) * 0.15) * 0.3 + 0.7
    : 0.5;

  // Annotation fade in for part 3
  const annotation1Opacity = interpolate(
    frame,
    [BEATS.RETURN_TO_CHART_END - 30, BEATS.RETURN_TO_CHART_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const annotation2Opacity = interpolate(
    frame,
    [BEATS.SETUP_SOLUTION_START + 30, BEATS.SETUP_SOLUTION_START + 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Build SVG path from data points
  const buildLinePath = (data: { year: number; hours: number }[]) => {
    let path = `M ${getXPosition(data[0].year)} ${getYPosition(data[0].hours)}`;
    for (let i = 1; i < data.length; i++) {
      path += ` L ${getXPosition(data[i].year)} ${getYPosition(data[i].hours)}`;
    }
    return path;
  };

  // Build debt area path between large CB immediate and total cost (2020-2025)
  const buildDebtAreaPath = () => {
    const startYear = 2020;
    const endYear = 2025;
    const steps = 20;

    // Top edge (total cost) left to right
    let path = `M ${getXPosition(startYear)} ${getYPosition(interpolateHours(CHART_DATA.totalCostLargeCodebase, startYear))}`;
    for (let i = 1; i <= steps; i++) {
      const year = startYear + (endYear - startYear) * (i / steps);
      path += ` L ${getXPosition(year)} ${getYPosition(interpolateHours(CHART_DATA.totalCostLargeCodebase, year))}`;
    }
    // Bottom edge (large CB immediate) right to left
    for (let i = steps; i >= 0; i--) {
      const year = startYear + (endYear - startYear) * (i / steps);
      path += ` L ${getXPosition(year)} ${getYPosition(interpolateHours(CHART_DATA.immediateCostLargeCodebase, year))}`;
    }
    path += " Z";
    return path;
  };

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* Part 1: Debt Layer Separation (frames 0-300) */}
      {isPart1 && part1Opacity > 0 && (
        <DebtLayerSeparation opacity={part1Opacity} />
      )}

      {/* Part 2: Context Window Visualization (frames 300-900) */}
      {(isPart2 || part2Opacity > 0) && frame >= BEATS.MORPH_TO_GRID_START && frame < BEATS.SPLIT_VIEW_START && (
        <div style={{ opacity: part2Opacity }}>
          <ContextWindowVisualization />
        </div>
      )}

      {/* Part 2b: Context Mismatch Visualization (frames 900-1020) */}
      {isPart2Split && (
        USE_IN_GRID_MISMATCH ? <InGridMismatch /> : <SplitViewMismatch />
      )}

      {/* Part 3: Return to Chart (frames 1020-1350) */}
      {isPart3Chart && part3ChartOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: "100%",
            height: "100%",
            opacity: part3ChartOpacity,
          }}
        >
          {/* Performance Graph Inset (frames 1020-1110) */}
          {frame >= BEATS.RETURN_TO_CHART_START && frame < BEATS.RETURN_TO_CHART_START + 90 && (
            <PerformanceGraphInset opacity={part3ChartOpacity} />
          )}
          {/* Chart SVG */}
          <svg
            width={width}
            height={height}
            style={{ position: "absolute", top: 0, left: 0 }}
          >
            <defs>
              {/* Glow filters */}
              <filter id="generateGlow" x="-30%" y="-30%" width="160%" height="160%">
                <feGaussianBlur in="SourceGraphic" stdDeviation="6" result="blur" />
                <feMerge>
                  <feMergeNode in="blur" />
                  <feMergeNode in="SourceGraphic" />
                </feMerge>
              </filter>

              <filter id="contextRotGlow" x="-20%" y="-20%" width="140%" height="140%">
                <feGaussianBlur in="SourceGraphic" stdDeviation="4" result="blur" />
                <feMerge>
                  <feMergeNode in="blur" />
                  <feMergeNode in="SourceGraphic" />
                </feMerge>
              </filter>

              <filter id="smallCBGlow" x="-30%" y="-30%" width="160%" height="160%">
                <feGaussianBlur in="SourceGraphic" stdDeviation="5" result="blur" />
                <feMerge>
                  <feMergeNode in="blur" />
                  <feMergeNode in="SourceGraphic" />
                </feMerge>
              </filter>
            </defs>

            {/* Vertical grid lines */}
            {[2016, 2018, 2020, 2022, 2024].map((year) => (
              <line
                key={`v-${year}`}
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

            {/* Horizontal grid lines */}
            {[0, 5, 10, 15, 20, 25, 30, 35].map((hours) => (
              <line
                key={`h-${hours}`}
                x1={CHART_MARGINS.left}
                y1={getYPosition(hours)}
                x2={width - CHART_MARGINS.right}
                y2={getYPosition(hours)}
                stroke={COLORS.GRID}
                strokeWidth={1}
                strokeDasharray="5,5"
                opacity={0.3}
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

            {/* Tech debt area with context rot pulse */}
            <path
              d={buildDebtAreaPath()}
              fill={COLORS.CONTEXT_ROT}
              fillOpacity={0.4 * contextRotPulse}
              filter="url(#contextRotGlow)"
            />

            {/* Cost to Generate line with pulse */}
            <path
              d={buildLinePath(CHART_DATA.costToGenerate)}
              fill="none"
              stroke={COLORS.LINE_GENERATE}
              strokeWidth={5}
              strokeLinecap="round"
              opacity={generateLinePulse + 0.5}
              filter={frame >= BEATS.SETUP_SOLUTION_START ? "url(#generateGlow)" : undefined}
            />

            {/* Baseline immediate cost (pre-fork) */}
            <path
              d={buildLinePath(CHART_DATA.immediateCostBaseline)}
              fill="none"
              stroke={COLORS.LINE_PATCH}
              strokeWidth={3}
              strokeLinecap="round"
              opacity={0.5}
            />

            {/* Small codebase fork — faint glow */}
            <path
              d={buildLinePath(CHART_DATA.immediateCostSmallCodebase)}
              fill="none"
              stroke={COLORS.LINE_PATCH}
              strokeWidth={3}
              strokeLinecap="round"
              opacity={0.4}
              filter="url(#smallCBGlow)"
            />

            {/* Large codebase fork */}
            <path
              d={buildLinePath(CHART_DATA.immediateCostLargeCodebase)}
              fill="none"
              stroke={COLORS.LINE_PATCH}
              strokeWidth={3}
              strokeLinecap="round"
              opacity={0.7}
            />

            {/* Total cost large codebase (dashed) */}
            <path
              d={buildLinePath(CHART_DATA.totalCostLargeCodebase)}
              fill="none"
              stroke={COLORS.LINE_PATCH}
              strokeWidth={3}
              strokeLinecap="round"
              strokeDasharray="12,6"
              opacity={0.8}
            />
          </svg>

          {/* Year labels */}
          {[2015, 2020, 2025].map((year) => (
            <div
              key={`year-${year}`}
              style={{
                position: "absolute",
                left: getXPosition(year),
                top: height - CHART_MARGINS.bottom + 20,
                transform: "translateX(-50%)",
                fontFamily: "Inter, system-ui, sans-serif",
                fontSize: 24,
                fontWeight: 500,
                color: COLORS.AXIS_LABEL,
              }}
            >
              {year}
            </div>
          ))}

          {/* Annotation 1: "Faster patching = faster growth = faster rot" */}
          {annotation1Opacity > 0 && (
            <div
              style={{
                position: "absolute",
                top: height / 2 - 50,
                right: CHART_MARGINS.right + 40,
                opacity: annotation1Opacity,
                fontFamily: "Inter, system-ui, sans-serif",
                fontSize: 22,
                fontWeight: 600,
                color: COLORS.CONTEXT_ROT,
                textShadow: "0 2px 10px rgba(0,0,0,0.8)",
                padding: "12px 20px",
                backgroundColor: "rgba(26, 26, 46, 0.9)",
                borderRadius: 8,
                border: `2px solid ${COLORS.CONTEXT_ROT}60`,
                maxWidth: 280,
                textAlign: "center",
              }}
            >
              Faster patching → faster growth → faster rot
            </div>
          )}

          {/* Annotation 2: "Regeneration: always starts small, always fits" */}
          {annotation2Opacity > 0 && (
            <div
              style={{
                position: "absolute",
                bottom: CHART_MARGINS.bottom + 80,
                left: CHART_MARGINS.left + chartWidth / 3,
                opacity: annotation2Opacity,
                fontFamily: "Inter, system-ui, sans-serif",
                fontSize: 22,
                fontWeight: 600,
                color: COLORS.LINE_GENERATE,
                textShadow: "0 2px 10px rgba(0,0,0,0.8)",
                padding: "12px 20px",
                backgroundColor: "rgba(26, 26, 46, 0.9)",
                borderRadius: 8,
                border: `2px solid ${COLORS.LINE_GENERATE}60`,
                maxWidth: 350,
                textAlign: "center",
              }}
            >
              Small modules. Clear prompts. Always fits in context.
            </div>
          )}

          {/* Legend */}
          <div
            style={{
              position: "absolute",
              top: 120,
              right: 60,
              display: "flex",
              flexDirection: "column",
              gap: 10,
              padding: "16px 20px",
              backgroundColor: "rgba(26, 26, 46, 0.8)",
              borderRadius: 8,
            }}
          >
            <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
              <div
                style={{
                  width: 30,
                  height: 4,
                  backgroundColor: COLORS.LINE_GENERATE,
                  borderRadius: 2,
                }}
              />
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 16,
                  color: "rgba(255, 255, 255, 0.9)",
                }}
              >
                Cost to Generate
              </span>
            </div>
            <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
              <div
                style={{
                  width: 30,
                  height: 4,
                  backgroundColor: COLORS.LINE_PATCH,
                  borderRadius: 2,
                  opacity: 0.7,
                }}
              />
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 16,
                  color: "rgba(255, 255, 255, 0.9)",
                }}
              >
                Patch (Small CB)
              </span>
            </div>
            <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
              <div
                style={{
                  width: 30,
                  height: 4,
                  backgroundColor: COLORS.LINE_PATCH,
                  borderRadius: 2,
                  opacity: 0.5,
                }}
              />
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 16,
                  color: "rgba(255, 255, 255, 0.7)",
                }}
              >
                Patch (Large CB)
              </span>
            </div>
            <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
              <div
                style={{
                  width: 30,
                  height: 4,
                  borderRadius: 2,
                  background: `repeating-linear-gradient(90deg, ${COLORS.LINE_PATCH} 0px, ${COLORS.LINE_PATCH} 6px, transparent 6px, transparent 10px)`,
                }}
              />
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 16,
                  color: "rgba(255, 255, 255, 0.9)",
                }}
              >
                True Cost (with tech debt)
              </span>
            </div>
            <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
              <div
                style={{
                  width: 20,
                  height: 20,
                  backgroundColor: COLORS.CONTEXT_ROT,
                  opacity: 0.5,
                  borderRadius: 4,
                }}
              />
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 16,
                  color: "rgba(255, 255, 255, 0.9)",
                }}
              >
                Context Rot
              </span>
            </div>
          </div>
        </div>
      )}

      {/* Title (only shown in Part 1 and Part 3) */}
      {showTitle && getCurrentTitle() && (
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
          {getCurrentTitle()}
        </div>
      )}
    </AbsoluteFill>
  );
};
