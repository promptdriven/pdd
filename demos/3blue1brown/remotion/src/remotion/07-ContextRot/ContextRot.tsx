import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { DebtLayerSeparation } from "./DebtLayerSeparation";
import { ContextWindowVisualization } from "./ContextWindowVisualization";
import { SplitViewMismatch } from "./SplitViewMismatch";
import {
  COLORS,
  BEATS,
  ContextRotPropsType,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
} from "./constants";

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

  // Build simplified chart lines for part 3
  const buildGeneratePath = () => {
    const points = [
      { year: 2015, hours: 2.5 },
      { year: 2020, hours: 1.5 },
      { year: 2023, hours: 0.8 },
      { year: 2030, hours: 0.05 },
    ];
    let path = `M ${getXPosition(points[0].year)} ${getYPosition(points[0].hours)}`;
    for (let i = 1; i < points.length; i++) {
      path += ` L ${getXPosition(points[i].year)} ${getYPosition(points[i].hours)}`;
    }
    return path;
  };

  const buildPatchPath = () => {
    return `M ${getXPosition(2015)} ${getYPosition(0.8)} L ${getXPosition(2030)} ${getYPosition(0.8)}`;
  };

  // Build debt region path for part 3
  const buildDebtPath = () => {
    const crossingYear = 2023.5;
    return `
      M ${getXPosition(crossingYear)} ${getYPosition(0.8)}
      L ${getXPosition(2030)} ${getYPosition(0.05)}
      L ${getXPosition(2030)} ${getYPosition(0.8)}
      Z
    `;
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

      {/* Part 2b: Split View Mismatch (frames 900-1020) */}
      {isPart2Split && (
        <SplitViewMismatch />
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
            </defs>

            {/* Grid lines */}
            {[2016, 2020, 2024, 2028].map((year) => (
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

            {/* Debt region with context rot pulse */}
            <path
              d={buildDebtPath()}
              fill={COLORS.CONTEXT_ROT}
              fillOpacity={0.4 * contextRotPulse}
              filter="url(#contextRotGlow)"
            />

            {/* Cost to patch line */}
            <path
              d={buildPatchPath()}
              fill="none"
              stroke={COLORS.LINE_PATCH}
              strokeWidth={4}
              strokeLinecap="round"
            />

            {/* Cost to generate line with pulse */}
            <path
              d={buildGeneratePath()}
              fill="none"
              stroke={COLORS.LINE_GENERATE}
              strokeWidth={5}
              strokeLinecap="round"
              opacity={generateLinePulse + 0.5}
              filter={frame >= BEATS.SETUP_SOLUTION_START ? "url(#generateGlow)" : undefined}
            />
          </svg>

          {/* Year labels */}
          {[2015, 2020, 2025, 2030].map((year) => (
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
              Faster patching = faster growth = faster rot
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
              Regeneration: always starts small, always fits
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
              gap: 12,
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
                }}
              />
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 16,
                  color: "rgba(255, 255, 255, 0.9)",
                }}
              >
                Cost to Patch
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
