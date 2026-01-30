import React from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import {
  BEATS,
  COLORS,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  CHART_DATA,
  interpolateHours,
} from "./constants";

interface DebtLayerSeparationProps {
  opacity?: number;
}

export const DebtLayerSeparation: React.FC<DebtLayerSeparationProps> = ({
  opacity = 1,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

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

  // Build SVG path from data points
  const buildPath = (data: { year: number; hours: number }[]) => {
    let path = `M ${getXPosition(data[0].year)} ${getYPosition(data[0].hours)}`;
    for (let i = 1; i < data.length; i++) {
      path += ` L ${getXPosition(data[i].year)} ${getYPosition(data[i].hours)}`;
    }
    return path;
  };

  // Zoom progress (0-60 frames)
  const zoomProgress = interpolate(
    frame,
    [BEATS.ZOOM_INTO_DEBT_START, BEATS.ZOOM_INTO_DEBT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Fade non-focus elements (generate, small CB) to 20% during zoom
  const focusFadeOpacity = interpolate(
    frame,
    [BEATS.ZOOM_INTO_DEBT_START, BEATS.ZOOM_INTO_DEBT_END],
    [1, 0.2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Background grid/axes fade
  const backgroundOpacity = interpolate(
    frame,
    [BEATS.ZOOM_INTO_DEBT_START, BEATS.ZOOM_INTO_DEBT_END],
    [1, 0.2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Layer separation progress (60-150 frames)
  const separationProgress = interpolate(
    frame,
    [BEATS.LAYER_SEPARATION_START, BEATS.LAYER_SEPARATION_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Label fade in after separation completes
  const labelOpacity = interpolate(
    frame,
    [BEATS.LAYER_SEPARATION_END, BEATS.LAYER_SEPARATION_END + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Build full debt area path between large CB immediate and total cost (2020-2025)
  const buildFullDebtPath = () => {
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

  // Build half of debt area (top = Context Rot, bottom = Code Complexity)
  const buildDebtHalfPath = (isTop: boolean, separation: number) => {
    const startYear = 2020;
    const endYear = 2025;
    const steps = 20;
    const offset = isTop ? -separation : separation;

    const getTopY = (year: number) => {
      const totalHours = interpolateHours(CHART_DATA.totalCostLargeCodebase, year);
      const immHours = interpolateHours(CHART_DATA.immediateCostLargeCodebase, year);
      const midHours = (totalHours + immHours) / 2;
      return isTop ? getYPosition(totalHours) : getYPosition(midHours);
    };

    const getBottomY = (year: number) => {
      const totalHours = interpolateHours(CHART_DATA.totalCostLargeCodebase, year);
      const immHours = interpolateHours(CHART_DATA.immediateCostLargeCodebase, year);
      const midHours = (totalHours + immHours) / 2;
      return isTop ? getYPosition(midHours) : getYPosition(immHours);
    };

    // Top edge left to right
    let path = `M ${getXPosition(startYear)} ${getTopY(startYear) + offset}`;
    for (let i = 1; i <= steps; i++) {
      const year = startYear + (endYear - startYear) * (i / steps);
      path += ` L ${getXPosition(year)} ${getTopY(year) + offset}`;
    }
    // Bottom edge right to left
    for (let i = steps; i >= 0; i--) {
      const year = startYear + (endYear - startYear) * (i / steps);
      path += ` L ${getXPosition(year)} ${getBottomY(year) + offset}`;
    }
    path += " Z";
    return path;
  };

  // Zoom center: center of the debt area (~year 2022.5, ~21 hours)
  const zoomCenterX = getXPosition(2022.5);
  const zoomCenterY = getYPosition(21);

  // Max separation between the two layers (in pixels)
  const maxSeparation = 30;
  const separation = separationProgress * maxSeparation;

  // Label positions
  const debtCenterX = getXPosition(2022.5);
  const totalAtCenter = interpolateHours(CHART_DATA.totalCostLargeCodebase, 2022.5);
  const immAtCenter = interpolateHours(CHART_DATA.immediateCostLargeCodebase, 2022.5);
  const midHours = (totalAtCenter + immAtCenter) / 2;

  const codeComplexityLabelY =
    (getYPosition(midHours) + getYPosition(immAtCenter)) / 2 + separation;
  const contextRotLabelY =
    (getYPosition(totalAtCenter) + getYPosition(midHours)) / 2 - separation;

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        opacity,
        transform: `scale(${1 + zoomProgress * 0.5})`,
        transformOrigin: `${zoomCenterX}px ${zoomCenterY}px`,
      }}
    >
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <defs>
          {/* Animated noise for context rot texture */}
          <filter id="animatedNoise">
            <feTurbulence
              type="fractalNoise"
              baseFrequency="0.05"
              numOctaves="3"
              seed={Math.floor(frame / 3)}
              result="noise"
            />
            <feColorMatrix
              type="matrix"
              values="0 0 0 0 0
                      0 0 0 0 0
                      0 0 0 0 0
                      0 0 0 0.15 0"
            />
            <feBlend in="SourceGraphic" mode="overlay" />
          </filter>

          {/* Glow effect for layers */}
          <filter id="layerGlow" x="-20%" y="-20%" width="140%" height="140%">
            <feGaussianBlur in="SourceGraphic" stdDeviation="4" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Background grid */}
        <g opacity={backgroundOpacity}>
          {/* Vertical grid lines */}
          {[2016, 2018, 2020, 2022, 2024].map((year) => (
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

          {/* Horizontal grid lines */}
          {[0, 5, 10, 15, 20, 25, 30, 35].map((hours) => (
            <line
              key={`h-grid-${hours}`}
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
        </g>

        {/* Generate line — fades to 20% during zoom */}
        <path
          d={buildPath(CHART_DATA.costToGenerate)}
          fill="none"
          stroke={COLORS.LINE_GENERATE}
          strokeWidth={3}
          strokeLinecap="round"
          opacity={focusFadeOpacity}
        />

        {/* Baseline immediate cost (pre-fork) — fades to 20% */}
        <path
          d={buildPath(CHART_DATA.immediateCostBaseline)}
          fill="none"
          stroke={COLORS.LINE_PATCH}
          strokeWidth={3}
          strokeLinecap="round"
          opacity={focusFadeOpacity}
        />

        {/* Small codebase fork — fades to 20% during zoom */}
        <path
          d={buildPath(CHART_DATA.immediateCostSmallCodebase)}
          fill="none"
          stroke={COLORS.LINE_PATCH}
          strokeWidth={3}
          strokeLinecap="round"
          opacity={focusFadeOpacity}
        />

        {/* Large codebase fork — stays visible */}
        <path
          d={buildPath(CHART_DATA.immediateCostLargeCodebase)}
          fill="none"
          stroke={COLORS.LINE_PATCH}
          strokeWidth={3}
          strokeLinecap="round"
          opacity={0.7}
        />

        {/* Total cost large codebase (dashed) — stays visible */}
        <path
          d={buildPath(CHART_DATA.totalCostLargeCodebase)}
          fill="none"
          stroke={COLORS.LINE_PATCH}
          strokeWidth={3}
          strokeLinecap="round"
          strokeDasharray="12,6"
          opacity={0.8}
        />

        {/* Full debt area (fades out during separation) */}
        <path
          d={buildFullDebtPath()}
          fill={COLORS.CODE_COMPLEXITY}
          fillOpacity={0.35 * (1 - separationProgress)}
        />

        {/* Separated layers (fade in during separation) */}
        {separationProgress > 0 && (
          <>
            {/* Bottom layer: Code Complexity */}
            <path
              d={buildDebtHalfPath(false, separation)}
              fill={COLORS.CODE_COMPLEXITY}
              fillOpacity={0.4 * separationProgress}
              filter="url(#layerGlow)"
            />
            <path
              d={buildDebtHalfPath(false, separation)}
              fill="none"
              stroke={COLORS.CODE_COMPLEXITY}
              strokeWidth={2}
              strokeDasharray="8,4"
              opacity={0.6 * separationProgress}
            />

            {/* Top layer: Context Rot with noise texture */}
            <g filter="url(#animatedNoise)">
              <path
                d={buildDebtHalfPath(true, separation)}
                fill={COLORS.CONTEXT_ROT}
                fillOpacity={0.5 * separationProgress}
              />
            </g>
            <path
              d={buildDebtHalfPath(true, separation)}
              fill="none"
              stroke={COLORS.CONTEXT_ROT}
              strokeWidth={2}
              opacity={0.7 * separationProgress}
            />
          </>
        )}
      </svg>

      {/* Labels for the layers */}
      {labelOpacity > 0 && (
        <>
          {/* Code Complexity label */}
          <div
            style={{
              position: "absolute",
              left: debtCenterX,
              top: codeComplexityLabelY,
              transform: "translate(-50%, -50%)",
              opacity: labelOpacity,
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 22,
              fontWeight: 600,
              color: COLORS.CODE_COMPLEXITY,
              textShadow: "0 2px 10px rgba(0,0,0,0.8)",
              whiteSpace: "nowrap",
              padding: "8px 16px",
              backgroundColor: "rgba(26, 26, 46, 0.85)",
              borderRadius: 6,
              border: `1px solid ${COLORS.CODE_COMPLEXITY}`,
            }}
          >
            Code Complexity
          </div>

          {/* Context Rot label */}
          <div
            style={{
              position: "absolute",
              left: debtCenterX,
              top: contextRotLabelY,
              transform: "translate(-50%, -50%)",
              opacity: labelOpacity,
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 22,
              fontWeight: 600,
              color: COLORS.CONTEXT_ROT,
              textShadow: "0 2px 10px rgba(0,0,0,0.8)",
              whiteSpace: "nowrap",
              padding: "8px 16px",
              backgroundColor: "rgba(26, 26, 46, 0.85)",
              borderRadius: 6,
              border: `1px solid ${COLORS.CONTEXT_ROT}`,
            }}
          >
            Context Rot
          </div>
        </>
      )}
    </div>
  );
};
