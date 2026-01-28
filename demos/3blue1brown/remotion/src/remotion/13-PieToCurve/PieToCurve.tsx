import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { ExponentialCurve } from "./ExponentialCurve";
import {
  COLORS,
  BEATS,
  CHART_MARGINS,
  YEAR_RANGE,
  COST_RANGE,
  PIE_CONFIG,
  PieToCurvePropsType,
} from "./constants";

export const PieToCurve: React.FC<PieToCurvePropsType> = ({
  showLinearRef = true,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  // Chart origin position (where pie center morphs to)
  const chartOriginX = CHART_MARGINS.left;
  const chartOriginY = CHART_MARGINS.top + chartHeight;

  // === MORPH ANIMATION (Frame 0-90) ===
  // Pie chart transforms into chart origin
  const morphProgress = interpolate(
    frame,
    [BEATS.MORPH_START, BEATS.MORPH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Pie center moves to chart origin
  const pieCenterX = interpolate(
    morphProgress,
    [0, 1],
    [PIE_CONFIG.centerX, chartOriginX]
  );
  const pieCenterY = interpolate(
    morphProgress,
    [0, 1],
    [PIE_CONFIG.centerY, chartOriginY]
  );

  // Pie radius shrinks and flattens
  const pieRadiusX = interpolate(
    morphProgress,
    [0, 0.5, 1],
    [PIE_CONFIG.radius, PIE_CONFIG.radius * 1.5, 0]
  );
  const pieRadiusY = interpolate(
    morphProgress,
    [0, 0.5, 1],
    [PIE_CONFIG.radius, PIE_CONFIG.radius * 0.3, 0]
  );

  // Pie rotation during morph
  const pieRotation = interpolate(morphProgress, [0, 1], [0, 180]);

  // Pie opacity fades out
  const pieOpacity = interpolate(
    morphProgress,
    [0, 0.7, 1],
    [1, 0.5, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // === AXES ANIMATION (Frame 90-150) ===
  const axesProgress = interpolate(
    frame,
    [BEATS.AXES_START, BEATS.AXES_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // X-axis extends right
  const xAxisWidth = interpolate(axesProgress, [0, 1], [0, chartWidth]);
  // Y-axis grows upward
  const yAxisHeight = interpolate(axesProgress, [0, 1], [0, chartHeight]);

  // Grid lines fade in
  const gridOpacity = interpolate(
    frame,
    [BEATS.AXES_START + 30, BEATS.AXES_END],
    [0, 0.3],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Axis labels fade in
  const labelOpacity = interpolate(
    frame,
    [BEATS.AXES_END - 30, BEATS.AXES_END + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // === FINAL STATE (Frame 240-300) ===
  // Text fade in with easeOutCubic
  const textOpacity = interpolate(
    frame,
    [BEATS.FINAL_START + 20, BEATS.FINAL_START + 60],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Generate pie chart SVG path for the amber segment
  const generatePieSegment = (
    cx: number,
    cy: number,
    rx: number,
    ry: number,
    startAngle: number,
    endAngle: number
  ) => {
    const startRad = (startAngle * Math.PI) / 180;
    const endRad = (endAngle * Math.PI) / 180;

    const x1 = cx + rx * Math.cos(startRad);
    const y1 = cy + ry * Math.sin(startRad);
    const x2 = cx + rx * Math.cos(endRad);
    const y2 = cy + ry * Math.sin(endRad);

    const largeArc = endAngle - startAngle > 180 ? 1 : 0;

    return `M ${cx} ${cy} L ${x1} ${y1} A ${rx} ${ry} 0 ${largeArc} 1 ${x2} ${y2} Z`;
  };

  // Y-axis tick positions
  const yTicks = [0, 4, 8, 12, 16];
  const xTicks = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.BACKGROUND,
      }}
    >
      {/* === PIE CHART (morphing out) === */}
      {morphProgress < 1 && (
        <svg
          width={width}
          height={height}
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            opacity: pieOpacity,
          }}
        >
          <g transform={`rotate(${pieRotation} ${pieCenterX} ${pieCenterY})`}>
            {/* Gray segment (background) */}
            <ellipse
              cx={pieCenterX}
              cy={pieCenterY}
              rx={pieRadiusX}
              ry={pieRadiusY}
              fill={COLORS.PIE_GRAY}
            />
            {/* Amber segment (main focus - will become the curve) */}
            <path
              d={generatePieSegment(
                pieCenterX,
                pieCenterY,
                pieRadiusX,
                pieRadiusY,
                -60,
                60
              )}
              fill={COLORS.PIE_AMBER}
            />
            {/* Blue segment */}
            <path
              d={generatePieSegment(
                pieCenterX,
                pieCenterY,
                pieRadiusX,
                pieRadiusY,
                60,
                180
              )}
              fill={COLORS.PIE_BLUE}
            />
          </g>
        </svg>
      )}

      {/* === CHART AXES AND GRID === */}
      {frame >= BEATS.AXES_START && (
        <svg
          width={width}
          height={height}
          style={{ position: "absolute", top: 0, left: 0 }}
        >
          {/* Grid lines - horizontal */}
          {yTicks.map((tick) => {
            const y =
              CHART_MARGINS.top +
              chartHeight -
              (tick / COST_RANGE.max) * chartHeight;
            return (
              <line
                key={`h-grid-${tick}`}
                x1={CHART_MARGINS.left}
                y1={y}
                x2={CHART_MARGINS.left + xAxisWidth}
                y2={y}
                stroke={COLORS.GRID}
                strokeWidth={1}
                opacity={gridOpacity}
              />
            );
          })}

          {/* Grid lines - vertical */}
          {xTicks.map((tick) => {
            const x =
              CHART_MARGINS.left +
              ((tick - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) *
                chartWidth;
            const progress = x <= CHART_MARGINS.left + xAxisWidth ? 1 : 0;
            return (
              <line
                key={`v-grid-${tick}`}
                x1={x}
                y1={chartOriginY}
                x2={x}
                y2={chartOriginY - yAxisHeight}
                stroke={COLORS.GRID}
                strokeWidth={1}
                opacity={gridOpacity * progress}
              />
            );
          })}

          {/* X-axis */}
          <line
            x1={chartOriginX}
            y1={chartOriginY}
            x2={chartOriginX + xAxisWidth}
            y2={chartOriginY}
            stroke={COLORS.AXIS}
            strokeWidth={2}
          />

          {/* Y-axis */}
          <line
            x1={chartOriginX}
            y1={chartOriginY}
            x2={chartOriginX}
            y2={chartOriginY - yAxisHeight}
            stroke={COLORS.AXIS}
            strokeWidth={2}
          />

          {/* Axis arrows */}
          {axesProgress >= 1 && (
            <>
              {/* X-axis arrow */}
              <path
                d={`M ${chartOriginX + chartWidth - 10} ${chartOriginY - 6} L ${chartOriginX + chartWidth} ${chartOriginY} L ${chartOriginX + chartWidth - 10} ${chartOriginY + 6}`}
                fill="none"
                stroke={COLORS.AXIS}
                strokeWidth={2}
              />
              {/* Y-axis arrow */}
              <path
                d={`M ${chartOriginX - 6} ${CHART_MARGINS.top + 10} L ${chartOriginX} ${CHART_MARGINS.top} L ${chartOriginX + 6} ${CHART_MARGINS.top + 10}`}
                fill="none"
                stroke={COLORS.AXIS}
                strokeWidth={2}
              />
            </>
          )}
        </svg>
      )}

      {/* === AXIS LABELS === */}
      {labelOpacity > 0 && (
        <>
          {/* X-axis label */}
          <div
            style={{
              position: "absolute",
              bottom: CHART_MARGINS.bottom - 80,
              left: "50%",
              transform: "translateX(-50%)",
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 24,
              fontWeight: 500,
              color: COLORS.AXIS_LABEL,
              opacity: labelOpacity,
            }}
          >
            Time (Years 1-10)
          </div>

          {/* Y-axis label */}
          <div
            style={{
              position: "absolute",
              top: "50%",
              left: CHART_MARGINS.left - 120,
              transform: "translateY(-50%) rotate(-90deg)",
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 22,
              fontWeight: 500,
              color: COLORS.AXIS_LABEL,
              opacity: labelOpacity,
              whiteSpace: "nowrap",
            }}
          >
            Cumulative Maintenance Cost
          </div>

          {/* X-axis tick labels */}
          {xTicks.map((tick) => {
            const x =
              CHART_MARGINS.left +
              ((tick - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) *
                chartWidth;
            return (
              <div
                key={`x-label-${tick}`}
                style={{
                  position: "absolute",
                  left: x,
                  top: chartOriginY + 15,
                  transform: "translateX(-50%)",
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 18,
                  color: COLORS.AXIS_LABEL,
                  opacity: labelOpacity,
                }}
              >
                {tick}
              </div>
            );
          })}

          {/* Y-axis tick labels */}
          {yTicks.map((tick) => {
            if (tick === 0) return null;
            const y =
              CHART_MARGINS.top +
              chartHeight -
              (tick / COST_RANGE.max) * chartHeight;
            return (
              <div
                key={`y-label-${tick}`}
                style={{
                  position: "absolute",
                  left: CHART_MARGINS.left - 40,
                  top: y,
                  transform: "translateY(-50%)",
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 18,
                  color: COLORS.AXIS_LABEL,
                  opacity: labelOpacity,
                  textAlign: "right",
                  width: 30,
                }}
              >
                {tick}x
              </div>
            );
          })}
        </>
      )}

      {/* === EXPONENTIAL CURVE === */}
      {frame >= BEATS.CURVE_START && (
        <ExponentialCurve
          startFrame={BEATS.CURVE_START}
          endFrame={BEATS.CURVE_END}
          showLinearRef={showLinearRef}
          pulseStartFrame={BEATS.FINAL_START}
          pulseEndFrame={BEATS.FINAL_END}
        />
      )}

      {/* === FINAL TEXT === */}
      {frame >= BEATS.FINAL_START && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: "50%",
            transform: "translateX(-50%)",
            fontFamily: "Georgia, serif",
            fontSize: 36,
            fontStyle: "italic",
            fontWeight: 400,
            color: COLORS.TEXT,
            opacity: textOpacity,
            textShadow: "0 2px 10px rgba(0,0,0,0.7)",
            textAlign: "center",
          }}
        >
          "And those costs compound."
        </div>
      )}

      {/* === FORMULA ANNOTATION === */}
      {frame >= BEATS.CURVE_END && (
        <div
          style={{
            position: "absolute",
            top: CHART_MARGINS.top + 30,
            right: CHART_MARGINS.right - 80,
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 20,
            color: COLORS.AMBER,
            opacity: interpolate(
              frame,
              [BEATS.CURVE_END, BEATS.CURVE_END + 30],
              [0, 0.8],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            textShadow: "0 2px 8px rgba(0,0,0,0.5)",
          }}
        >
          y = 1.35^(year-1)
        </div>
      )}
    </AbsoluteFill>
  );
};
