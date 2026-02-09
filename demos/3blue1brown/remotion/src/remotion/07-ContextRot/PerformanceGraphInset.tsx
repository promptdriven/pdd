import React from "react";
import { Easing, interpolate, useCurrentFrame } from "remotion";
import { BEATS, COLORS } from "./constants";

interface PerformanceGraphInsetProps {
  opacity?: number;
}

export const PerformanceGraphInset: React.FC<PerformanceGraphInsetProps> = ({
  opacity = 1,
}) => {
  const frame = useCurrentFrame();

  // Fade in animation
  const fadeInProgress = interpolate(
    frame,
    [BEATS.RETURN_TO_CHART_START, BEATS.RETURN_TO_CHART_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Fade out animation
  const fadeOutProgress = interpolate(
    frame,
    [BEATS.RETURN_TO_CHART_START + 90 - 20, BEATS.RETURN_TO_CHART_START + 90],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const insetOpacity = Math.min(fadeInProgress, fadeOutProgress) * opacity;

  // Inset dimensions and position
  const insetWidth = 420;
  const insetHeight = 280;
  const insetX = 80;
  const insetY = 100;

  // Graph area within inset
  const graphMargin = { top: 50, right: 20, bottom: 45, left: 50 };
  const graphWidth = insetWidth - graphMargin.left - graphMargin.right;
  const graphHeight = insetHeight - graphMargin.top - graphMargin.bottom;

  // Performance degradation data points (context length vs performance)
  // Based on "14-85% degradation as context grows"
  const dataPoints = [
    { contextLength: 0, performance: 100 },     // Baseline
    { contextLength: 20, performance: 95 },     // -5%
    { contextLength: 40, performance: 86 },     // -14% (lower bound cited)
    { contextLength: 60, performance: 65 },     // Mid-range degradation
    { contextLength: 80, performance: 30 },     // Upper degradation
    { contextLength: 100, performance: 15 },    // -85% (upper bound cited)
  ];

  // Helper to get X position for context length (0-100%)
  const getX = (contextLength: number) => {
    return graphMargin.left + (contextLength / 100) * graphWidth;
  };

  // Helper to get Y position for performance (0-100%)
  const getY = (performance: number) => {
    return graphMargin.top + graphHeight - (performance / 100) * graphHeight;
  };

  // Build path for the performance line
  const buildPerformancePath = () => {
    let path = `M ${getX(dataPoints[0].contextLength)} ${getY(dataPoints[0].performance)}`;
    for (let i = 1; i < dataPoints.length; i++) {
      // Use smooth curves for more professional look
      const prevPoint = dataPoints[i - 1];
      const currentPoint = dataPoints[i];
      const controlX = getX((prevPoint.contextLength + currentPoint.contextLength) / 2);
      path += ` Q ${controlX} ${getY(prevPoint.performance)}, ${getX(currentPoint.contextLength)} ${getY(currentPoint.performance)}`;
    }
    return path;
  };

  // Animate line drawing
  const lineDrawProgress = interpolate(
    frame,
    [BEATS.RETURN_TO_CHART_START + 15, BEATS.RETURN_TO_CHART_START + 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: insetX,
        top: insetY,
        width: insetWidth,
        height: insetHeight,
        opacity: insetOpacity,
        backgroundColor: "rgba(26, 26, 46, 0.95)",
        borderRadius: 12,
        border: `2px solid ${COLORS.IRRELEVANT_CODE}60`,
        boxShadow: "0 4px 20px rgba(0, 0, 0, 0.6)",
        overflow: "hidden",
      }}
    >
      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 12,
          left: graphMargin.left,
          right: graphMargin.right,
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 16,
          fontWeight: 600,
          color: COLORS.TITLE,
          textAlign: "center",
        }}
      >
        Performance vs. Context Length
      </div>

      {/* Graph SVG */}
      <svg
        width={insetWidth}
        height={insetHeight}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          {/* Gradient for area under curve */}
          <linearGradient id="perfGradient" x1="0%" y1="0%" x2="0%" y2="100%">
            <stop offset="0%" stopColor={COLORS.IRRELEVANT_CODE} stopOpacity={0.4} />
            <stop offset="100%" stopColor={COLORS.IRRELEVANT_CODE} stopOpacity={0.05} />
          </linearGradient>

          {/* Glow filter for line */}
          <filter id="perfLineGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur in="SourceGraphic" stdDeviation="3" result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>

          {/* Mask for line draw animation */}
          <mask id="lineDrawMask">
            <rect
              x={0}
              y={0}
              width={graphMargin.left + graphWidth * lineDrawProgress}
              height={insetHeight}
              fill="white"
            />
          </mask>
        </defs>

        {/* Grid lines */}
        {[0, 25, 50, 75, 100].map((value) => (
          <line
            key={`h-${value}`}
            x1={graphMargin.left}
            y1={getY(value)}
            x2={graphMargin.left + graphWidth}
            y2={getY(value)}
            stroke={COLORS.GRID}
            strokeWidth={1}
            strokeDasharray="3,3"
            opacity={0.3}
          />
        ))}

        {/* Area under curve */}
        <path
          d={`${buildPerformancePath()} L ${getX(100)} ${getY(0)} L ${getX(0)} ${getY(0)} Z`}
          fill="url(#perfGradient)"
          mask="url(#lineDrawMask)"
        />

        {/* Performance line */}
        <path
          d={buildPerformancePath()}
          fill="none"
          stroke={COLORS.IRRELEVANT_CODE}
          strokeWidth={3}
          strokeLinecap="round"
          filter="url(#perfLineGlow)"
          mask="url(#lineDrawMask)"
        />

        {/* Data points */}
        {dataPoints.map((point, i) => {
          const pointOpacity = lineDrawProgress >= point.contextLength / 100 ? 1 : 0;
          return (
            <circle
              key={`point-${i}`}
              cx={getX(point.contextLength)}
              cy={getY(point.performance)}
              r={4}
              fill={COLORS.IRRELEVANT_CODE}
              opacity={pointOpacity}
            />
          );
        })}

        {/* Y-axis labels */}
        <text
          x={graphMargin.left - 10}
          y={getY(100)}
          textAnchor="end"
          alignmentBaseline="middle"
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 11,
            fill: COLORS.AXIS_LABEL,
          }}
        >
          100%
        </text>
        <text
          x={graphMargin.left - 10}
          y={getY(50)}
          textAnchor="end"
          alignmentBaseline="middle"
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 11,
            fill: COLORS.AXIS_LABEL,
          }}
        >
          50%
        </text>
        <text
          x={graphMargin.left - 10}
          y={getY(0)}
          textAnchor="end"
          alignmentBaseline="middle"
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 11,
            fill: COLORS.AXIS_LABEL,
          }}
        >
          0%
        </text>

        {/* X-axis labels */}
        <text
          x={getX(0)}
          y={graphMargin.top + graphHeight + 20}
          textAnchor="middle"
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 11,
            fill: COLORS.AXIS_LABEL,
          }}
        >
          Small
        </text>
        <text
          x={getX(100)}
          y={graphMargin.top + graphHeight + 20}
          textAnchor="middle"
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 11,
            fill: COLORS.AXIS_LABEL,
          }}
        >
          Large
        </text>

        {/* Axis label */}
        <text
          x={graphMargin.left + graphWidth / 2}
          y={insetHeight - 8}
          textAnchor="middle"
          style={{
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 10,
            fill: COLORS.AXIS_LABEL,
            opacity: 0.7,
          }}
        >
          Context Length →
        </text>
      </svg>

      {/* Citation */}
      <div
        style={{
          position: "absolute",
          bottom: 8,
          left: 12,
          right: 12,
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 10,
          fontStyle: "italic",
          color: "rgba(255, 255, 255, 0.6)",
          textAlign: "center",
          lineHeight: 1.3,
        }}
      >
        Even with perfect retrieval, performance degrades 14-85%
        <br />
        as context grows (EMNLP, 2025)
      </div>
    </div>
  );
};
