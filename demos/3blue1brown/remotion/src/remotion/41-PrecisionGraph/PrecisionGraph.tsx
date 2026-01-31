import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, GRAPH, PrecisionGraphPropsType } from "./constants";

// Graph Axes Component
const GraphAxes: React.FC<{
  yProgress: number;
  xProgress: number;
}> = ({ yProgress, xProgress }) => {
  const { ORIGIN, Y_END, X_END } = GRAPH;

  // Calculate current Y-axis endpoint
  const yAxisCurrentY = ORIGIN.y - (ORIGIN.y - Y_END.y) * yProgress;
  // Calculate current X-axis endpoint
  const xAxisCurrentX = ORIGIN.x + (X_END.x - ORIGIN.x) * xProgress;

  return (
    <svg
      style={{
        position: "absolute",
        width: "100%",
        height: "100%",
        left: 0,
        top: 0,
      }}
    >
      {/* Y-axis */}
      <line
        x1={ORIGIN.x}
        y1={ORIGIN.y}
        x2={ORIGIN.x}
        y2={yAxisCurrentY}
        stroke={COLORS.AXIS_COLOR}
        strokeWidth={3}
      />

      {/* Y-axis arrow */}
      {yProgress >= 0.95 && (
        <polygon
          points={`${Y_END.x},${Y_END.y} ${Y_END.x - 10},${Y_END.y + 20} ${Y_END.x + 10},${Y_END.y + 20}`}
          fill={COLORS.AXIS_COLOR}
          opacity={interpolate(yProgress, [0.95, 1], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        />
      )}

      {/* X-axis */}
      <line
        x1={ORIGIN.x}
        y1={ORIGIN.y}
        x2={xAxisCurrentX}
        y2={ORIGIN.y}
        stroke={COLORS.AXIS_COLOR}
        strokeWidth={3}
      />

      {/* X-axis arrow */}
      {xProgress >= 0.95 && (
        <polygon
          points={`${X_END.x},${X_END.y} ${X_END.x - 20},${X_END.y - 10} ${X_END.x - 20},${X_END.y + 10}`}
          fill={COLORS.AXIS_COLOR}
          opacity={interpolate(xProgress, [0.95, 1], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        />
      )}
    </svg>
  );
};

// Axis Labels Component
const AxisLabels: React.FC<{ opacity: number; showRegionLabels: boolean }> = ({
  opacity,
  showRegionLabels,
}) => {
  return (
    <>
      {/* Y-axis label */}
      <div
        style={{
          position: "absolute",
          left: 30,
          top: 400,
          transform: "rotate(-90deg)",
          transformOrigin: "center",
          color: COLORS.LABEL_WHITE,
          fontSize: 28,
          fontFamily: "system-ui, sans-serif",
          fontWeight: 500,
          opacity,
          whiteSpace: "nowrap",
        }}
      >
        Required Prompt Precision
      </div>

      {/* X-axis label */}
      <div
        style={{
          position: "absolute",
          left: 900,
          bottom: 80,
          color: COLORS.LABEL_WHITE,
          fontSize: 28,
          fontFamily: "system-ui, sans-serif",
          fontWeight: 500,
          opacity,
        }}
      >
        Number of Tests
      </div>

      {/* Region labels (optional) */}
      {showRegionLabels && (
        <>
          <div
            style={{
              position: "absolute",
              left: 280,
              top: 250,
              color: COLORS.REGION_LABEL,
              fontSize: 18,
              fontFamily: "system-ui, sans-serif",
              fontWeight: 600,
              textTransform: "uppercase",
              letterSpacing: 2,
              opacity: opacity * 0.7,
            }}
          >
            Few Tests
          </div>
          <div
            style={{
              position: "absolute",
              right: 280,
              bottom: 180,
              color: COLORS.REGION_LABEL,
              fontSize: 18,
              fontFamily: "system-ui, sans-serif",
              fontWeight: 600,
              textTransform: "uppercase",
              letterSpacing: 2,
              opacity: opacity * 0.7,
            }}
          >
            Many Tests
          </div>
        </>
      )}
    </>
  );
};

// Inverse Curve Component
const InverseCurve: React.FC<{ progress: number }> = ({ progress }) => {
  const { ORIGIN, Y_END, X_END } = GRAPH;

  // Generate curve points
  const generateCurvePath = (): string => {
    const points: string[] = [];
    const numPoints = 100;
    const graphWidth = X_END.x - ORIGIN.x - 100;
    const graphHeight = ORIGIN.y - Y_END.y - 100;

    const pointsToDraw = Math.floor(numPoints * progress);

    for (let i = 0; i <= pointsToDraw; i++) {
      const t = i / numPoints;
      const x = ORIGIN.x + 50 + t * graphWidth;
      // Inverse function: y = 1 / (x + k) normalized to fit graph
      // Adjusted to create a nice curve from high-left to low-right
      const normalizedY = 1 / (t * 2.5 + 0.25);
      const y = ORIGIN.y - 50 - normalizedY * graphHeight * 0.85;

      if (i === 0) {
        points.push(`M ${x} ${y}`);
      } else {
        points.push(`L ${x} ${y}`);
      }
    }

    return points.join(" ");
  };

  return (
    <svg
      style={{
        position: "absolute",
        width: "100%",
        height: "100%",
        left: 0,
        top: 0,
      }}
    >
      <defs>
        <linearGradient
          id="curveGradient"
          x1="0%"
          y1="0%"
          x2="100%"
          y2="0%"
        >
          <stop offset="0%" stopColor={COLORS.CURVE_BLUE} />
          <stop offset="100%" stopColor={COLORS.CURVE_AMBER} />
        </linearGradient>

        <filter
          id="curveGlow"
          x="-30%"
          y="-30%"
          width="160%"
          height="160%"
        >
          <feGaussianBlur stdDeviation="6" result="coloredBlur" />
          <feMerge>
            <feMergeNode in="coloredBlur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {progress > 0 && (
        <path
          d={generateCurvePath()}
          fill="none"
          stroke="url(#curveGradient)"
          strokeWidth={5}
          strokeLinecap="round"
          strokeLinejoin="round"
          filter="url(#curveGlow)"
        />
      )}

      {/* Endpoint dot */}
      {progress > 0 && (
        <>
          {/* Start point */}
          <circle
            cx={ORIGIN.x + 50}
            cy={ORIGIN.y - 50 - (1 / 0.25) * (ORIGIN.y - Y_END.y - 100) * 0.85}
            r={8}
            fill={COLORS.CURVE_BLUE}
            opacity={Math.min(progress * 5, 1)}
            filter="url(#curveGlow)"
          />
          {/* End point (only when curve is complete) */}
          {progress >= 0.95 && (
            <circle
              cx={X_END.x - 100 - 50}
              cy={
                ORIGIN.y -
                50 -
                (1 / (1 * 2.5 + 0.25)) * (ORIGIN.y - Y_END.y - 100) * 0.85
              }
              r={8}
              fill={COLORS.CURVE_AMBER}
              opacity={interpolate(progress, [0.95, 1], [0, 1], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              })}
              filter="url(#curveGlow)"
            />
          )}
        </>
      )}
    </svg>
  );
};

export const PrecisionGraph: React.FC<PrecisionGraphPropsType> = ({
  showRegionLabels = true,
}) => {
  const frame = useCurrentFrame();

  // Y-axis draw progress
  const yAxisProgress = interpolate(
    frame,
    [BEATS.Y_AXIS_START, BEATS.Y_AXIS_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // X-axis draw progress
  const xAxisProgress = interpolate(
    frame,
    [BEATS.X_AXIS_START, BEATS.X_AXIS_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Label opacity
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Curve draw progress
  const curveProgress = interpolate(
    frame,
    [BEATS.CURVE_START, BEATS.CURVE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Graph container */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: "100%",
          height: "100%",
        }}
      >
        {/* Axes */}
        <GraphAxes yProgress={yAxisProgress} xProgress={xAxisProgress} />

        {/* Labels */}
        <AxisLabels opacity={labelOpacity} showRegionLabels={showRegionLabels} />

        {/* Inverse curve */}
        <InverseCurve progress={curveProgress} />
      </div>
    </AbsoluteFill>
  );
};
