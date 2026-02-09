import React from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import {
  CHART_MARGINS,
  YEAR_RANGE,
  COST_RANGE,
  COST_CURVE_DATA,
  LINEAR_REF_DATA,
  COLORS,
  CostDataPoint,
} from "./constants";

interface ExponentialCurveProps {
  startFrame: number;
  endFrame: number;
  showLinearRef?: boolean;
  pulseStartFrame?: number;
  pulseEndFrame?: number;
}

export const ExponentialCurve: React.FC<ExponentialCurveProps> = ({
  startFrame,
  endFrame,
  showLinearRef = true,
  pulseStartFrame,
  pulseEndFrame,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  // Convert data coordinates to screen coordinates
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

  // Calculate draw progress with easeOutQuad as specified
  const drawProgress = interpolate(frame, [startFrame, endFrame], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Build smooth curve path using cubic bezier for exponential look
  const buildCurvePath = (data: CostDataPoint[], progress: number): string => {
    if (progress === 0) return "";

    const points = data.map((d) => ({
      x: getXPosition(d.year),
      y: getYPosition(d.cost),
    }));

    // Calculate how many points to include based on progress
    const totalPoints = points.length;
    const pointsToShow = Math.max(2, Math.ceil(totalPoints * progress));
    const visiblePoints = points.slice(0, pointsToShow);

    // Calculate partial progress within the last segment
    const exactProgress = totalPoints * progress;
    const lastFullIndex = Math.floor(exactProgress) - 1;
    const partialProgress = exactProgress - Math.floor(exactProgress);

    // Start path
    let pathD = `M ${visiblePoints[0].x} ${visiblePoints[0].y}`;

    // Use quadratic bezier curves for smooth exponential appearance
    for (let i = 1; i < visiblePoints.length; i++) {
      const prev = visiblePoints[i - 1];
      const curr = visiblePoints[i];

      // Check if this is the last segment and needs partial drawing
      const isLastSegment = i === visiblePoints.length - 1;
      const needsPartial = isLastSegment && partialProgress > 0 && i > lastFullIndex;

      if (needsPartial && i > 1) {
        // Interpolate the end point for partial segment
        const targetX = prev.x + (curr.x - prev.x) * partialProgress;
        const targetY = prev.y + (curr.y - prev.y) * partialProgress;

        // Control point for smooth curve
        const cpX = prev.x + (curr.x - prev.x) * 0.5;
        const cpY = prev.y; // Keep control point at previous y for exponential feel

        pathD += ` Q ${cpX} ${cpY} ${targetX} ${targetY}`;
      } else {
        // Control point for smooth curve
        const cpX = prev.x + (curr.x - prev.x) * 0.5;
        const cpY = prev.y; // Keep control point at previous y for exponential feel

        pathD += ` Q ${cpX} ${cpY} ${curr.x} ${curr.y}`;
      }
    }

    return pathD;
  };

  // Build linear reference line
  const buildLinearPath = (): string => {
    const startPoint = {
      x: getXPosition(LINEAR_REF_DATA[0].year),
      y: getYPosition(LINEAR_REF_DATA[0].cost),
    };
    const endPoint = {
      x: getXPosition(LINEAR_REF_DATA[1].year),
      y: getYPosition(LINEAR_REF_DATA[1].cost),
    };
    return `M ${startPoint.x} ${startPoint.y} L ${endPoint.x} ${endPoint.y}`;
  };

  // Pulse animation for steep portion
  const pulseScale = pulseStartFrame && pulseEndFrame
    ? interpolate(
        frame,
        [pulseStartFrame, pulseStartFrame + 15, pulseEndFrame - 15, pulseEndFrame],
        [1, 1.03, 1.03, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 1;

  const pulseGlow = pulseStartFrame && pulseEndFrame
    ? interpolate(
        frame,
        [pulseStartFrame, pulseStartFrame + 20, pulseEndFrame - 19, pulseEndFrame],
        [0, 8, 8, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  // Get the current tip position for the animated dot
  const getTipPosition = () => {
    const pointIndex = Math.min(
      COST_CURVE_DATA.length - 1,
      Math.floor(COST_CURVE_DATA.length * drawProgress)
    );
    const point = COST_CURVE_DATA[pointIndex];
    return {
      x: getXPosition(point.year),
      y: getYPosition(point.cost),
    };
  };

  const tip = getTipPosition();
  const curvePath = buildCurvePath(COST_CURVE_DATA, drawProgress);
  const linearPath = buildLinearPath();

  // Linear reference fade in
  const linearOpacity = showLinearRef
    ? interpolate(
        frame,
        [startFrame, startFrame + 30],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {/* Linear reference line (faint blue) */}
      {showLinearRef && linearOpacity > 0 && (
        <>
          <path
            d={linearPath}
            fill="none"
            stroke={COLORS.LINEAR_REF}
            strokeWidth={2}
            strokeDasharray="8,8"
            opacity={linearOpacity}
          />
          {/* Label for linear reference */}
          <text
            x={getXPosition(10) + 15}
            y={getYPosition(1)}
            fill={COLORS.LINEAR_REF}
            fontSize={18}
            fontFamily="Inter, system-ui, sans-serif"
            opacity={linearOpacity}
          >
            Linear
          </text>
        </>
      )}

      {/* Exponential curve with glow effect */}
      {drawProgress > 0 && curvePath && (
        <>
          {/* Glow layer */}
          {pulseGlow > 0 && (
            <path
              d={curvePath}
              fill="none"
              stroke={COLORS.AMBER}
              strokeWidth={6 + pulseGlow}
              strokeLinecap="round"
              strokeLinejoin="round"
              opacity={0.3}
              style={{
                filter: `blur(${pulseGlow}px)`,
              }}
            />
          )}

          {/* Main curve */}
          <path
            d={curvePath}
            fill="none"
            stroke={COLORS.AMBER}
            strokeWidth={4 * pulseScale}
            strokeLinecap="round"
            strokeLinejoin="round"
          />

          {/* Animated dot at the drawing tip */}
          {drawProgress > 0 && drawProgress < 1 && (
            <circle
              cx={tip.x}
              cy={tip.y}
              r={8}
              fill={COLORS.AMBER}
            />
          )}

          {/* End point marker */}
          {drawProgress >= 1 && (
            <circle
              cx={getXPosition(10)}
              cy={getYPosition(14.89)}
              r={6 * pulseScale}
              fill={COLORS.AMBER}
            />
          )}
        </>
      )}
    </svg>
  );
};
