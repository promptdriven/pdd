import React from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { CHART_MARGINS, YEAR_RANGE, HOURS_RANGE, DataPoint } from "./constants";

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  startFrame: number;
  endFrame: number;
  strokeWidth?: number;
  label?: string;
  dashed?: boolean;
  showDot?: boolean;
  lineOpacity?: number;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  startFrame,
  endFrame,
  strokeWidth = 4,
  label,
  dashed = false,
  showDot = true,
  lineOpacity = 1,
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

  // Calculate the draw progress with easing
  const drawProgress = interpolate(frame, [startFrame, endFrame], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Build the full path points
  const allPoints = data.map((d) => ({
    x: getXPosition(d.year),
    y: getYPosition(d.hours),
  }));

  if (allPoints.length < 2) return null;

  // For simple 2-point lines, just interpolate the endpoint directly
  const startPoint = allPoints[0];
  const endPoint = allPoints[allPoints.length - 1];

  // Calculate current endpoint based on progress
  const currentEndX = startPoint.x + (endPoint.x - startPoint.x) * drawProgress;
  const currentEndY = startPoint.y + (endPoint.y - startPoint.y) * drawProgress;

  // Build path - for multi-point, calculate segments; for 2-point, simple interpolation
  let pathD = "";
  let tipX = startPoint.x;
  let tipY = startPoint.y;

  if (drawProgress > 0) {
    if (allPoints.length === 2) {
      // Simple 2-point line - direct interpolation
      pathD = `M ${startPoint.x} ${startPoint.y} L ${currentEndX} ${currentEndY}`;
      tipX = currentEndX;
      tipY = currentEndY;
    } else {
      // Multi-point line - calculate segments
      const segments: { startX: number; startY: number; endX: number; endY: number; length: number }[] = [];
      let totalLength = 0;

      for (let i = 1; i < allPoints.length; i++) {
        const dx = allPoints[i].x - allPoints[i - 1].x;
        const dy = allPoints[i].y - allPoints[i - 1].y;
        const length = Math.sqrt(dx * dx + dy * dy);
        segments.push({
          startX: allPoints[i - 1].x,
          startY: allPoints[i - 1].y,
          endX: allPoints[i].x,
          endY: allPoints[i].y,
          length,
        });
        totalLength += length;
      }

      const drawLength = totalLength * drawProgress;
      let remainingLength = drawLength;

      pathD = `M ${allPoints[0].x} ${allPoints[0].y}`;
      tipX = allPoints[0].x;
      tipY = allPoints[0].y;

      for (const seg of segments) {
        if (remainingLength <= 0) break;

        if (remainingLength >= seg.length) {
          pathD += ` L ${seg.endX} ${seg.endY}`;
          tipX = seg.endX;
          tipY = seg.endY;
          remainingLength -= seg.length;
        } else {
          const t = remainingLength / seg.length;
          tipX = seg.startX + t * (seg.endX - seg.startX);
          tipY = seg.startY + t * (seg.endY - seg.startY);
          pathD += ` L ${tipX} ${tipY}`;
          remainingLength = 0;
        }
      }
    }
  }

  // Label opacity
  const labelOpacity = interpolate(
    frame,
    [endFrame - 15, endFrame],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <>
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none", opacity: lineOpacity }}
      >
        {/* The animated line */}
        {drawProgress > 0 && pathD && (
          <path
            d={pathD}
            fill="none"
            stroke={color}
            strokeWidth={strokeWidth}
            strokeLinecap="round"
            strokeLinejoin="round"
            strokeDasharray={dashed ? "12,8" : undefined}
          />
        )}

        {/* Animated dot at the drawing tip */}
        {showDot && drawProgress > 0 && drawProgress < 1 && (
          <circle
            cx={tipX}
            cy={tipY}
            r={8}
            fill={color}
          />
        )}
      </svg>

      {/* Label at the end of the line */}
      {label && drawProgress >= 1 && (
        <div
          style={{
            position: "absolute",
            left: endPoint.x + 15,
            top: endPoint.y,
            transform: "translateY(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 22,
            fontWeight: 600,
            color: color,
            opacity: labelOpacity,
            textShadow: "0 2px 4px rgba(0,0,0,0.5)",
            maxWidth: 180,
            lineHeight: 1.3,
          }}
        >
          {label}
        </div>
      )}
    </>
  );
};
