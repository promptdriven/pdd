import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

interface GridLinesProps {
  gridLeft: number;
  gridTop: number;
  gridSize: number;
  lineColor: string;
  lineWidth: number;
  axisLabelColor: string;
  axisLabelSize: number;
  drawDuration: number;
}

const GridLines: React.FC<GridLinesProps> = ({
  gridLeft,
  gridTop,
  gridSize,
  lineColor,
  lineWidth,
  axisLabelColor,
  axisLabelSize,
  drawDuration,
}) => {
  const frame = useCurrentFrame();
  const half = gridSize / 2;

  // Grid draw progress: 0 → 1 over drawDuration frames
  const drawProgress = interpolate(frame, [0, drawDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Label fade-in (starts at ~frame 20, ends at drawDuration)
  const labelOpacity = interpolate(frame, [20, drawDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Outer box line lengths
  const perimeterLength = gridSize * 4;
  const perimeterDrawn = perimeterLength * drawProgress;

  // Center cross lines
  const crossProgress = interpolate(
    frame,
    [drawDuration * 0.3, drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Arrow SVG for axis directions
  const arrowSize = 8;

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
      }}
    >
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", left: 0, top: 0 }}
      >
        {/* Outer rectangle */}
        <rect
          x={gridLeft}
          y={gridTop}
          width={gridSize}
          height={gridSize}
          fill="none"
          stroke={lineColor}
          strokeWidth={lineWidth}
          strokeDasharray={perimeterLength}
          strokeDashoffset={perimeterLength - perimeterDrawn}
        />

        {/* Vertical center line */}
        <line
          x1={gridLeft + half}
          y1={gridTop}
          x2={gridLeft + half}
          y2={gridTop + gridSize * crossProgress}
          stroke={lineColor}
          strokeWidth={lineWidth}
        />

        {/* Horizontal center line */}
        <line
          x1={gridLeft}
          y1={gridTop + half}
          x2={gridLeft + gridSize * crossProgress}
          y2={gridTop + half}
          stroke={lineColor}
          strokeWidth={lineWidth}
        />

        {/* X-axis arrow (bottom, pointing right) */}
        <g opacity={labelOpacity}>
          <line
            x1={gridLeft}
            y1={gridTop + gridSize + 40}
            x2={gridLeft + gridSize}
            y2={gridTop + gridSize + 40}
            stroke={axisLabelColor}
            strokeWidth={1}
            strokeOpacity={0.4}
          />
          <polygon
            points={`${gridLeft + gridSize},${gridTop + gridSize + 40} ${gridLeft + gridSize - arrowSize},${gridTop + gridSize + 40 - arrowSize / 2} ${gridLeft + gridSize - arrowSize},${gridTop + gridSize + 40 + arrowSize / 2}`}
            fill={axisLabelColor}
            fillOpacity={0.4}
          />
        </g>

        {/* Y-axis arrow (left, pointing down) */}
        <g opacity={labelOpacity}>
          <line
            x1={gridLeft - 40}
            y1={gridTop}
            x2={gridLeft - 40}
            y2={gridTop + gridSize}
            stroke={axisLabelColor}
            strokeWidth={1}
            strokeOpacity={0.4}
          />
          <polygon
            points={`${gridLeft - 40},${gridTop + gridSize} ${gridLeft - 40 - arrowSize / 2},${gridTop + gridSize - arrowSize} ${gridLeft - 40 + arrowSize / 2},${gridTop + gridSize - arrowSize}`}
            fill={axisLabelColor}
            fillOpacity={0.4}
          />
        </g>
      </svg>

      {/* X-axis labels */}
      <div
        style={{
          position: "absolute",
          left: gridLeft,
          top: gridTop + gridSize + 50,
          width: half,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: axisLabelSize,
          fontWeight: 400,
          color: axisLabelColor,
          opacity: labelOpacity,
        }}
      >
        Greenfield
      </div>
      <div
        style={{
          position: "absolute",
          left: gridLeft + half,
          top: gridTop + gridSize + 50,
          width: half,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: axisLabelSize,
          fontWeight: 400,
          color: axisLabelColor,
          opacity: labelOpacity,
        }}
      >
        Brownfield
      </div>

      {/* Y-axis labels */}
      <div
        style={{
          position: "absolute",
          left: gridLeft - 180,
          top: gridTop,
          width: 160,
          height: half,
          display: "flex",
          alignItems: "center",
          justifyContent: "flex-end",
          fontFamily: "Inter, sans-serif",
          fontSize: axisLabelSize,
          fontWeight: 400,
          color: axisLabelColor,
          opacity: labelOpacity,
          textAlign: "right",
        }}
      >
        In-Distribution
      </div>
      <div
        style={{
          position: "absolute",
          left: gridLeft - 180,
          top: gridTop + half,
          width: 160,
          height: half,
          display: "flex",
          alignItems: "center",
          justifyContent: "flex-end",
          fontFamily: "Inter, sans-serif",
          fontSize: axisLabelSize,
          fontWeight: 400,
          color: axisLabelColor,
          opacity: labelOpacity,
          textAlign: "right",
        }}
      >
        Out-of-Distribution
      </div>
    </div>
  );
};

export default GridLines;
