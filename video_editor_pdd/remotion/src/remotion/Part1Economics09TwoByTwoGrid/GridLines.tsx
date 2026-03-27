import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface GridLinesProps {
  gridLeft: number;
  gridTop: number;
  gridSize: number;
  cellSize: number;
  lineColor: string;
  lineWidth: number;
  drawStart: number;
  drawEnd: number;
}

export const GridLines: React.FC<GridLinesProps> = ({
  gridLeft,
  gridTop,
  gridSize,
  cellSize,
  lineColor,
  lineWidth,
  drawStart,
  drawEnd,
}) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(frame, [drawStart, drawEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Outer border
  const outerPerimeter = 2 * (gridSize + gridSize);
  const outerDash = outerPerimeter * drawProgress;

  // Center cross lines
  const crossProgress = interpolate(
    frame,
    [drawStart + 10, drawEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const midX = gridLeft + cellSize;
  const midY = gridTop + cellSize;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Outer border rectangle */}
      <rect
        x={gridLeft}
        y={gridTop}
        width={gridSize}
        height={gridSize}
        fill="none"
        stroke={lineColor}
        strokeWidth={lineWidth}
        strokeDasharray={`${outerDash} ${outerPerimeter}`}
      />

      {/* Vertical center line */}
      <line
        x1={midX}
        y1={gridTop}
        x2={midX}
        y2={gridTop + gridSize * crossProgress}
        stroke={lineColor}
        strokeWidth={lineWidth}
      />

      {/* Horizontal center line */}
      <line
        x1={gridLeft}
        y1={midY}
        x2={gridLeft + gridSize * crossProgress}
        y2={midY}
        stroke={lineColor}
        strokeWidth={lineWidth}
      />
    </svg>
  );
};

export default GridLines;
