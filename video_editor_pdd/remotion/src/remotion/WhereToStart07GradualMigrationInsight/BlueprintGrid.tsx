import React from "react";
import { AbsoluteFill } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GRID_SPACING,
  GRID_COLOR,
  GRID_OPACITY,
} from "./constants";

export const BlueprintGrid: React.FC = () => {
  const verticalLines: React.ReactNode[] = [];
  const horizontalLines: React.ReactNode[] = [];

  for (let x = 0; x <= CANVAS_WIDTH; x += GRID_SPACING) {
    verticalLines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS_HEIGHT}
        stroke={GRID_COLOR}
        strokeWidth={1}
        opacity={GRID_OPACITY}
      />
    );
  }

  for (let y = 0; y <= CANVAS_HEIGHT; y += GRID_SPACING) {
    horizontalLines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS_WIDTH}
        y2={y}
        stroke={GRID_COLOR}
        strokeWidth={1}
        opacity={GRID_OPACITY}
      />
    );
  }

  return (
    <AbsoluteFill>
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {verticalLines}
        {horizontalLines}
      </svg>
    </AbsoluteFill>
  );
};
