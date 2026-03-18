import React from "react";
import { AbsoluteFill } from "remotion";
import { GRID_COLOR, GRID_OPACITY, GRID_SPACING, WIDTH, HEIGHT } from "./constants";

export const EngineeringGrid: React.FC = () => {
  const verticalLines: React.ReactNode[] = [];
  const horizontalLines: React.ReactNode[] = [];

  for (let x = 0; x <= WIDTH; x += GRID_SPACING) {
    verticalLines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={HEIGHT}
        stroke={GRID_COLOR}
        strokeWidth={1}
        opacity={GRID_OPACITY}
      />
    );
  }

  for (let y = 0; y <= HEIGHT; y += GRID_SPACING) {
    horizontalLines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={WIDTH}
        y2={y}
        stroke={GRID_COLOR}
        strokeWidth={1}
        opacity={GRID_OPACITY}
      />
    );
  }

  return (
    <AbsoluteFill>
      <svg width={WIDTH} height={HEIGHT} style={{ position: "absolute" }}>
        {verticalLines}
        {horizontalLines}
      </svg>
    </AbsoluteFill>
  );
};
