import React from "react";
import { AbsoluteFill } from "remotion";
import {
  WIDTH,
  HEIGHT,
  GRID_SPACING,
  GRID_LINE_COLOR,
  GRID_LINE_OPACITY,
} from "./constants";

export const BlueprintGrid: React.FC<{ opacity: number }> = ({ opacity }) => {
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
        stroke={GRID_LINE_COLOR}
        strokeWidth={1}
        opacity={GRID_LINE_OPACITY}
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
        stroke={GRID_LINE_COLOR}
        strokeWidth={1}
        opacity={GRID_LINE_OPACITY}
      />
    );
  }

  return (
    <AbsoluteFill style={{ opacity }}>
      <svg width={WIDTH} height={HEIGHT} viewBox={`0 0 ${WIDTH} ${HEIGHT}`}>
        {verticalLines}
        {horizontalLines}
      </svg>
    </AbsoluteFill>
  );
};

export default BlueprintGrid;
