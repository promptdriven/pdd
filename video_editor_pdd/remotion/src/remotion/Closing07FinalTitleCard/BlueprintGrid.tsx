import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GRID_SPACING,
  GRID_LINE_COLOR,
  GRID_LINE_OPACITY,
  GRID_FADE_END,
} from "./constants";

export const BlueprintGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const gridOpacity = interpolate(frame, [0, GRID_FADE_END], [0, GRID_LINE_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const verticalLines: React.ReactNode[] = [];
  for (let x = GRID_SPACING; x < CANVAS_WIDTH; x += GRID_SPACING) {
    verticalLines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS_HEIGHT}
        stroke={GRID_LINE_COLOR}
        strokeWidth={1}
      />
    );
  }

  const horizontalLines: React.ReactNode[] = [];
  for (let y = GRID_SPACING; y < CANVAS_HEIGHT; y += GRID_SPACING) {
    horizontalLines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS_WIDTH}
        y2={y}
        stroke={GRID_LINE_COLOR}
        strokeWidth={1}
      />
    );
  }

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        opacity: gridOpacity,
      }}
    >
      {verticalLines}
      {horizontalLines}
    </svg>
  );
};
