import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import {
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  WIDTH,
  HEIGHT,
  AXES_DURATION,
} from "./constants";

export const GridLines: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, AXES_DURATION], [0, GRID_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const verticalLines: number[] = [];
  for (let x = GRID_SPACING; x < WIDTH; x += GRID_SPACING) {
    verticalLines.push(x);
  }

  const horizontalLines: number[] = [];
  for (let y = GRID_SPACING; y < HEIGHT; y += GRID_SPACING) {
    horizontalLines.push(y);
  }

  return (
    <AbsoluteFill>
      <svg width={WIDTH} height={HEIGHT}>
        {verticalLines.map((x) => (
          <line
            key={`v-${x}`}
            x1={x}
            y1={0}
            x2={x}
            y2={HEIGHT}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={opacity}
          />
        ))}
        {horizontalLines.map((y) => (
          <line
            key={`h-${y}`}
            x1={0}
            y1={y}
            x2={WIDTH}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={opacity}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};
