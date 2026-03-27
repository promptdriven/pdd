import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  GRID_SPACING,
  GRID_COLOR,
  GRID_OPACITY,
  CANVAS_W,
  CANVAS_H,
  BG_FADE_START,
  BG_FADE_END,
} from "./constants";

export const BlueprintGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [BG_FADE_START, BG_FADE_END],
    [0, GRID_OPACITY],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const verticalLines: React.ReactNode[] = [];
  const horizontalLines: React.ReactNode[] = [];

  for (let x = 0; x <= CANVAS_W; x += GRID_SPACING) {
    verticalLines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS_H}
        stroke={GRID_COLOR}
        strokeWidth={1}
      />
    );
  }

  for (let y = 0; y <= CANVAS_H; y += GRID_SPACING) {
    horizontalLines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS_W}
        y2={y}
        stroke={GRID_COLOR}
        strokeWidth={1}
      />
    );
  }

  return (
    <AbsoluteFill style={{ opacity }}>
      <svg
        width={CANVAS_W}
        height={CANVAS_H}
        viewBox={`0 0 ${CANVAS_W} ${CANVAS_H}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {verticalLines}
        {horizontalLines}
      </svg>
    </AbsoluteFill>
  );
};

export default BlueprintGrid;
