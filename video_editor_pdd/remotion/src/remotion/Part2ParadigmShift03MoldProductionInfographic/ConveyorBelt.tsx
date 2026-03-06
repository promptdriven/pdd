import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CONVEYOR_X_START,
  CONVEYOR_X_END,
  CONVEYOR_Y,
  CONVEYOR_STROKE,
  CONVEYOR_STROKE_WIDTH,
  CONVEYOR_DRAW_START,
  CONVEYOR_DRAW_END,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const ConveyorBelt: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [CONVEYOR_DRAW_START, CONVEYOR_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const opacity = interpolate(
    frame,
    [CONVEYOR_DRAW_START, CONVEYOR_DRAW_START + 5, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const beltLength = CONVEYOR_X_END - CONVEYOR_X_START;
  const visibleLength = beltLength * drawProgress;

  // Animated dash offset for belt movement
  const dashOffset = -frame * 2;

  // Support leg height
  const legH = 60;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, opacity }}
    >
      {/* Main belt line with animated dashes */}
      <line
        x1={CONVEYOR_X_START}
        y1={CONVEYOR_Y}
        x2={CONVEYOR_X_START + visibleLength}
        y2={CONVEYOR_Y}
        stroke={CONVEYOR_STROKE}
        strokeWidth={CONVEYOR_STROKE_WIDTH}
        strokeDasharray="12 6"
        strokeDashoffset={dashOffset}
      />

      {/* Top rail (thin) */}
      <line
        x1={CONVEYOR_X_START}
        y1={CONVEYOR_Y - 22}
        x2={CONVEYOR_X_START + visibleLength}
        y2={CONVEYOR_Y - 22}
        stroke={CONVEYOR_STROKE}
        strokeWidth={1.5}
        opacity={0.4}
      />

      {/* Support legs */}
      {drawProgress > 0.1 && (
        <line
          x1={CONVEYOR_X_START}
          y1={CONVEYOR_Y}
          x2={CONVEYOR_X_START}
          y2={CONVEYOR_Y + legH}
          stroke={CONVEYOR_STROKE}
          strokeWidth={3}
          opacity={0.6}
        />
      )}
      {drawProgress > 0.9 && (
        <line
          x1={CONVEYOR_X_END}
          y1={CONVEYOR_Y}
          x2={CONVEYOR_X_END}
          y2={CONVEYOR_Y + legH}
          stroke={CONVEYOR_STROKE}
          strokeWidth={3}
          opacity={0.6}
        />
      )}

      {/* Belt surface highlight */}
      <line
        x1={CONVEYOR_X_START}
        y1={CONVEYOR_Y + 2}
        x2={CONVEYOR_X_START + visibleLength}
        y2={CONVEYOR_Y + 2}
        stroke="#64748B"
        strokeWidth={1}
        opacity={0.3}
      />
    </svg>
  );
};

export default ConveyorBelt;
