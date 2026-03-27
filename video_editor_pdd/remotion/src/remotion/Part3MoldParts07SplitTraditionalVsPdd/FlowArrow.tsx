import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  ARROW_STROKE_WIDTH,
  ARROW_OPACITY,
  ARROW_LENGTH,
  ARROW_DRAW_DURATION,
  STEP_HEIGHT,
} from "./constants";

interface FlowArrowProps {
  color: string;
  startFrame: number;
  centerX: number;
  y: number; // top of the arrow (bottom of previous step)
}

export const FlowArrow: React.FC<FlowArrowProps> = ({
  color,
  startFrame,
  centerX,
  y,
}) => {
  const frame = useCurrentFrame();
  const drawFrame = startFrame + 5; // arrow draws 5 frames after step appears

  const progress = interpolate(
    frame,
    [drawFrame, drawFrame + ARROW_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (progress <= 0) return null;

  const arrowTop = y + STEP_HEIGHT;
  const drawnLength = ARROW_LENGTH * progress;

  return (
    <svg
      style={{
        position: "absolute",
        left: centerX - 8,
        top: arrowTop,
        width: 16,
        height: ARROW_LENGTH,
        overflow: "visible",
      }}
    >
      {/* Main line */}
      <line
        x1={8}
        y1={0}
        x2={8}
        y2={Math.max(0, drawnLength)}
        stroke={color}
        strokeWidth={ARROW_STROKE_WIDTH}
        opacity={ARROW_OPACITY}
      />
      {/* Arrowhead */}
      {progress > 0.7 && (
        <polygon
          points={`4,${ARROW_LENGTH - 6} 8,${ARROW_LENGTH} 12,${ARROW_LENGTH - 6}`}
          fill={color}
          opacity={ARROW_OPACITY * interpolate(progress, [0.7, 1], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })}
        />
      )}
    </svg>
  );
};

export default FlowArrow;
