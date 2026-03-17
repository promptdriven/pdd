import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  DASHED_LINE_COLOR,
  DASHED_LINE_OPACITY,
} from "./constants";

interface DashedConnectionProps {
  x: number;
  fromY: number;
  toY: number;
  drawStart: number;
  drawDuration: number;
}

export const DashedConnection: React.FC<DashedConnectionProps> = ({
  x,
  fromY,
  toY,
  drawStart,
  drawDuration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [drawStart, drawStart + drawDuration],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < drawStart) return null;

  const totalLength = toY - fromY;
  const currentEndY = fromY + totalLength * progress;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
      style={{ position: "absolute", left: 0, top: 0, pointerEvents: "none" }}
    >
      <line
        x1={x}
        y1={fromY}
        x2={x}
        y2={currentEndY}
        stroke={DASHED_LINE_COLOR}
        strokeWidth={1}
        opacity={DASHED_LINE_OPACITY}
        strokeDasharray="6 4"
      />
    </svg>
  );
};

export default DashedConnection;
