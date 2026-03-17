import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { ARROW_COLOR, ARROW_OPACITY, CANVAS_WIDTH, CANVAS_HEIGHT } from "./constants";

interface FlowArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  drawStart: number;
  drawEnd: number;
}

export const FlowArrow: React.FC<FlowArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  drawStart,
  drawEnd,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [drawStart, drawEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  if (frame < drawStart) return null;

  const dx = toX - fromX;
  const dy = toY - fromY;
  const arrowSize = 6;

  // Current endpoint based on progress
  const curX = fromX + dx * progress;
  const curY = fromY + dy * progress;

  // Arrowhead direction
  const angle = Math.atan2(dy, dx);
  const ax1 = curX - arrowSize * Math.cos(angle - Math.PI / 6);
  const ay1 = curY - arrowSize * Math.sin(angle - Math.PI / 6);
  const ax2 = curX - arrowSize * Math.cos(angle + Math.PI / 6);
  const ay2 = curY - arrowSize * Math.sin(angle + Math.PI / 6);

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
      style={{ position: "absolute", left: 0, top: 0, pointerEvents: "none" }}
    >
      {/* Main line */}
      <line
        x1={fromX}
        y1={fromY}
        x2={curX}
        y2={curY}
        stroke={ARROW_COLOR}
        strokeWidth={1}
        opacity={ARROW_OPACITY}
      />
      {/* Arrowhead */}
      {progress > 0.2 && (
        <polygon
          points={`${curX},${curY} ${ax1},${ay1} ${ax2},${ay2}`}
          fill={ARROW_COLOR}
          opacity={ARROW_OPACITY}
        />
      )}
    </svg>
  );
};

export default FlowArrow;
