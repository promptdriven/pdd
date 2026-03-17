import React from "react";
import { interpolate, Easing } from "remotion";
import {
  ARROW_COLOR,
  ARROW_OPACITY,
  ARROW_LABEL_OPACITY,
  TENSION_LINE_OPACITY,
  ANIM,
} from "./constants";

interface ScaleArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  localFrame: number;
  isDramatic?: boolean;
}

export const ScaleArrow: React.FC<ScaleArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  localFrame,
  isDramatic,
}) => {
  const arrowProgress = interpolate(
    localFrame,
    [0, ANIM.ARROW_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const tensionProgress = interpolate(
    localFrame,
    [0, ANIM.TENSION_LINE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.exp),
    }
  );

  if (arrowProgress <= 0) return null;

  // Arrow endpoints (from right side of source step to left side of target step)
  const startX = fromX + 200;
  const startY = fromY - 60;
  const endX = toX + 40;
  const endY = toY - 60;

  // Curve control point (arches upward)
  const midX = (startX + endX) / 2;
  const midY = Math.min(startY, endY) - 40;

  // Interpolated end point for drawing animation
  const currentEndX = interpolate(arrowProgress, [0, 1], [startX, endX]);
  const currentEndY = interpolate(arrowProgress, [0, 1], [startY, endY]);
  const currentMidX = interpolate(arrowProgress, [0, 1], [startX, midX]);
  const currentMidY = interpolate(arrowProgress, [0, 1], [startY, midY]);

  const tensionCount = isDramatic ? 5 : 3;
  const tensionLength = isDramatic ? 18 : 12;

  // SVG covers the entire canvas area for this arrow
  const svgLeft = Math.min(fromX, toX) - 40;
  const svgTop = Math.min(startY, endY) - 80;
  const svgWidth = Math.abs(toX - fromX) + 300;
  const svgHeight = Math.abs(startY - endY) + 160;

  const labelX = (startX + endX) / 2 - svgLeft;
  const labelY = midY - 12 - svgTop;

  return (
    <div
      style={{
        position: "absolute",
        left: svgLeft,
        top: svgTop,
        width: svgWidth,
        height: svgHeight,
        pointerEvents: "none",
      }}
    >
      <svg
        width={svgWidth}
        height={svgHeight}
        viewBox={`0 0 ${svgWidth} ${svgHeight}`}
        fill="none"
      >
        {/* Tension lines radiating from source */}
        {Array.from({ length: tensionCount }).map((_, i) => {
          const angle = -30 - (i * 60) / (tensionCount - 1 || 1);
          const rad = (angle * Math.PI) / 180;
          const len = tensionLength * tensionProgress;
          const ox = startX - svgLeft;
          const oy = startY - svgTop;
          return (
            <line
              key={i}
              x1={ox}
              y1={oy}
              x2={ox + Math.cos(rad) * len}
              y2={oy + Math.sin(rad) * len}
              stroke={ARROW_COLOR}
              strokeWidth={1}
              opacity={TENSION_LINE_OPACITY * tensionProgress}
            />
          );
        })}

        {/* Curved arrow path */}
        <path
          d={`M ${startX - svgLeft} ${startY - svgTop} Q ${currentMidX - svgLeft} ${currentMidY - svgTop} ${currentEndX - svgLeft} ${currentEndY - svgTop}`}
          stroke={ARROW_COLOR}
          strokeWidth={1.5}
          opacity={ARROW_OPACITY * arrowProgress}
          fill="none"
        />

        {/* Arrowhead */}
        {arrowProgress > 0.8 && (
          <polygon
            points={`${endX - svgLeft},${endY - svgTop} ${endX - svgLeft - 8},${endY - svgTop - 5} ${endX - svgLeft - 8},${endY - svgTop + 5}`}
            fill={ARROW_COLOR}
            opacity={ARROW_OPACITY * interpolate(arrowProgress, [0.8, 1], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })}
          />
        )}

        {/* Label */}
        {arrowProgress > 0.5 && (
          <text
            x={labelX}
            y={labelY}
            fill={ARROW_COLOR}
            fontSize={9}
            fontFamily="Inter, sans-serif"
            textAnchor="middle"
            opacity={ARROW_LABEL_OPACITY * interpolate(arrowProgress, [0.5, 0.8], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })}
          >
            Couldn&apos;t scale
          </text>
        )}
      </svg>
    </div>
  );
};
