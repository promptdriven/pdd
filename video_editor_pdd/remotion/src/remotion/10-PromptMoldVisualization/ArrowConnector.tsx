import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  ARROW_COLOR,
  ARROW_STROKE,
  ARROWHEAD_SIZE,
  ARROW_LABEL_FONT_SIZE,
  FONT_FAMILY,
} from "./constants";

interface ArrowConnectorProps {
  fromX: number;
  toX: number;
  y: number;
  label: string;
  bidirectional?: boolean;
  drawStartFrame: number;
  drawEndFrame: number;
}

export const ArrowConnector: React.FC<ArrowConnectorProps> = ({
  fromX,
  toX,
  y,
  label,
  bidirectional = false,
  drawStartFrame,
  drawEndFrame,
}) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [drawStartFrame, drawEndFrame],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.bezier(0.42, 0, 0.58, 1),
    }
  );

  if (drawProgress <= 0) return null;

  const labelOpacity = interpolate(
    frame,
    [drawEndFrame - 5, drawEndFrame + 5],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const totalLength = toX - fromX;
  const currentLength = totalLength * drawProgress;
  const currentEndX = fromX + currentLength;

  const midX = (fromX + toX) / 2;
  const a = ARROWHEAD_SIZE;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {/* Main line */}
      <line
        x1={fromX}
        y1={y}
        x2={currentEndX}
        y2={y}
        stroke={ARROW_COLOR}
        strokeWidth={ARROW_STROKE}
      />

      {/* Right arrowhead */}
      {drawProgress >= 0.9 && (
        <polygon
          points={`${toX},${y} ${toX - a},${y - a / 2} ${toX - a},${y + a / 2}`}
          fill={ARROW_COLOR}
          opacity={interpolate(drawProgress, [0.9, 1], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        />
      )}

      {/* Left arrowhead (bidirectional) */}
      {bidirectional && drawProgress >= 0.9 && (
        <polygon
          points={`${fromX},${y} ${fromX + a},${y - a / 2} ${fromX + a},${y + a / 2}`}
          fill={ARROW_COLOR}
          opacity={interpolate(drawProgress, [0.9, 1], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        />
      )}

      {/* Label above arrow */}
      <text
        x={midX}
        y={y - 16}
        fill={ARROW_COLOR}
        fontSize={ARROW_LABEL_FONT_SIZE}
        fontFamily={FONT_FAMILY}
        fontWeight={500}
        textAnchor="middle"
        opacity={labelOpacity}
      >
        {label}
      </text>
    </svg>
  );
};
