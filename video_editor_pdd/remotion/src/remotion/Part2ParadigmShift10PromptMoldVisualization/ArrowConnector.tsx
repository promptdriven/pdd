import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  ARROW_COLOR,
  ARROW_STROKE_WIDTH,
  ARROWHEAD_SIZE,
  FADEOUT_START,
  FADEOUT_END,
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

  if (frame < drawStartFrame) return null;

  // Draw progress
  const drawDuration = drawEndFrame - drawStartFrame;
  const localFrame = frame - drawStartFrame;
  const progress = interpolate(localFrame, [0, drawDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Label fade-in (appears as arrow finishes drawing)
  const labelOpacity = interpolate(
    localFrame,
    [drawDuration * 0.5, drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Master fade-out
  const fadeOut = interpolate(frame, [FADEOUT_START, FADEOUT_END], [1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.cubic),
  });

  const totalLength = toX - fromX;
  const currentLength = totalLength * progress;
  const currentEndX = fromX + currentLength;

  // Arrowhead at the right end (forward direction)
  const rightArrowhead =
    progress > 0.1
      ? `M ${currentEndX} ${y} L ${currentEndX - ARROWHEAD_SIZE} ${y - ARROWHEAD_SIZE / 2} M ${currentEndX} ${y} L ${currentEndX - ARROWHEAD_SIZE} ${y + ARROWHEAD_SIZE / 2}`
      : "";

  // Arrowhead at the left end (backward direction, for bidirectional)
  const leftArrowhead =
    bidirectional && progress > 0.5
      ? `M ${fromX} ${y} L ${fromX + ARROWHEAD_SIZE} ${y - ARROWHEAD_SIZE / 2} M ${fromX} ${y} L ${fromX + ARROWHEAD_SIZE} ${y + ARROWHEAD_SIZE / 2}`
      : "";

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        opacity: fadeOut,
        pointerEvents: "none",
      }}
    >
      {/* Main line */}
      <line
        x1={fromX}
        y1={y}
        x2={currentEndX}
        y2={y}
        stroke={ARROW_COLOR}
        strokeWidth={ARROW_STROKE_WIDTH}
      />

      {/* Right arrowhead */}
      {rightArrowhead && (
        <path
          d={rightArrowhead}
          fill="none"
          stroke={ARROW_COLOR}
          strokeWidth={ARROW_STROKE_WIDTH}
          strokeLinecap="round"
        />
      )}

      {/* Left arrowhead (bidirectional) */}
      {leftArrowhead && (
        <path
          d={leftArrowhead}
          fill="none"
          stroke={ARROW_COLOR}
          strokeWidth={ARROW_STROKE_WIDTH}
          strokeLinecap="round"
        />
      )}

      {/* Label above arrow */}
      <text
        x={(fromX + toX) / 2}
        y={y - 16}
        fill={ARROW_COLOR}
        fontSize={14}
        fontFamily="Inter, sans-serif"
        fontWeight={500}
        textAnchor="middle"
        opacity={labelOpacity}
      >
        {label}
      </text>
    </svg>
  );
};
