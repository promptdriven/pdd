import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  PART_EJECT_TO_Y,
  PART_COLOR,
  GHOST_TOOL_OPACITY,
  DEFECT_COLOR,
  RED_X_SIZE,
  RED_X_STROKE_WIDTH,
  GHOST_TOOL_START,
  GHOST_TOOL_END,
  RED_X_START,
  RED_X_END,
  REJECTED_FADE_START,
  REJECTED_FADE_END,
} from "./constants";

export const RejectedPatch: React.FC = () => {
  const frame = useCurrentFrame();

  // Ghost tool slides in from left
  const toolSlideX = interpolate(
    frame,
    [GHOST_TOOL_START, GHOST_TOOL_END],
    [-60, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const toolOpacity = interpolate(
    frame,
    [GHOST_TOOL_START, GHOST_TOOL_END],
    [0, GHOST_TOOL_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Red X strike-through with back easing
  const xScale = interpolate(
    frame,
    [RED_X_START, RED_X_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.3)) }
  );

  // Everything fades out
  const fadeOut = interpolate(
    frame,
    [REJECTED_FADE_START, REJECTED_FADE_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame >= REJECTED_FADE_END) return null;

  const centerX = MOLD_CENTER_X - 60;
  const centerY = PART_EJECT_TO_Y;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX - 40 + toolSlideX,
        top: centerY - 30,
        width: 80,
        height: 60,
        opacity: fadeOut,
      }}
    >
      {/* Ghost wrench/hand tool */}
      <svg width={80} height={60} viewBox="0 0 80 60">
        {/* Simplified wrench shape */}
        <g opacity={toolOpacity}>
          {/* Handle */}
          <rect
            x={10}
            y={24}
            width={35}
            height={12}
            rx={3}
            fill={PART_COLOR}
          />
          {/* Head */}
          <path
            d="M 45 20 L 60 20 L 65 26 L 65 34 L 60 40 L 45 40 Z"
            fill={PART_COLOR}
          />
          {/* Jaw gap */}
          <rect
            x={55}
            y={27}
            width={10}
            height={6}
            fill="#0A0F1A"
          />
        </g>

        {/* Red X overlay */}
        {frame >= RED_X_START && (
          <g
            transform={`translate(40, 30) scale(${xScale})`}
            style={{ transformOrigin: "center" }}
          >
            <line
              x1={-RED_X_SIZE / 2}
              y1={-RED_X_SIZE / 2}
              x2={RED_X_SIZE / 2}
              y2={RED_X_SIZE / 2}
              stroke={DEFECT_COLOR}
              strokeWidth={RED_X_STROKE_WIDTH}
              strokeLinecap="round"
            />
            <line
              x1={RED_X_SIZE / 2}
              y1={-RED_X_SIZE / 2}
              x2={-RED_X_SIZE / 2}
              y2={RED_X_SIZE / 2}
              stroke={DEFECT_COLOR}
              strokeWidth={RED_X_STROKE_WIDTH}
              strokeLinecap="round"
            />
          </g>
        )}
      </svg>
    </div>
  );
};
