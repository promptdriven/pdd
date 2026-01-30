import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { BEATS, COLORS, PART_SHAPE } from "./constants";

/**
 * Shows the previous defective part in the bottom-left corner.
 * During frame 180-240 it fades to gray and falls off screen.
 */
export const DefectivePartDiscard: React.FC = () => {
  const frame = useCurrentFrame();

  // The defective part is visible starting at frame 120, positioned in bottom-left corner
  // At frame 180 it begins its discard animation
  if (frame < BEATS.MORE_PARTS_START) return null;

  // Fade-in of the defective part in corner (frames 120-140)
  const fadeIn = interpolate(
    frame,
    [BEATS.MORE_PARTS_START, BEATS.MORE_PARTS_START + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // During discard phase, fade to gray and fall
  const discardProgress = interpolate(
    frame,
    [BEATS.DEFECT_DISCARD_START, BEATS.DEFECT_DISCARD_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    },
  );

  // Color transition: amber -> gray
  // We'll render two rects overlapping, crossfading
  const grayOpacity = discardProgress;

  // Overall opacity: fades out during discard
  const overallOpacity = interpolate(
    frame,
    [BEATS.DEFECT_DISCARD_START, BEATS.DEFECT_DISCARD_START + 30, BEATS.DEFECT_DISCARD_END],
    [1, 0.7, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Fall off screen: vertical translation
  const fallY = discardProgress * 250;

  // Slight rotation as it falls
  const rotation = discardProgress * 25;

  // Position: bottom-left corner
  const baseX = 180;
  const baseY = 750;

  // After fully discarded, don't render
  if (frame > BEATS.DEFECT_DISCARD_END + 10) return null;

  const opacity = fadeIn * overallOpacity;
  if (opacity <= 0) return null;

  return (
    <g>
      {/* "Previous defect" label */}
      {frame < BEATS.DEFECT_DISCARD_END && (
        <text
          x={baseX + PART_SHAPE.width / 2}
          y={baseY - 30}
          textAnchor="middle"
          fontSize={14}
          fontFamily="sans-serif"
          fontWeight={500}
          fill={COLORS.LABEL_GRAY}
          opacity={opacity * 0.8}
        >
          Previous Defect
        </text>
      )}

      {/* Defective part with a small "X" mark */}
      <g
        transform={`translate(${baseX + PART_SHAPE.width / 2}, ${baseY + fallY}) rotate(${rotation})`}
        opacity={opacity}
      >
        {/* Amber base (fades out as gray fades in) */}
        <rect
          x={-PART_SHAPE.width / 2}
          y={-PART_SHAPE.height / 2}
          width={PART_SHAPE.width}
          height={PART_SHAPE.height}
          rx={PART_SHAPE.rx}
          fill={COLORS.PART_AMBER}
          opacity={1 - grayOpacity}
        />
        {/* Gray overlay (fades in during discard) */}
        <rect
          x={-PART_SHAPE.width / 2}
          y={-PART_SHAPE.height / 2}
          width={PART_SHAPE.width}
          height={PART_SHAPE.height}
          rx={PART_SHAPE.rx}
          fill={COLORS.DEFECT_GRAY}
          opacity={grayOpacity}
        />
        {/* Red "X" defect mark */}
        <line
          x1={-8}
          y1={-8}
          x2={8}
          y2={8}
          stroke="#cc4444"
          strokeWidth={2.5}
          strokeLinecap="round"
          opacity={0.9}
        />
        <line
          x1={8}
          y1={-8}
          x2={-8}
          y2={8}
          stroke="#cc4444"
          strokeWidth={2.5}
          strokeLinecap="round"
          opacity={0.9}
        />
      </g>
    </g>
  );
};
