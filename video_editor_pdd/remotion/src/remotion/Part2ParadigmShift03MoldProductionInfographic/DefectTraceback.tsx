import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_X,
  MOLD_Y,
  MOLD_W,
  MOLD_H,
  PART_Y,
  PART_H,
  DEFECT_COLOR,
  TRACEBACK_START,
  TRACEBACK_END,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

interface DefectTracebackProps {
  defectX: number;
}

export const DefectTraceback: React.FC<DefectTracebackProps> = ({
  defectX,
}) => {
  const frame = useCurrentFrame();

  if (frame < TRACEBACK_START) return null;

  const drawProgress = interpolate(
    frame,
    [TRACEBACK_START, TRACEBACK_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const opacity = interpolate(
    frame,
    [TRACEBACK_START, TRACEBACK_START + 5, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Line from defect part position back to the mold
  const fromX = defectX;
  const fromY = PART_Y + PART_H / 2;
  const toX = MOLD_X + MOLD_W;
  const toY = MOLD_Y + MOLD_H / 2;

  // Compute the current endpoint based on draw progress
  const currentX = interpolate(drawProgress, [0, 1], [fromX, toX]);
  const currentY = interpolate(drawProgress, [0, 1], [fromY, toY]);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, opacity }}
    >
      <defs>
        <marker
          id="arrowhead"
          markerWidth="8"
          markerHeight="6"
          refX="8"
          refY="3"
          orient="auto"
        >
          <polygon points="0 0, 8 3, 0 6" fill={DEFECT_COLOR} />
        </marker>
      </defs>

      {/* Dashed trace-back line */}
      <line
        x1={fromX}
        y1={fromY}
        x2={currentX}
        y2={currentY}
        stroke={DEFECT_COLOR}
        strokeWidth={2.5}
        strokeDasharray="8 5"
        markerEnd={drawProgress > 0.9 ? "url(#arrowhead)" : undefined}
      />

      {/* Red "X" mark at defect part when visible */}
      {frame >= TRACEBACK_START - 20 && (
        <text
          x={defectX}
          y={PART_Y - 10}
          textAnchor="middle"
          fill={DEFECT_COLOR}
          fontSize={28}
          fontFamily="Inter, sans-serif"
          fontWeight={700}
        >
          ✗
        </text>
      )}
    </svg>
  );
};

export default DefectTraceback;
