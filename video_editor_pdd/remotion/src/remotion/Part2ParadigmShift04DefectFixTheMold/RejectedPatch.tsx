import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PART_COLOR,
  DEFECT_RED,
  REJECT_START,
  REJECT_END,
} from "./constants";

/**
 * Act 2a — The rejected "patch the part" approach.
 * A ghost hand tool approaches the part, then a red X strikes through.
 * Visible from REJECT_START to REJECT_END.
 */
export const RejectedPatch: React.FC<{
  partX: number;
  partY: number;
}> = ({ partX, partY }) => {
  const frame = useCurrentFrame();

  if (frame < REJECT_START || frame > REJECT_END + 10) return null;

  const localFrame = frame - REJECT_START;

  // Ghost tool fades in then out
  const ghostOpacity = interpolate(
    localFrame,
    [0, 8, 20, 35],
    [0, 0.2, 0.2, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Ghost tool approaches from the left
  const ghostX = interpolate(
    localFrame,
    [0, 15],
    [partX - 80, partX - 30],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Red X appears with back easing
  const xScale = interpolate(
    localFrame,
    [12, 22],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.3)) }
  );

  const xOpacity = interpolate(
    localFrame,
    [12, 22, 35, 45],
    [0, 0.8, 0.8, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div style={{ position: "absolute", left: 0, top: 0, width: "100%", height: "100%" }}>
      {/* Ghost hand/wrench tool */}
      <svg
        width={40}
        height={40}
        viewBox="0 0 40 40"
        style={{
          position: "absolute",
          left: ghostX,
          top: partY - 20,
          opacity: ghostOpacity,
        }}
      >
        {/* Simplified wrench icon */}
        <path
          d="M8 32 L28 12 L32 8 C34 6 38 8 36 12 L32 16 L12 36 C10 38 6 34 8 32Z"
          fill={PART_COLOR}
          fillOpacity={0.4}
        />
        <circle cx={34} cy={10} r={4} fill={PART_COLOR} fillOpacity={0.3} />
      </svg>

      {/* Red X overlay */}
      <svg
        width={40}
        height={40}
        viewBox="0 0 40 40"
        style={{
          position: "absolute",
          left: partX - 20,
          top: partY - 5,
          opacity: xOpacity,
          transform: `scale(${xScale})`,
          transformOrigin: "center center",
        }}
      >
        <line
          x1={8}
          y1={8}
          x2={32}
          y2={32}
          stroke={DEFECT_RED}
          strokeWidth={2.5}
          strokeLinecap="round"
        />
        <line
          x1={32}
          y1={8}
          x2={8}
          y2={32}
          stroke={DEFECT_RED}
          strokeWidth={2.5}
          strokeLinecap="round"
        />
      </svg>
    </div>
  );
};

export default RejectedPatch;
