import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  AMBER,
  LIGHT_GRAY,
  FIX_START,
} from "./constants";

/**
 * Act 2b — Fix the mold.
 * Wrench/cursor icon appears at the right wall of the mold.
 * "Fix the mold" label fades in.
 * Visible from FIX_START onward.
 */
export const WallAdjustment: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < FIX_START) return null;

  const localFrame = frame - FIX_START;

  // Wrench icon fades in
  const wrenchOpacity = interpolate(localFrame, [0, 10], [0, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Wrench moves toward wall
  const moldRight =
    MOLD_CENTER_X + MOLD_WIDTH / 2 - 60; // right wall inner edge
  const moldMidY = MOLD_CENTER_Y - 20;

  const wrenchX = interpolate(
    localFrame,
    [0, 15, 30],
    [moldRight + 50, moldRight + 10, moldRight + 15],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Wrench fades out after a while
  const wrenchFade = interpolate(localFrame, [40, 55], [0.6, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const finalWrenchOpacity = localFrame <= 40 ? wrenchOpacity : wrenchFade;

  // Label "Fix the mold" fades in
  const labelOpacity = interpolate(localFrame, [15, 30], [0, 0.8], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Label fades slightly after fixed parts start
  const labelFade = interpolate(localFrame, [60, 100], [0.8, 0.5], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const finalLabelOpacity = localFrame <= 60 ? labelOpacity : labelFade;

  return (
    <div style={{ position: "absolute", left: 0, top: 0, width: "100%", height: "100%" }}>
      {/* Wrench/cursor icon */}
      <svg
        width={44}
        height={44}
        viewBox="0 0 44 44"
        style={{
          position: "absolute",
          left: wrenchX,
          top: moldMidY - 22,
          opacity: finalWrenchOpacity,
        }}
      >
        {/* Wrench icon */}
        <path
          d="M6 34 L24 16 L28 12 C30 8 36 6 38 10 L36 16 L30 18 L14 34 L10 38 C6 40 4 36 6 34Z"
          fill="none"
          stroke={LIGHT_GRAY}
          strokeWidth={1.5}
        />
        <circle
          cx={37}
          cy={10}
          r={5}
          fill="none"
          stroke={LIGHT_GRAY}
          strokeWidth={1.5}
        />
      </svg>

      {/* "Fix the mold" label */}
      <div
        style={{
          position: "absolute",
          left: MOLD_CENTER_X + MOLD_WIDTH / 2 + 30,
          top: MOLD_CENTER_Y - 40,
          fontSize: 14,
          fontWeight: 600,
          fontFamily: "Inter, sans-serif",
          color: AMBER,
          opacity: finalLabelOpacity,
          whiteSpace: "nowrap",
        }}
      >
        Fix the mold
      </div>

      {/* Arrow pointing to wall */}
      {localFrame < 60 && (
        <svg
          width={30}
          height={2}
          style={{
            position: "absolute",
            left: MOLD_CENTER_X + MOLD_WIDTH / 2 + 5,
            top: MOLD_CENTER_Y - 33,
            opacity: finalLabelOpacity * 0.5,
          }}
        >
          <line
            x1={25}
            y1={1}
            x2={0}
            y2={1}
            stroke={AMBER}
            strokeWidth={1.5}
            markerEnd=""
          />
        </svg>
      )}
    </div>
  );
};

export default WallAdjustment;
