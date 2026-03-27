import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_OUTER_WIDTH,
  MOLD_OUTER_HEIGHT,
  MOLD_INNER_WIDTH,
  MOLD_INNER_HEIGHT,
  MOLD_CORNER_RADIUS,
  MOLD_STROKE_COLOR,
  MOLD_STROKE_WIDTH,
  NOZZLE_WIDTH,
  NOZZLE_HEIGHT,
  OUTLINE_DRAW_START,
  OUTLINE_DRAW_DURATION,
} from "./constants";

/**
 * Draws the mold cross-section outline with a stroke-dashoffset animation.
 * The mold consists of:
 *  - Outer rectangular shell
 *  - Top nozzle (funnel shape)
 *  - Inner cavity rectangle
 */
export const MoldOutline: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Outer shell coordinates ──
  const outerLeft = MOLD_CENTER_X - MOLD_OUTER_WIDTH / 2;
  const outerTop = MOLD_CENTER_Y - MOLD_OUTER_HEIGHT / 2;

  // ── Inner cavity coordinates (offset slightly downward) ──
  const innerLeft = MOLD_CENTER_X - MOLD_INNER_WIDTH / 2;
  const innerTop = MOLD_CENTER_Y - MOLD_INNER_HEIGHT / 2 + 30;

  // ── Nozzle coordinates ──
  const nozzleTopY = outerTop - NOZZLE_HEIGHT;
  const nozzleBottomY = outerTop;
  const nozzleCenterX = MOLD_CENTER_X;

  // Build the outer rectangle path
  const r = MOLD_CORNER_RADIUS;
  const outerPath = [
    `M ${outerLeft + r} ${outerTop}`,
    `L ${outerLeft + MOLD_OUTER_WIDTH - r} ${outerTop}`,
    `Q ${outerLeft + MOLD_OUTER_WIDTH} ${outerTop} ${outerLeft + MOLD_OUTER_WIDTH} ${outerTop + r}`,
    `L ${outerLeft + MOLD_OUTER_WIDTH} ${outerTop + MOLD_OUTER_HEIGHT - r}`,
    `Q ${outerLeft + MOLD_OUTER_WIDTH} ${outerTop + MOLD_OUTER_HEIGHT} ${outerLeft + MOLD_OUTER_WIDTH - r} ${outerTop + MOLD_OUTER_HEIGHT}`,
    `L ${outerLeft + r} ${outerTop + MOLD_OUTER_HEIGHT}`,
    `Q ${outerLeft} ${outerTop + MOLD_OUTER_HEIGHT} ${outerLeft} ${outerTop + MOLD_OUTER_HEIGHT - r}`,
    `L ${outerLeft} ${outerTop + r}`,
    `Q ${outerLeft} ${outerTop} ${outerLeft + r} ${outerTop}`,
    "Z",
  ].join(" ");

  // Build nozzle path (funnel)
  const nozzlePath = [
    `M ${nozzleCenterX - NOZZLE_WIDTH / 2} ${nozzleTopY}`,
    `L ${nozzleCenterX + NOZZLE_WIDTH / 2} ${nozzleTopY}`,
    `L ${nozzleCenterX + 20} ${nozzleBottomY}`,
    `L ${nozzleCenterX - 20} ${nozzleBottomY}`,
    "Z",
  ].join(" ");

  // Build inner cavity path
  const innerR = MOLD_CORNER_RADIUS;
  const innerPath = [
    `M ${innerLeft + innerR} ${innerTop}`,
    `L ${innerLeft + MOLD_INNER_WIDTH - innerR} ${innerTop}`,
    `Q ${innerLeft + MOLD_INNER_WIDTH} ${innerTop} ${innerLeft + MOLD_INNER_WIDTH} ${innerTop + innerR}`,
    `L ${innerLeft + MOLD_INNER_WIDTH} ${innerTop + MOLD_INNER_HEIGHT - innerR}`,
    `Q ${innerLeft + MOLD_INNER_WIDTH} ${innerTop + MOLD_INNER_HEIGHT} ${innerLeft + MOLD_INNER_WIDTH - innerR} ${innerTop + MOLD_INNER_HEIGHT}`,
    `L ${innerLeft + innerR} ${innerTop + MOLD_INNER_HEIGHT}`,
    `Q ${innerLeft} ${innerTop + MOLD_INNER_HEIGHT} ${innerLeft} ${innerTop + MOLD_INNER_HEIGHT - innerR}`,
    `L ${innerLeft} ${innerTop + innerR}`,
    `Q ${innerLeft} ${innerTop} ${innerLeft + innerR} ${innerTop}`,
    "Z",
  ].join(" ");

  // Approximate total path length for stroke animation
  const outerPerimeter =
    2 * (MOLD_OUTER_WIDTH + MOLD_OUTER_HEIGHT) - 8 * r + 2 * Math.PI * r;
  const nozzlePerimeter =
    NOZZLE_WIDTH +
    2 * Math.sqrt(((NOZZLE_WIDTH / 2 - 20) ** 2) + (NOZZLE_HEIGHT ** 2)) +
    40;
  const innerPerimeter =
    2 * (MOLD_INNER_WIDTH + MOLD_INNER_HEIGHT) - 8 * innerR + 2 * Math.PI * innerR;
  const totalLength = outerPerimeter + nozzlePerimeter + innerPerimeter;

  // Stroke-dashoffset animation
  const drawProgress = interpolate(
    frame,
    [OUTLINE_DRAW_START, OUTLINE_DRAW_START + OUTLINE_DRAW_DURATION],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const dashOffset = totalLength * drawProgress;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Outer shell */}
      <path
        d={outerPath}
        fill="none"
        stroke={MOLD_STROKE_COLOR}
        strokeWidth={MOLD_STROKE_WIDTH}
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
      />
      {/* Nozzle */}
      <path
        d={nozzlePath}
        fill="none"
        stroke={MOLD_STROKE_COLOR}
        strokeWidth={MOLD_STROKE_WIDTH}
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
      />
      {/* Inner cavity outline */}
      <path
        d={innerPath}
        fill="none"
        stroke={MOLD_STROKE_COLOR}
        strokeWidth={MOLD_STROKE_WIDTH}
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
        strokeLinejoin="round"
      />
    </svg>
  );
};

export default MoldOutline;
