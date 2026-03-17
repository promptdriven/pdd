import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  MOLD_CENTER_Y,
  MOLD_WIDTH,
  MOLD_HEIGHT,
  CURSOR_COLOR,
  CURSOR_OPACITY,
  ADJUSTMENT_COLOR,
  CURSOR_APPEAR_START,
  CURSOR_APPEAR_END,
  WALL_ADJUST_START,
  WALL_ADJUST_END,
  FIX_LABEL_FADE_START,
  FIX_LABEL_FADE_END,
  FIX_MOLD_LABEL_X,
  FIX_MOLD_LABEL_Y,
  FIX_MOLD_LABEL_SIZE,
  FIX_MOLD_LABEL_WEIGHT,
  FONT_FAMILY,
} from "./constants";

export const MoldAdjustment: React.FC = () => {
  const frame = useCurrentFrame();

  // Cursor/wrench icon appears
  const cursorOpacity = interpolate(
    frame,
    [CURSOR_APPEAR_START, CURSOR_APPEAR_END],
    [0, CURSOR_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Cursor follows the wall shift
  const cursorShiftX = interpolate(
    frame,
    [WALL_ADJUST_START, WALL_ADJUST_END],
    [0, -4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // "Fix the mold" label
  const labelOpacity = interpolate(
    frame,
    [FIX_LABEL_FADE_START, FIX_LABEL_FADE_END],
    [0, 0.8],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Position cursor at right wall of mold
  const wallThickness = 40;
  const cursorX = MOLD_CENTER_X + MOLD_WIDTH / 2 - wallThickness + cursorShiftX;
  const cursorY = MOLD_CENTER_Y - 20;

  return (
    <>
      {/* Cursor/wrench icon positioned at the right wall */}
      <div
        style={{
          position: "absolute",
          left: cursorX + 10,
          top: cursorY - 20,
          opacity: cursorOpacity,
        }}
      >
        <svg width={36} height={36} viewBox="0 0 36 36">
          {/* Wrench icon */}
          <g fill={CURSOR_COLOR}>
            {/* Handle */}
            <rect x={14} y={16} width={18} height={5} rx={2} />
            {/* Head ring */}
            <circle cx={12} cy={18} r={10} fill="none" stroke={CURSOR_COLOR} strokeWidth={3} />
            <circle cx={12} cy={18} r={5} fill="#0A0F1A" />
            {/* Notch in head */}
            <rect x={7} y={16} width={10} height={4} fill={CURSOR_COLOR} />
          </g>
        </svg>
      </div>

      {/* "Fix the mold" label */}
      <div
        style={{
          position: "absolute",
          left: FIX_MOLD_LABEL_X,
          top: FIX_MOLD_LABEL_Y,
          fontFamily: FONT_FAMILY,
          fontSize: FIX_MOLD_LABEL_SIZE,
          fontWeight: FIX_MOLD_LABEL_WEIGHT,
          color: ADJUSTMENT_COLOR,
          opacity: labelOpacity,
          whiteSpace: "nowrap" as const,
        }}
      >
        Fix the mold
      </div>
    </>
  );
};
