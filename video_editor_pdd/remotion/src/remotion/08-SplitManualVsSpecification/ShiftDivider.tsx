import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  LAYOUT_X,
  LAYOUT_W,
  DIVIDER_Y,
  BEFORE_COLOR,
  AFTER_COLOR,
  SHIFT_TEXT_COLOR,
  SHIFT_LABEL,
  DIVIDER_SWEEP_START,
  DIVIDER_SWEEP_END,
  SHIFT_LABEL_FADE_START,
  SHIFT_LABEL_FADE_END,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const ShiftDivider: React.FC = () => {
  const frame = useCurrentFrame();

  // Divider sweeps left → right with easeInOutCubic
  const sweepProgress = interpolate(
    frame,
    [DIVIDER_SWEEP_START, DIVIDER_SWEEP_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    },
  );

  // "THE SHIFT" pill fades in
  const labelOpacity = interpolate(
    frame,
    [SHIFT_LABEL_FADE_START, SHIFT_LABEL_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  const lineWidth = LAYOUT_W * sweepProgress;

  const globalOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  return (
    <div
      style={{
        position: "absolute",
        left: LAYOUT_X,
        top: DIVIDER_Y,
        width: LAYOUT_W,
        height: 2,
        opacity: globalOpacity,
      }}
    >
      {/* Gradient divider line */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: lineWidth,
          height: 2,
          background: `linear-gradient(to right, ${BEFORE_COLOR}, ${AFTER_COLOR})`,
        }}
      />

      {/* "THE SHIFT" pill label */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: "50%",
          transform: "translate(-50%, -50%)",
          opacity: labelOpacity,
          fontFamily: "Inter, sans-serif",
          fontWeight: 900,
          fontSize: 16,
          color: SHIFT_TEXT_COLOR,
          background: `linear-gradient(to right, ${BEFORE_COLOR}, ${AFTER_COLOR})`,
          padding: "6px 20px",
          borderRadius: 12,
          whiteSpace: "nowrap",
          letterSpacing: "0.06em",
        }}
      >
        {SHIFT_LABEL}
      </div>
    </div>
  );
};

export default ShiftDivider;
