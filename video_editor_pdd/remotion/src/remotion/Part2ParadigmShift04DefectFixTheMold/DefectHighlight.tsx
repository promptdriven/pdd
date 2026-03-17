import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MOLD_CENTER_X,
  PART_WIDTH,
  PART_EJECT_TO_Y,
  DEFECT_COLOR,
  DEFECT_PULSE_RADIUS,
  DEFECT_OPACITY,
  DEFECT_LABEL_OPACITY,
  MAGNIFY_SIZE,
  MAGNIFY_COLOR,
  MAGNIFY_OPACITY,
  DEFECT_PULSE_START,
  DEFECT_PULSE_CYCLE,
  DEFECT_LABEL_FADE_START,
  DEFECT_LABEL_FADE_END,
  MAGNIFY_APPEAR_START,
  MAGNIFY_APPEAR_END,
  DEFECT_LABEL_SIZE,
  DEFECT_LABEL_X,
  DEFECT_LABEL_Y,
  FONT_FAMILY,
} from "./constants";

export const DefectHighlight: React.FC = () => {
  const frame = useCurrentFrame();

  // Pulse ring animation (sine cycle)
  const cycleFrame = Math.max(0, frame - DEFECT_PULSE_START);
  const phase = (cycleFrame % DEFECT_PULSE_CYCLE) / DEFECT_PULSE_CYCLE;
  const sineVal = Math.sin(phase * Math.PI * 2);
  const pulseScale = interpolate(sineVal, [-1, 1], [0.8, 1.3]);
  const pulseOpacity = interpolate(sineVal, [-1, 1], [DEFECT_OPACITY * 0.5, DEFECT_OPACITY]);

  // Magnifying glass appearance
  const magnifyScale = interpolate(
    frame,
    [MAGNIFY_APPEAR_START, MAGNIFY_APPEAR_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Label fade in
  const labelOpacity = interpolate(
    frame,
    [DEFECT_LABEL_FADE_START, DEFECT_LABEL_FADE_END],
    [0, DEFECT_LABEL_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Position: right edge of the part (where the notch defect is)
  const defectX = MOLD_CENTER_X + PART_WIDTH / 2 - 12;
  const defectY = PART_EJECT_TO_Y;

  return (
    <>
      {/* Pulsing red ring around defect area */}
      <div
        style={{
          position: "absolute",
          left: defectX - DEFECT_PULSE_RADIUS,
          top: defectY - DEFECT_PULSE_RADIUS,
          width: DEFECT_PULSE_RADIUS * 2,
          height: DEFECT_PULSE_RADIUS * 2,
          borderRadius: "50%",
          border: `2px solid ${DEFECT_COLOR}`,
          opacity: pulseOpacity,
          transform: `scale(${pulseScale})`,
          transformOrigin: "center center",
          boxShadow: `0 0 12px ${DEFECT_COLOR}`,
        }}
      />

      {/* Magnifying glass icon */}
      <div
        style={{
          position: "absolute",
          left: defectX + 20,
          top: defectY - MAGNIFY_SIZE - 10,
          width: MAGNIFY_SIZE,
          height: MAGNIFY_SIZE,
          transform: `scale(${magnifyScale})`,
          transformOrigin: "bottom left",
        }}
      >
        <svg width={MAGNIFY_SIZE} height={MAGNIFY_SIZE} viewBox="0 0 40 40">
          {/* Glass circle */}
          <circle
            cx={16}
            cy={16}
            r={12}
            fill="none"
            stroke={MAGNIFY_COLOR}
            strokeWidth={2}
            strokeOpacity={MAGNIFY_OPACITY}
          />
          {/* Handle */}
          <line
            x1={25}
            y1={25}
            x2={36}
            y2={36}
            stroke={MAGNIFY_COLOR}
            strokeWidth={3}
            strokeOpacity={MAGNIFY_OPACITY}
            strokeLinecap="round"
          />
          {/* Glint */}
          <circle
            cx={12}
            cy={12}
            r={3}
            fill="none"
            stroke={MAGNIFY_COLOR}
            strokeWidth={1}
            strokeOpacity={MAGNIFY_OPACITY * 0.6}
          />
        </svg>
      </div>

      {/* "Defect detected" label */}
      <div
        style={{
          position: "absolute",
          left: DEFECT_LABEL_X,
          top: DEFECT_LABEL_Y,
          fontFamily: FONT_FAMILY,
          fontSize: DEFECT_LABEL_SIZE,
          color: DEFECT_COLOR,
          opacity: labelOpacity,
          whiteSpace: "nowrap" as const,
        }}
      >
        Defect detected
      </div>
    </>
  );
};
