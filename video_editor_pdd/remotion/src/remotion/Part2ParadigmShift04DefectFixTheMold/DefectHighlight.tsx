import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  DEFECT_RED,
  LIGHT_GRAY,
  DEFECT_START,
} from "./constants";

/**
 * Defect callout: red pulse ring, magnifying glass icon, and "Defect detected" label.
 * Appears at DEFECT_START.
 */
export const DefectHighlight: React.FC<{
  partX: number;
  partY: number;
}> = ({ partX, partY }) => {
  const frame = useCurrentFrame();

  if (frame < DEFECT_START) return null;

  const localFrame = frame - DEFECT_START;

  // Fade in
  const fadeIn = interpolate(localFrame, [0, 15], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Pulsing red ring
  const pulseScale =
    1 + 0.15 * Math.sin((localFrame / 10) * Math.PI * 2);
  const pulseOpacity =
    0.3 + 0.15 * Math.sin((localFrame / 10) * Math.PI * 2);

  // Magnifying glass position (zooms in from upper-right)
  const magX = interpolate(localFrame, [0, 20], [partX + 60, partX + 35], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });
  const magY = interpolate(localFrame, [0, 20], [partY - 40, partY - 15], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Label fade in
  const labelOpacity = interpolate(localFrame, [15, 30], [0, 0.7], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div style={{ position: "absolute", left: 0, top: 0, width: "100%", height: "100%", opacity: fadeIn }}>
      {/* Red pulse ring */}
      <div
        style={{
          position: "absolute",
          left: partX - 16,
          top: partY - 16,
          width: 32,
          height: 32,
          borderRadius: "50%",
          border: `2px solid ${DEFECT_RED}`,
          opacity: pulseOpacity,
          transform: `scale(${pulseScale})`,
        }}
      />

      {/* Magnifying glass icon */}
      <svg
        width={40}
        height={40}
        viewBox="0 0 40 40"
        style={{
          position: "absolute",
          left: magX,
          top: magY,
          opacity: 0.5,
        }}
      >
        <circle
          cx={16}
          cy={16}
          r={12}
          fill="none"
          stroke={LIGHT_GRAY}
          strokeWidth={2}
        />
        <line
          x1={25}
          y1={25}
          x2={36}
          y2={36}
          stroke={LIGHT_GRAY}
          strokeWidth={2.5}
          strokeLinecap="round"
        />
      </svg>

      {/* "Defect detected" label */}
      <div
        style={{
          position: "absolute",
          left: partX + 55,
          top: partY + 5,
          fontSize: 13,
          fontFamily: "Inter, sans-serif",
          color: DEFECT_RED,
          opacity: labelOpacity,
          whiteSpace: "nowrap",
        }}
      >
        Defect detected
      </div>
    </div>
  );
};

export default DefectHighlight;
