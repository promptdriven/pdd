import React from "react";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  FONT_FAMILY,
} from "./constants";

interface DangerZoneProps {
  side: "left" | "right";
  label: string;
  color: string;
  zoneOpacity: number;
  labelOpacity: number;
}

export const DangerZone: React.FC<DangerZoneProps> = ({
  side,
  label,
  color,
  zoneOpacity,
  labelOpacity,
}) => {
  const chartWidth = CHART_RIGHT - CHART_LEFT;
  const chartHeight = CHART_BOTTOM - CHART_TOP;

  // Left zone: x 0–0.185, Right zone: x 0.815–1.0
  const x =
    side === "left"
      ? CHART_LEFT
      : CHART_LEFT + chartWidth * 0.815;
  const width =
    side === "left"
      ? chartWidth * 0.185
      : chartWidth * 0.185;

  return (
    <>
      {/* Tinted rectangle */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: CHART_TOP,
          width,
          height: chartHeight,
          backgroundColor: color,
          opacity: zoneOpacity,
          borderRadius: 4,
        }}
      />

      {/* Label */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: CHART_BOTTOM - 50,
          width,
          textAlign: "center",
          opacity: labelOpacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 600,
          fontSize: 20,
          color,
          whiteSpace: "nowrap",
        }}
      >
        {label}
      </div>
    </>
  );
};
