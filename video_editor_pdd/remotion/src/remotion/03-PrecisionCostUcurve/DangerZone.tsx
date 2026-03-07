import React from "react";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  LEFT_DANGER,
  RIGHT_DANGER,
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

  const zone = side === "left" ? LEFT_DANGER : RIGHT_DANGER;
  const x = CHART_LEFT + chartWidth * zone.xStart;
  const width = chartWidth * (zone.xEnd - zone.xStart);

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

      {/* Label — positioned inside the zone near the bottom */}
      <div
        style={{
          position: "absolute",
          left: x,
          top: CHART_BOTTOM - 60,
          width,
          textAlign: "center",
          opacity: labelOpacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 600,
          fontSize: 20,
          color,
          whiteSpace: "nowrap",
          textShadow: `0 0 12px ${color}40`,
        }}
      >
        {label}
      </div>
    </>
  );
};
