import React from "react";
import {
  CHART_LEFT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  SWEET_SPOT,
  GREEN,
  FONT_FAMILY,
} from "./constants";

interface SweetSpotMarkerProps {
  scale: number;
  opacity: number;
}

export const SweetSpotMarker: React.FC<SweetSpotMarkerProps> = ({
  scale,
  opacity,
}) => {
  const spotX = CHART_LEFT + SWEET_SPOT.x * CHART_WIDTH;
  const spotY = CHART_BOTTOM - SWEET_SPOT.y * CHART_HEIGHT;

  return (
    <>
      {/* Dashed vertical line at sweet spot */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0, opacity }}
      >
        <line
          x1={spotX}
          y1={CHART_TOP}
          x2={spotX}
          y2={CHART_BOTTOM}
          stroke={GREEN}
          strokeWidth={2}
          strokeDasharray="8 6"
          opacity={0.5}
        />

        {/* Green dot on curve with glow */}
        <circle
          cx={spotX}
          cy={spotY}
          r={18 * scale}
          fill={GREEN}
          opacity={0.15}
        />
        <circle
          cx={spotX}
          cy={spotY}
          r={8 * scale}
          fill={GREEN}
        />
      </svg>

      {/* "~250 lines" label with downward arrow */}
      <div
        style={{
          position: "absolute",
          left: spotX - 60,
          top: spotY - 70,
          width: 120,
          textAlign: "center",
          opacity,
          transform: `scale(${scale})`,
          transformOrigin: "center bottom",
        }}
      >
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontWeight: 700,
            fontSize: 22,
            color: GREEN,
            lineHeight: 1.2,
          }}
        >
          ~250 lines
        </div>
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 16,
            color: GREEN,
            lineHeight: 1,
          }}
        >
          ▼
        </div>
      </div>

      {/* "Sweet spot" pill badge */}
      <div
        style={{
          position: "absolute",
          left: spotX - 50,
          top: spotY + 20,
          opacity,
          transform: `scale(${scale})`,
          transformOrigin: "center top",
        }}
      >
        <div
          style={{
            display: "inline-block",
            padding: "4px 16px",
            backgroundColor: `${GREEN}33`,
            border: `1.5px solid ${GREEN}`,
            borderRadius: 20,
            fontFamily: FONT_FAMILY,
            fontWeight: 600,
            fontSize: 14,
            color: GREEN,
            whiteSpace: "nowrap",
          }}
        >
          Sweet spot
        </div>
      </div>
    </>
  );
};
