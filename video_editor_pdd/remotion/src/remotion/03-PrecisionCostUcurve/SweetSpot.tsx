import React from "react";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  SWEET_SPOT,
  AMBER,
  SWEET_SPOT_SUBLABEL_COLOR,
  FONT_FAMILY,
} from "./constants";

interface SweetSpotProps {
  dotScale: number;
  glowOpacity: number;
  labelOpacity: number;
  overallOpacity: number;
}

export const SweetSpot: React.FC<SweetSpotProps> = ({
  dotScale,
  glowOpacity,
  labelOpacity,
  overallOpacity,
}) => {
  const chartWidth = CHART_RIGHT - CHART_LEFT;
  const chartHeight = CHART_BOTTOM - CHART_TOP;

  const cx = CHART_LEFT + SWEET_SPOT.x * chartWidth;
  const cy = CHART_BOTTOM - SWEET_SPOT.y * chartHeight;

  return (
    <div style={{ position: "absolute", top: 0, left: 0, width: 1920, height: 1080, opacity: overallOpacity }}>
      {/* Pulsing glow ring */}
      <div
        style={{
          position: "absolute",
          left: cx - 30,
          top: cy - 30,
          width: 60,
          height: 60,
          borderRadius: "50%",
          backgroundColor: AMBER,
          opacity: glowOpacity * dotScale,
          filter: "blur(12px)",
          transform: `scale(${dotScale})`,
        }}
      />

      {/* Dot */}
      <div
        style={{
          position: "absolute",
          left: cx - 7,
          top: cy - 7,
          width: 14,
          height: 14,
          borderRadius: "50%",
          backgroundColor: AMBER,
          transform: `scale(${dotScale})`,
          boxShadow: `0 0 20px ${AMBER}`,
        }}
      />

      {/* Label with arrow */}
      <div
        style={{
          position: "absolute",
          left: cx - 80,
          top: cy + 28,
          width: 160,
          textAlign: "center",
          opacity: labelOpacity,
        }}
      >
        {/* Upward arrow */}
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontSize: 18,
            color: AMBER,
            lineHeight: "1",
            marginBottom: 2,
          }}
        >
          ▲
        </div>
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontWeight: 700,
            fontSize: 24,
            color: AMBER,
            lineHeight: "1.2",
          }}
        >
          Sweet Spot
        </div>
        <div
          style={{
            fontFamily: FONT_FAMILY,
            fontWeight: 500,
            fontSize: 16,
            color: SWEET_SPOT_SUBLABEL_COLOR,
            marginTop: 4,
          }}
        >
          Optimal Precision
        </div>
      </div>
    </div>
  );
};
