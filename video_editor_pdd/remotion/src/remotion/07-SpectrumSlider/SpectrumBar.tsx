import React from "react";
import { interpolate } from "remotion";
import {
  BAR_Y,
  BAR_X_START,
  BAR_WIDTH,
  BAR_HEIGHT,
  BAR_RADIUS,
  TICK_COUNT,
  TICK_WIDTH,
  TICK_HEIGHT,
  TICK_COLOR,
  TICK_OPACITY,
  BLUE,
  GRAY,
  AMBER,
  BALANCED_DIM,
  BALANCED_BRIGHT,
  FONT_FAMILY,
} from "./constants";

interface SpectrumBarProps {
  barExpandProgress: number;
  barOpacity: number;
  labelsOpacity: number;
  ticksOpacity: number;
  balancedBrightness: number;
}

export const SpectrumBar: React.FC<SpectrumBarProps> = ({
  barExpandProgress,
  barOpacity,
  labelsOpacity,
  ticksOpacity,
  balancedBrightness,
}) => {
  const currentWidth = barExpandProgress * BAR_WIDTH;
  const barCenterX = BAR_X_START + BAR_WIDTH / 2;

  // Interpolate balanced label color
  const balancedColor = interpolate(balancedBrightness, [0, 1], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  // Manual hex interpolation: #94A3B8 → #CBD5E1
  const r = Math.round(0x94 + (0xcb - 0x94) * balancedColor);
  const g = Math.round(0xa3 + (0xd5 - 0xa3) * balancedColor);
  const b = Math.round(0xb8 + (0xe1 - 0xb8) * balancedColor);
  const balancedHex = `rgb(${r}, ${g}, ${b})`;

  // Generate tick positions
  const ticks = [];
  for (let i = 1; i < TICK_COUNT + 1; i++) {
    const x = BAR_X_START + (BAR_WIDTH / (TICK_COUNT + 1)) * i;
    ticks.push(x);
  }

  return (
    <>
      {/* Background track */}
      <div
        style={{
          position: "absolute",
          left: barCenterX - currentWidth / 2,
          top: BAR_Y - BAR_HEIGHT / 2,
          width: currentWidth,
          height: BAR_HEIGHT,
          borderRadius: BAR_RADIUS,
          background: "rgba(255, 255, 255, 0.1)",
          opacity: barOpacity,
        }}
      />

      {/* Gradient fill */}
      <div
        style={{
          position: "absolute",
          left: barCenterX - currentWidth / 2,
          top: BAR_Y - BAR_HEIGHT / 2,
          width: currentWidth,
          height: BAR_HEIGHT,
          borderRadius: BAR_RADIUS,
          background: `linear-gradient(to right, ${BLUE}, ${GRAY}, ${AMBER})`,
          opacity: barOpacity,
        }}
      />

      {/* Tick marks */}
      {ticks.map((x, i) => (
        <div
          key={i}
          style={{
            position: "absolute",
            left: x - TICK_WIDTH / 2,
            top: BAR_Y - TICK_HEIGHT / 2,
            width: TICK_WIDTH,
            height: TICK_HEIGHT,
            backgroundColor: TICK_COLOR,
            opacity: ticksOpacity * TICK_OPACITY,
            borderRadius: 1,
          }}
        />
      ))}

      {/* EXPLORATION label (left) */}
      <div
        style={{
          position: "absolute",
          left: BAR_X_START,
          top: BAR_Y - 50,
          fontFamily: FONT_FAMILY,
          fontWeight: 700,
          fontSize: 18,
          color: BLUE,
          letterSpacing: "0.15em",
          textTransform: "uppercase" as const,
          opacity: labelsOpacity,
        }}
      >
        EXPLORATION
      </div>

      {/* ENFORCEMENT label (right) */}
      <div
        style={{
          position: "absolute",
          right: 1920 - BAR_X_START - BAR_WIDTH,
          top: BAR_Y - 50,
          fontFamily: FONT_FAMILY,
          fontWeight: 700,
          fontSize: 18,
          color: AMBER,
          letterSpacing: "0.15em",
          textTransform: "uppercase" as const,
          textAlign: "right" as const,
          opacity: labelsOpacity,
        }}
      >
        ENFORCEMENT
      </div>

      {/* BALANCED label (center) */}
      <div
        style={{
          position: "absolute",
          left: BAR_X_START + BAR_WIDTH / 2,
          top: BAR_Y - 50,
          transform: "translateX(-50%)",
          fontFamily: FONT_FAMILY,
          fontWeight: 700,
          fontSize: 18,
          color: balancedHex,
          letterSpacing: "0.15em",
          textTransform: "uppercase" as const,
          textAlign: "center" as const,
          opacity: labelsOpacity,
        }}
      >
        BALANCED
      </div>
    </>
  );
};
