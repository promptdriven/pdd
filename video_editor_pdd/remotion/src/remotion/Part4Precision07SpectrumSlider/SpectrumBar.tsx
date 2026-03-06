import React from "react";
import {
  BAR_X,
  BAR_Y,
  BAR_WIDTH,
  BAR_HEIGHT,
  BAR_RADIUS,
  TRACK_BG,
  BLUE,
  GRAY,
  AMBER,
  TICK_COUNT,
  TICK_WIDTH,
  TICK_HEIGHT,
  TICK_COLOR,
  FONT_FAMILY,
  LABEL_FONT_SIZE,
  LABEL_LETTER_SPACING,
  BALANCED_DIM,
} from "./constants";

interface SpectrumBarProps {
  barWidth: number;
  barOpacity: number;
  labelsOpacity: number;
  ticksOpacity: number;
  balancedColor: string;
}

export const SpectrumBar: React.FC<SpectrumBarProps> = ({
  barWidth,
  barOpacity,
  labelsOpacity,
  ticksOpacity,
  balancedColor,
}) => {
  const barCenterX = BAR_X + BAR_WIDTH / 2;
  const currentBarLeft = barCenterX - barWidth / 2;

  // Generate tick positions (evenly spaced along the bar)
  const ticks: number[] = [];
  for (let i = 1; i <= TICK_COUNT; i++) {
    ticks.push(BAR_X + (BAR_WIDTH / (TICK_COUNT + 1)) * i);
  }

  return (
    <>
      {/* Background track (always full width once visible) */}
      <div
        style={{
          position: "absolute",
          left: BAR_X,
          top: BAR_Y,
          width: BAR_WIDTH,
          height: BAR_HEIGHT,
          borderRadius: BAR_RADIUS,
          backgroundColor: TRACK_BG,
          opacity: barOpacity,
        }}
      />

      {/* Gradient fill (expanding from center) */}
      <div
        style={{
          position: "absolute",
          left: currentBarLeft,
          top: BAR_Y,
          width: barWidth,
          height: BAR_HEIGHT,
          borderRadius: BAR_RADIUS,
          background: `linear-gradient(to right, ${BLUE}, ${GRAY}, ${AMBER})`,
          opacity: barOpacity,
          overflow: "hidden",
        }}
      />

      {/* Tick marks */}
      {ticks.map((tickX, i) => (
        <div
          key={i}
          style={{
            position: "absolute",
            left: tickX - TICK_WIDTH / 2,
            top: BAR_Y - (TICK_HEIGHT - BAR_HEIGHT) / 2,
            width: TICK_WIDTH,
            height: TICK_HEIGHT,
            borderRadius: 1,
            backgroundColor: TICK_COLOR,
            opacity: ticksOpacity,
          }}
        />
      ))}

      {/* Label: EXPLORATION (left) */}
      <div
        style={{
          position: "absolute",
          left: BAR_X,
          top: BAR_Y - 36,
          fontFamily: FONT_FAMILY,
          fontWeight: 700,
          fontSize: LABEL_FONT_SIZE,
          letterSpacing: LABEL_LETTER_SPACING,
          color: BLUE,
          opacity: labelsOpacity,
          textTransform: "uppercase" as const,
        }}
      >
        EXPLORATION
      </div>

      {/* Label: ENFORCEMENT (right) */}
      <div
        style={{
          position: "absolute",
          right: 1920 - (BAR_X + BAR_WIDTH),
          top: BAR_Y - 36,
          fontFamily: FONT_FAMILY,
          fontWeight: 700,
          fontSize: LABEL_FONT_SIZE,
          letterSpacing: LABEL_LETTER_SPACING,
          color: AMBER,
          opacity: labelsOpacity,
          textAlign: "right" as const,
          textTransform: "uppercase" as const,
        }}
      >
        ENFORCEMENT
      </div>

      {/* Label: BALANCED (center) */}
      <div
        style={{
          position: "absolute",
          left: barCenterX - 60,
          top: BAR_Y - 36,
          width: 120,
          fontFamily: FONT_FAMILY,
          fontWeight: 700,
          fontSize: LABEL_FONT_SIZE,
          letterSpacing: LABEL_LETTER_SPACING,
          color: balancedColor,
          opacity: labelsOpacity,
          textAlign: "center" as const,
          textTransform: "uppercase" as const,
        }}
      >
        BALANCED
      </div>
    </>
  );
};
