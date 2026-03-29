import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BG_LIGHTEN_END,
  LEFT_METER_X,
  RIGHT_METER_X,
  LEFT_METER_CONFIG,
  RIGHT_METER_CONFIG,
} from "./constants";
import { VerticalMeter } from "./VerticalMeter";
import { InsightText } from "./InsightText";

export const defaultPart1Economics19DoubleMeterInsightProps = {};

export const Part1Economics19DoubleMeterInsight: React.FC = () => {
  const frame = useCurrentFrame();

  // Background lightens from deep black to dark navy over first 30 frames
  const bgLighten = interpolate(frame, [0, BG_LIGHTEN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Interpolate between BG_DARK and BG_MAIN via rgb
  // #050810 → rgb(5,8,16)  |  #0A0F1A → rgb(10,15,26)
  const r = Math.round(5 + bgLighten * (10 - 5));
  const g = Math.round(8 + bgLighten * (15 - 8));
  const b = Math.round(16 + bgLighten * (26 - 16));
  const backgroundColor = `rgb(${r},${g},${b})`;

  return (
    <AbsoluteFill
      style={{
        backgroundColor,
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* Left Meter: Effective Context Window */}
      <VerticalMeter
        x={LEFT_METER_X}
        title={LEFT_METER_CONFIG.title}
        fillColor={LEFT_METER_CONFIG.fillColor}
        bottomLabel={LEFT_METER_CONFIG.bottomLabel}
        topLabel={LEFT_METER_CONFIG.topLabel}
        bottomFontSize={LEFT_METER_CONFIG.bottomFontSize}
      />

      {/* Right Meter: Model Performance */}
      <VerticalMeter
        x={RIGHT_METER_X}
        title={RIGHT_METER_CONFIG.title}
        fillColor={RIGHT_METER_CONFIG.fillColor}
        bottomLabel={RIGHT_METER_CONFIG.bottomLabel}
        topLabel={RIGHT_METER_CONFIG.topLabel}
        bottomFontSize={RIGHT_METER_CONFIG.bottomFontSize}
      />

      {/* Insight text: "Bigger window AND smarter model." */}
      <InsightText />
    </AbsoluteFill>
  );
};

export default Part1Economics19DoubleMeterInsight;
