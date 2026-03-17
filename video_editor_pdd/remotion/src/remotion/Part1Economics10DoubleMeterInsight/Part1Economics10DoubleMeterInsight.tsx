import React from "react";
import { AbsoluteFill, Sequence, useCurrentFrame, interpolate } from "remotion";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  LEFT_METER_X,
  RIGHT_METER_X,
  LEFT_COLOR,
  RIGHT_COLOR,
  LEFT_LABEL,
  RIGHT_LABEL,
  LEFT_SCALE_MARKERS,
  RIGHT_SCALE_MARKERS,
  LEFT_MAX_VALUE,
  RIGHT_MAX_VALUE,
  STILLNESS_END,
} from "./constants";
import { VerticalMeter } from "./VerticalMeter";
import { CenterText } from "./CenterText";

export const defaultPart1Economics10DoubleMeterInsightProps = {};

/**
 * Part1Economics10DoubleMeterInsight
 *
 * "Double Meter Insight" — The key insight beat for Part 1.
 * Two side-by-side vertical meters (Effective Context Window + Model Performance)
 * fill simultaneously, then pulse at peak. Center text reveals:
 * "Bigger window AND smarter model." followed by summary and challenge.
 *
 * Duration: 750 frames @ 30fps (25s)
 */
export const Part1Economics10DoubleMeterInsight: React.FC = () => {
  const frame = useCurrentFrame();

  // Vignette that settles during stillness beat
  const vignetteOpacity = interpolate(
    frame,
    [0, STILLNESS_END],
    [0.35, 0.2],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Vignette overlay — visible from frame 0 for the stillness beat */}
        <div
          style={{
            position: "absolute",
            inset: 0,
            background: `radial-gradient(ellipse at center, transparent 50%, rgba(0,0,0,${vignetteOpacity}) 100%)`,
            pointerEvents: "none",
            zIndex: 0,
          }}
        />

        {/* Left Meter — Effective Context Window */}
        <VerticalMeter
          x={LEFT_METER_X}
          label={LEFT_LABEL}
          color={LEFT_COLOR}
          scaleMarkers={LEFT_SCALE_MARKERS}
          maxValue={LEFT_MAX_VALUE}
          valuePrefix=""
          valueSuffix="×"
        />

        {/* Right Meter — Model Performance */}
        <VerticalMeter
          x={RIGHT_METER_X}
          label={RIGHT_LABEL}
          color={RIGHT_COLOR}
          scaleMarkers={RIGHT_SCALE_MARKERS}
          maxValue={RIGHT_MAX_VALUE}
          valuePrefix="+"
          valueSuffix="%"
        />

        {/* Center text, summary, and challenge */}
        <CenterText />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics10DoubleMeterInsight;
