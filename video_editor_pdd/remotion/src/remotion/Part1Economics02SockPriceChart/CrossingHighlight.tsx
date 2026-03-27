import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CROSSING_YEAR,
  LABOR_COST_DATA,
  GARMENT_COST_DATA,
  CROSSING_GLOW_COLOR,
  THRESHOLD_LABEL_COLOR,
  DARNING_SENSE_COLOR,
  DARNING_IRRATIONAL_COLOR,
  THRESHOLD_LABEL_START,
  THRESHOLD_LABEL_END,
  ZONE_LABEL_START,
  ZONE_LABEL_DURATION,
  xToPixel,
  yToPixel,
  interpolateData,
} from "./constants";

export const CrossingHighlight: React.FC = () => {
  const frame = useCurrentFrame();

  // Compute the crossing point pixel position
  const crossingY = interpolateData(LABOR_COST_DATA, CROSSING_YEAR);
  const crossingPx = xToPixel(CROSSING_YEAR);
  const crossingPy = yToPixel(crossingY);

  // Threshold label animation (frames 150–180): scale from 1.05 → 1.0
  const thresholdProgress = interpolate(
    frame,
    [THRESHOLD_LABEL_START, THRESHOLD_LABEL_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const thresholdOpacity = interpolate(
    frame,
    [THRESHOLD_LABEL_START, THRESHOLD_LABEL_START + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const thresholdScale = interpolate(
    frame,
    [THRESHOLD_LABEL_START, THRESHOLD_LABEL_END],
    [1.05, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Glow pulse
  const glowPulse =
    thresholdOpacity > 0
      ? interpolate(
          frame,
          [THRESHOLD_LABEL_START, THRESHOLD_LABEL_START + 20, THRESHOLD_LABEL_START + 40],
          [0, 0.25, 0.15],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        )
      : 0;

  // Zone labels (frame 180+)
  const zoneOpacity = interpolate(
    frame,
    [ZONE_LABEL_START, ZONE_LABEL_START + ZONE_LABEL_DURATION],
    [0, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  if (frame < THRESHOLD_LABEL_START) return null;

  return (
    <>
      {/* Radial glow at crossing point */}
      <div
        style={{
          position: "absolute",
          left: crossingPx - 40,
          top: crossingPy - 40,
          width: 80,
          height: 80,
          borderRadius: "50%",
          background: `radial-gradient(circle, ${CROSSING_GLOW_COLOR} 0%, transparent 70%)`,
          opacity: glowPulse,
          pointerEvents: "none",
        }}
      />

      {/* Crossing dot */}
      <div
        style={{
          position: "absolute",
          left: crossingPx - 5,
          top: crossingPy - 5,
          width: 10,
          height: 10,
          borderRadius: "50%",
          backgroundColor: CROSSING_GLOW_COLOR,
          opacity: thresholdOpacity * 0.9,
          boxShadow: `0 0 12px 4px ${CROSSING_GLOW_COLOR}40`,
        }}
      />

      {/* "The Threshold" label */}
      <div
        style={{
          position: "absolute",
          left: crossingPx - 80,
          top: crossingPy - 55,
          opacity: thresholdOpacity,
          transform: `scale(${thresholdScale})`,
          transformOrigin: "center bottom",
          pointerEvents: "none",
        }}
      >
        {/* Connecting line from label to dot */}
        <div
          style={{
            position: "absolute",
            left: 80,
            top: 28,
            width: 2,
            height: 16,
            backgroundColor: THRESHOLD_LABEL_COLOR,
            opacity: 0.4,
          }}
        />
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 18,
            fontWeight: 700,
            color: THRESHOLD_LABEL_COLOR,
            whiteSpace: "nowrap",
          }}
        >
          The Threshold
        </span>
      </div>

      {/* "Darning makes sense" label — left of crossing */}
      <div
        style={{
          position: "absolute",
          left: crossingPx - 210,
          top: crossingPy + 20,
          opacity: zoneOpacity,
          pointerEvents: "none",
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 13,
            fontWeight: 400,
            color: DARNING_SENSE_COLOR,
            whiteSpace: "nowrap",
          }}
        >
          Darning makes sense
        </span>
      </div>

      {/* "Darning is irrational" label — right of crossing */}
      <div
        style={{
          position: "absolute",
          left: crossingPx + 50,
          top: crossingPy + 20,
          opacity: zoneOpacity,
          pointerEvents: "none",
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 13,
            fontWeight: 400,
            color: DARNING_IRRATIONAL_COLOR,
            whiteSpace: "nowrap",
          }}
        >
          Darning is irrational
        </span>
      </div>
    </>
  );
};

export default CrossingHighlight;
