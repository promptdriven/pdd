import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  METERS_START,
  METER_FILL_DURATION,
  STATUS_LABEL_START,
  STATUS_LABEL_FADE_DURATION,
  METER_WIDTH,
  METER_HEIGHT,
} from "./constants";

interface CognitiveLoadMeterProps {
  centerX: number;
  centerY: number;
  fillPercent: number;
  color: string;
  status: string;
}

export const CognitiveLoadMeter: React.FC<CognitiveLoadMeterProps> = ({
  centerX,
  centerY,
  fillPercent,
  color,
  status,
}) => {
  const frame = useCurrentFrame();

  if (frame < METERS_START) return null;

  // Meter fade in
  const meterOpacity = interpolate(
    frame,
    [METERS_START, METERS_START + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Fill animation
  const fillWidth = interpolate(
    frame,
    [METERS_START, METERS_START + METER_FILL_DURATION],
    [0, (fillPercent / 100) * METER_WIDTH],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Status label fade
  const statusOpacity = interpolate(
    frame,
    [STATUS_LABEL_START, STATUS_LABEL_START + STATUS_LABEL_FADE_DURATION],
    [0, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: centerX - METER_WIDTH / 2,
        top: centerY - 20,
        width: METER_WIDTH,
        opacity: meterOpacity,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 10,
          color,
          opacity: 0.4,
          marginBottom: 4,
          textAlign: "center",
        }}
      >
        Cognitive load
      </div>

      {/* Meter track */}
      <div
        style={{
          width: METER_WIDTH,
          height: METER_HEIGHT,
          backgroundColor: "rgba(255,255,255,0.05)",
          borderRadius: METER_HEIGHT / 2,
          overflow: "hidden",
          position: "relative",
        }}
      >
        {/* Fill bar */}
        <div
          style={{
            width: fillWidth,
            height: METER_HEIGHT,
            backgroundColor: color,
            opacity: 0.5,
            borderRadius: METER_HEIGHT / 2,
          }}
        />
      </div>

      {/* Status label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 10,
          fontWeight: 700,
          color,
          opacity: statusOpacity,
          marginTop: 4,
          textAlign: "center",
        }}
      >
        {status}
      </div>
    </div>
  );
};
