import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  SECONDARY_COUNTER_START,
  SECONDARY_COUNTER_END,
  SECONDARY_DESC_START,
  SECONDARY_DESC_END,
  SECONDARY_STAT_SIZE,
  SECONDARY_DESC_SIZE,
  ACCENT_RED,
  SECONDARY_DESC_COLOR,
} from "./constants";

export const SecondaryStat: React.FC = () => {
  const frame = useCurrentFrame();

  const counterValue = Math.round(
    interpolate(frame, [SECONDARY_COUNTER_START, SECONDARY_COUNTER_END], [0, 41], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    })
  );

  const statOpacity = interpolate(
    frame,
    [SECONDARY_COUNTER_START, SECONDARY_COUNTER_START + 10],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const descOpacity = interpolate(frame, [SECONDARY_DESC_START, SECONDARY_DESC_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div style={{ marginBottom: 16 }}>
      <div style={{ display: "flex", alignItems: "baseline", gap: 12 }}>
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 900,
            fontSize: SECONDARY_STAT_SIZE,
            color: ACCENT_RED,
            lineHeight: 1,
            opacity: statOpacity,
          }}
        >
          {counterValue}%
        </div>
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontSize: SECONDARY_DESC_SIZE,
            color: SECONDARY_DESC_COLOR,
            opacity: descOpacity,
          }}
        >
          more bugs introduced
        </div>
      </div>
    </div>
  );
};
