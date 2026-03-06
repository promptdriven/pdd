import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  PRIMARY_STAT_START,
  PRIMARY_STAT_END,
  PRIMARY_DESC_START,
  PRIMARY_DESC_END,
  PRIMARY_STAT_SIZE,
  PRIMARY_DESC_SIZE,
  PRIMARY_STAT_COLOR,
  PRIMARY_DESC_COLOR,
} from "./constants";

export const PrimaryStat: React.FC = () => {
  const frame = useCurrentFrame();

  const statOpacity = interpolate(frame, [PRIMARY_STAT_START, PRIMARY_STAT_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const statScale = interpolate(frame, [PRIMARY_STAT_START, PRIMARY_STAT_END], [0.85, 1.0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const descOpacity = interpolate(frame, [PRIMARY_DESC_START, PRIMARY_DESC_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div style={{ marginBottom: 16 }}>
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 900,
          fontSize: PRIMARY_STAT_SIZE,
          color: PRIMARY_STAT_COLOR,
          lineHeight: 1,
          opacity: statOpacity,
          transform: `scale(${statScale})`,
          transformOrigin: "left center",
        }}
      >
        0%
      </div>
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 500,
          fontSize: PRIMARY_DESC_SIZE,
          color: PRIMARY_DESC_COLOR,
          opacity: descOpacity,
          marginTop: 4,
        }}
      >
        throughput change
      </div>
    </div>
  );
};
