import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { SOURCE_FADE_START, SOURCE_FADE_END, SOURCE_SIZE, SOURCE_COLOR } from "./constants";

export const SourceAttribution: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [SOURCE_FADE_START, SOURCE_FADE_END], [0, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        fontFamily: "Inter, sans-serif",
        fontWeight: 400,
        fontSize: SOURCE_SIZE,
        color: SOURCE_COLOR,
        opacity,
        marginTop: 8,
      }}
    >
      Uplevel Study — 800 developers, 6 months
    </div>
  );
};
