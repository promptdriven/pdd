import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  RATIO_FADE_START,
  RATIO_FADE_END,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const RatioCallout: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [RATIO_FADE_START, RATIO_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const scale = interpolate(
    frame,
    [RATIO_FADE_START, RATIO_FADE_END],
    [0.8, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        right: 0,
        top: 0,
        bottom: 0,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        pointerEvents: "none",
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 900,
          fontSize: 48,
          color: "#FFFFFF",
          opacity,
          transform: `scale(${scale})`,
          textShadow: "0 4px 24px rgba(255, 255, 255, 0.3)",
        }}
      >
        ~6x
      </div>
    </div>
  );
};

export default RatioCallout;
