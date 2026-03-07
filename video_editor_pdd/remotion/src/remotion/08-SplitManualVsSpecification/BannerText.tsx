import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BANNER_TEXT,
  BANNER_Y,
  BANNER_COLOR,
  BANNER_FADE_START,
  BANNER_FADE_END,
  FADEOUT_START,
  FADEOUT_END,
  WIDTH,
} from "./constants";

export const BannerText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [BANNER_FADE_START, BANNER_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  const translateY = interpolate(
    frame,
    [BANNER_FADE_START, BANNER_FADE_END],
    [10, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: "absolute",
        top: BANNER_Y,
        left: 0,
        width: WIDTH,
        textAlign: "center",
        fontFamily: "Inter, sans-serif",
        fontWeight: 600,
        fontSize: 26,
        color: BANNER_COLOR,
        fontStyle: "italic",
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {BANNER_TEXT}
    </div>
  );
};

export default BannerText;
