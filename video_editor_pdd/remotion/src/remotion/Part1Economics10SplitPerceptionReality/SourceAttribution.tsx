import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  SOURCE_COLOR,
  SOURCE_FONT_SIZE,
  SOURCE_TEXT,
  SOURCE_FADE_START,
  SOURCE_FADE_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
} from "./constants";

export const SourceAttribution: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in
  const fadeIn = interpolate(
    frame,
    [SOURCE_FADE_START, SOURCE_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Fade out
  const fadeOut = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const opacity = Math.min(fadeIn, fadeOut);

  return (
    <div
      style={{
        position: "absolute",
        bottom: 40,
        left: 0,
        width: WIDTH,
        textAlign: "center",
        fontFamily: "Inter, sans-serif",
        fontWeight: 400,
        fontSize: SOURCE_FONT_SIZE,
        color: SOURCE_COLOR,
        opacity,
      }}
    >
      {SOURCE_TEXT}
    </div>
  );
};

export default SourceAttribution;
