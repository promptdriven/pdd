import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  FOOTER_COLOR,
  FOOTER_FONT_SIZE,
  FOOTER_TEXT,
  FOOTER_FADE_START,
  FOOTER_FADE_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
} from "./constants";

export const FooterText: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [FOOTER_FADE_START, FOOTER_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const fadeOut = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );

  const opacity = Math.min(fadeIn, fadeOut);

  return (
    <div
      style={{
        position: "absolute",
        bottom: 30,
        left: 0,
        width: WIDTH,
        textAlign: "center",
        fontFamily: "Inter, sans-serif",
        fontWeight: 600,
        fontSize: FOOTER_FONT_SIZE,
        color: FOOTER_COLOR,
        opacity,
      }}
    >
      {FOOTER_TEXT}
    </div>
  );
};

export default FooterText;
