import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  FOOTER_FONT_SIZE,
  WHITE,
  FOOTER_FADE_START,
  FOOTER_FADE_END,
  DISSOLVE_START,
  DISSOLVE_END,
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
    [DISSOLVE_START, DISSOLVE_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
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
        fontWeight: 700,
        fontSize: FOOTER_FONT_SIZE,
        color: WHITE,
        opacity,
        letterSpacing: "0.02em",
      }}
    >
      Stop darning. Start molding.
    </div>
  );
};

export default FooterText;
