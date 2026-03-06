import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  SOURCE_COLOR,
  FONT_FAMILY,
  SOURCE_SIZE,
  SOURCE_FADE_START,
  SOURCE_FADE_END,
  PANEL_SLIDE_OUT_START,
  PANEL_SLIDE_OUT_END,
} from "./constants";

export const SourceAttribution: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [SOURCE_FADE_START, SOURCE_FADE_END, PANEL_SLIDE_OUT_START, PANEL_SLIDE_OUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) },
  );

  return (
    <div
      style={{
        position: "absolute",
        bottom: 40,
        left: 0,
        width: WIDTH,
        textAlign: "center",
        fontFamily: FONT_FAMILY,
        fontWeight: 400,
        fontSize: SOURCE_SIZE,
        color: SOURCE_COLOR,
        opacity,
      }}
    >
      METR Study, 2024
    </div>
  );
};

export default SourceAttribution;
