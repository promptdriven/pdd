import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CAPTION_COLOR,
  CAPTION_OPACITY,
  CAPTION_FONT_SIZE,
  CAPTION_Y,
  CAPTION_FADE_START,
  CAPTION_FADE_DUR,
} from "./constants";

export const PanelCaption: React.FC<{
  side: "left" | "right";
}> = ({ side }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [CAPTION_FADE_START, CAPTION_FADE_START + CAPTION_FADE_DUR],
    [0, CAPTION_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (side === "left") {
    return (
      <div
        style={{
          position: "absolute",
          bottom: 1080 - CAPTION_Y - 20,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: CAPTION_FONT_SIZE,
          fontStyle: "italic",
          color: CAPTION_COLOR,
          opacity,
          padding: "0 24px",
        }}
      >
        The economics made it rational.
      </div>
    );
  }

  // Right panel — "Until now" emphasized
  return (
    <div
      style={{
        position: "absolute",
        bottom: 1080 - CAPTION_Y - 20,
        left: 0,
        width: "100%",
        textAlign: "center",
        fontFamily: "Inter, sans-serif",
        fontSize: CAPTION_FONT_SIZE,
        fontStyle: "italic",
        color: CAPTION_COLOR,
        opacity,
        padding: "0 24px",
      }}
    >
      <span style={{ opacity: 0.6 / CAPTION_OPACITY }}>Until now, </span>
      <span style={{ color: "#4A90D9", opacity: 0.8 / CAPTION_OPACITY }}>
        the economics made it rational.
      </span>
    </div>
  );
};

export default PanelCaption;
