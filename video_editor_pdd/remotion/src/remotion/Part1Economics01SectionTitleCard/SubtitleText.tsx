import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  SUBTITLE_TEXT,
  SUBTITLE_FADE_START,
  SUBTITLE_FADE_END,
  SUBTITLE_Y,
  SLATE_TEXT,
  SUBTITLE_FONT_SIZE,
  SUBTITLE_FONT_WEIGHT,
  SUBTITLE_OPACITY,
} from "./constants";

export const SubtitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [SUBTITLE_FADE_START, SUBTITLE_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: SUBTITLE_Y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        opacity: fadeIn * SUBTITLE_OPACITY,
        fontFamily: "'Inter', sans-serif",
        fontWeight: SUBTITLE_FONT_WEIGHT,
        fontSize: SUBTITLE_FONT_SIZE,
        fontStyle: "italic",
        color: SLATE_TEXT,
        textAlign: "center" as const,
      }}
    >
      {SUBTITLE_TEXT}
    </div>
  );
};

export default SubtitleText;
