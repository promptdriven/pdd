import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  SUBTITLE_TEXT,
  SUBTITLE_FONT_SIZE,
  SUBTITLE_FONT_WEIGHT,
  SUBTITLE_COLOR,
  SUBTITLE_OPACITY,
  SUBTITLE_Y,
  SUBTITLE_START_FRAME,
  SUBTITLE_FADE_DURATION,
  TITLE_FONT_FAMILY,
  CANVAS_WIDTH,
} from "./constants";

/**
 * Subtitle: "Writing the mold, not the plastic."
 * Fades in at frame 80 with easeOut(quad) over 20 frames.
 * Italic, light weight, muted color.
 */
export const Subtitle: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - SUBTITLE_START_FRAME;
  if (localFrame < 0) return null;

  const opacity = interpolate(
    localFrame,
    [0, SUBTITLE_FADE_DURATION],
    [0, SUBTITLE_OPACITY],
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
        width: CANVAS_WIDTH,
        display: "flex",
        justifyContent: "center",
        opacity,
        pointerEvents: "none",
      }}
    >
      <span
        style={{
          fontFamily: TITLE_FONT_FAMILY,
          fontSize: SUBTITLE_FONT_SIZE,
          fontWeight: SUBTITLE_FONT_WEIGHT,
          fontStyle: "italic",
          color: SUBTITLE_COLOR,
        }}
      >
        {SUBTITLE_TEXT}
      </span>
    </div>
  );
};
