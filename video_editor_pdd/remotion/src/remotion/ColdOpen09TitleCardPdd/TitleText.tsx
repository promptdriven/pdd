import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TITLE_COLOR,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_FONT_FAMILY,
  TITLE_LINE1_Y,
  TITLE_LINE2_Y,
  TITLE_LINE2_OFFSET_X,
  CANVAS_WIDTH,
  LINE1_FADE_START,
  LINE1_FADE_END,
  LINE2_FADE_START,
  LINE2_FADE_END,
  SLIDE_DISTANCE,
} from "./constants";

/** "PROMPT-DRIVEN" title line */
export const TitleLine1: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [LINE1_FADE_START, LINE1_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const translateY = interpolate(
    frame,
    [LINE1_FADE_START, LINE1_FADE_END],
    [SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: TITLE_LINE1_Y,
        left: 0,
        width: CANVAS_WIDTH,
        textAlign: "center",
        opacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: TITLE_FONT_FAMILY,
        fontSize: TITLE_FONT_SIZE,
        fontWeight: TITLE_FONT_WEIGHT,
        color: TITLE_COLOR,
        letterSpacing: 4,
      }}
    >
      PROMPT-DRIVEN
    </div>
  );
};

/** "DEVELOPMENT" title line */
export const TitleLine2: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [LINE2_FADE_START, LINE2_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const translateY = interpolate(
    frame,
    [LINE2_FADE_START, LINE2_FADE_END],
    [SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: TITLE_LINE2_Y,
        left: TITLE_LINE2_OFFSET_X,
        width: CANVAS_WIDTH,
        textAlign: "center",
        opacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: TITLE_FONT_FAMILY,
        fontSize: TITLE_FONT_SIZE,
        fontWeight: TITLE_FONT_WEIGHT,
        color: TITLE_COLOR,
        letterSpacing: 4,
      }}
    >
      DEVELOPMENT
    </div>
  );
};
