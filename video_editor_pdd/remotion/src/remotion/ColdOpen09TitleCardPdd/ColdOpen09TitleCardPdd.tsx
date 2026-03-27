import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  BG_COLOR,
  OVERLAY_TARGET_OPACITY,
  OVERLAY_START,
  OVERLAY_END,
} from "./constants";
import { BackgroundCode } from "./BackgroundCode";
import { TitleText } from "./TitleText";
import { HorizontalRule } from "./HorizontalRule";

export const defaultColdOpen09TitleCardPddProps = {};

export const ColdOpen09TitleCardPdd: React.FC = () => {
  const frame = useCurrentFrame();

  // Darkening overlay fades in over frames 0-10
  const overlayOpacity = interpolate(
    frame,
    [OVERLAY_START, OVERLAY_END],
    [0, OVERLAY_TARGET_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Background: regenerated code at low opacity */}
      <BackgroundCode />

      {/* Darkening overlay that fades in */}
      <AbsoluteFill
        style={{
          backgroundColor: BG_COLOR,
          opacity: overlayOpacity,
        }}
      />

      {/* Title text: PROMPT-DRIVEN and DEVELOPMENT */}
      <TitleText />

      {/* Horizontal rule + accent glow */}
      <HorizontalRule />
    </AbsoluteFill>
  );
};

export default ColdOpen09TitleCardPdd;
