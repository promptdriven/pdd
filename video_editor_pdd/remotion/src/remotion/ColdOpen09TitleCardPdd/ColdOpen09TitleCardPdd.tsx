import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BG_COLOR,
  OVERLAY_OPACITY,
  OVERLAY_FADE_START,
  OVERLAY_FADE_END,
} from "./constants";
import { BackgroundCode } from "./BackgroundCode";
import { TitleLine1, TitleLine2 } from "./TitleText";
import { HorizontalRule } from "./HorizontalRule";

export const defaultColdOpen09TitleCardPddProps = {};

export const ColdOpen09TitleCardPdd: React.FC = () => {
  const frame = useCurrentFrame();

  // Darkening overlay fades in over frames 0-10
  const overlayOpacity = interpolate(
    frame,
    [OVERLAY_FADE_START, OVERLAY_FADE_END],
    [0, OVERLAY_OPACITY],
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
        width: 1920,
        height: 1080,
      }}
    >
      {/* Layer 1: Background code at low opacity */}
      <BackgroundCode />

      {/* Layer 2: Darkening overlay that fades in */}
      <AbsoluteFill
        style={{
          backgroundColor: BG_COLOR,
          opacity: overlayOpacity,
        }}
      />

      {/* Layer 3: Title elements */}
      <AbsoluteFill>
        <TitleLine1 />
        <HorizontalRule />
        <TitleLine2 />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default ColdOpen09TitleCardPdd;
