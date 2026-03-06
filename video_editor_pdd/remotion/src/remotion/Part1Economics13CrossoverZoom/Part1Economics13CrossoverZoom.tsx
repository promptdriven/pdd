import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { ChartSnapshot } from "./ChartSnapshot";
import { Starburst } from "./Starburst";
import { CalloutPill } from "./CalloutPill";
import {
  BG_COLOR,
  CROSSOVER_PX_X,
  CROSSOVER_PX_Y,
  ZOOM_SCALE,
  ZOOM_START,
  ZOOM_END,
  CALLOUT_A_START,
  CALLOUT_B_START,
  FADE_START,
  FADE_END,
} from "./constants";

export const defaultPart1Economics13CrossoverZoomProps = {};

export const Part1Economics13CrossoverZoom: React.FC = () => {
  const frame = useCurrentFrame();

  // Zoom: scale 1.0 → 2.5, easeInOutCubic, frames 0-40
  const zoomScale = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [1.0, ZOOM_SCALE],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Translate to keep crossover centered during zoom
  const centerX = 960; // half of 1920
  const centerY = 540; // half of 1080
  const translateX = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [0, -(CROSSOVER_PX_X - centerX) * (ZOOM_SCALE - 1)],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );
  const translateY = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [0, -(CROSSOVER_PX_Y - centerY) * (ZOOM_SCALE - 1)],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Fade to black: frames 180-210
  const fadeOpacity = interpolate(
    frame,
    [FADE_START, FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Zooming chart container */}
      <AbsoluteFill
        style={{
          transform: `translate(${translateX}px, ${translateY}px) scale(${zoomScale})`,
          transformOrigin: `${CROSSOVER_PX_X}px ${CROSSOVER_PX_Y}px`,
        }}
      >
        {/* Static chart at final drawn state */}
        <ChartSnapshot />

        {/* Starburst at crossover */}
        <Starburst />
      </AbsoluteFill>

      {/* Callout A: above crossover, slides from right */}
      <CalloutPill
        text="Generation cost has crossed below both lines"
        textColor="#FFFFFF"
        position="top-right"
        appearFrame={CALLOUT_A_START}
        slideDuration={30}
      />

      {/* Callout B: below crossover, slides from left */}
      <CalloutPill
        text="80-90% of software cost is maintenance"
        textColor="#F59E0B"
        position="bottom-left"
        appearFrame={CALLOUT_B_START}
        slideDuration={30}
      />

      {/* Fade to black overlay */}
      <AbsoluteFill
        style={{
          backgroundColor: "#000000",
          opacity: fadeOpacity,
        }}
      />
    </AbsoluteFill>
  );
};

export default Part1Economics13CrossoverZoom;
