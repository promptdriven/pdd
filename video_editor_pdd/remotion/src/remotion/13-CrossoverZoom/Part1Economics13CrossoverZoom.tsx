import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { StaticChart } from "./StaticChart";
import { Starburst } from "./Starburst";
import { CalloutPill } from "./CalloutPill";
import {
  BG_COLOR,
  CROSSOVER_PX_X,
  CROSSOVER_PX_Y,
  CENTER_X,
  CENTER_Y,
  ZOOM_SCALE_TARGET,
  ZOOM_START,
  ZOOM_END,
  CALLOUT_A_START,
  CALLOUT_A_ANIM_DURATION,
  CALLOUT_B_START,
  CALLOUT_B_ANIM_DURATION,
  CALLOUT_A_COLOR,
  CALLOUT_B_COLOR,
  FADE_TO_BLACK_START,
  FADE_TO_BLACK_END,
} from "./constants";

export const defaultPart1Economics13CrossoverZoomProps = {};

export const Part1Economics13CrossoverZoom: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Zoom animation: scale 1.0 → 2.5 centered on crossover point ---
  const zoomProgress = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const zoomScale = 1.0 + (ZOOM_SCALE_TARGET - 1.0) * zoomProgress;
  // Translate so crossover point stays at screen center during zoom
  const translateX = (CENTER_X - CROSSOVER_PX_X) * zoomProgress;
  const translateY = (CENTER_Y - CROSSOVER_PX_Y) * zoomProgress;

  // --- Fade to black: frames 180-210 ---
  const fadeToBlack = interpolate(
    frame,
    [FADE_TO_BLACK_START, FADE_TO_BLACK_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Zooming chart layer */}
      <AbsoluteFill
        style={{
          transform: `translate(${translateX}px, ${translateY}px) scale(${zoomScale})`,
          transformOrigin: `${CROSSOVER_PX_X}px ${CROSSOVER_PX_Y}px`,
        }}
      >
        {/* Static (fully-drawn) chart */}
        <StaticChart />
      </AbsoluteFill>

      {/* Starburst at crossover — rendered in zoom-transformed space */}
      <AbsoluteFill
        style={{
          transform: `translate(${translateX}px, ${translateY}px) scale(${zoomScale})`,
          transformOrigin: `${CROSSOVER_PX_X}px ${CROSSOVER_PX_Y}px`,
        }}
      >
        <Starburst />
      </AbsoluteFill>

      {/* Callout A: "Generation cost has crossed below both lines" */}
      {/* Positioned in screen space (not zoomed) so text stays readable */}
      <AbsoluteFill>
        <CalloutPill
          text="Generation cost has crossed below both lines"
          textColor={CALLOUT_A_COLOR}
          fontSize={28}
          appearFrame={CALLOUT_A_START}
          animDuration={CALLOUT_A_ANIM_DURATION}
          offsetX={160}
          offsetY={-120}
          slideFromX={60}
        />
      </AbsoluteFill>

      {/* Callout B: "80-90% of software cost is maintenance" */}
      <AbsoluteFill>
        <CalloutPill
          text="80-90% of software cost is maintenance"
          textColor={CALLOUT_B_COLOR}
          fontSize={26}
          appearFrame={CALLOUT_B_START}
          animDuration={CALLOUT_B_ANIM_DURATION}
          offsetX={-160}
          offsetY={100}
          slideFromX={-60}
        />
      </AbsoluteFill>

      {/* Fade to black overlay */}
      <AbsoluteFill
        style={{
          backgroundColor: "#000000",
          opacity: fadeToBlack,
        }}
      />
    </AbsoluteFill>
  );
};

export default Part1Economics13CrossoverZoom;
