import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  interpolateColors,
  OffthreadVideo,
  spring,
  staticFile,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";
import { SpectrumBar } from "./SpectrumBar";
import { SpectrumHandle } from "./SpectrumHandle";
import { ContextCard } from "./ContextCard";
import {
  BG_COLOR,
  BAR_WIDTH,
  BLUE,
  AMBER,
  BLUE_BG,
  BLUE_BORDER,
  AMBER_BG,
  AMBER_BORDER,
  BALANCED_DIM,
  BALANCED_BRIGHT,
  CENTER_POS,
  LEFT_POS,
  RIGHT_POS,
  BAR_FADE_START,
  BAR_FADE_END,
  LABELS_FADE_START,
  LABELS_FADE_END,
  TICKS_FADE_START,
  TICKS_FADE_END,
  HANDLE_APPEAR_START,
  HANDLE_SLIDE_LEFT_START,
  HANDLE_SLIDE_LEFT_END,
  HANDLE_SLIDE_RIGHT_START,
  HANDLE_SLIDE_RIGHT_END,
  HANDLE_SLIDE_CENTER_START,
  HANDLE_SLIDE_CENTER_END,
  GREENFIELD_CARD_START,
  GREENFIELD_CARD_FADE_IN_END,
  GREENFIELD_CARD_FADE_OUT_START,
  GREENFIELD_CARD_FADE_OUT_END,
  LEGACY_CARD_START,
  LEGACY_CARD_FADE_IN_END,
  LEGACY_CARD_FADE_OUT_START,
  LEGACY_CARD_FADE_OUT_END,
  BALANCED_BRIGHTEN_START,
  BALANCED_BRIGHTEN_END,
  SCENE_FADE_OUT_START,
  SCENE_FADE_OUT_END,
  HANDLE_SPRING,
} from "./constants";

// Rocket icon SVG path (simple silhouette)
const ROCKET_PATH =
  "M12 2C12 2 7 7 7 12c0 3.5 2 5.5 3.5 6.5L9 22h6l-1.5-3.5C15 17.5 17 15.5 17 12c0-5-5-10-5-10zm0 12a2 2 0 110-4 2 2 0 010 4z";

// Shield/lock icon SVG path (simple silhouette)
const SHIELD_PATH =
  "M12 2L4 5v6.09c0 5.05 3.41 9.76 8 10.91 4.59-1.15 8-5.86 8-10.91V5l-8-3zm0 10.5c-1.38 0-2.5-1.12-2.5-2.5S10.62 7.5 12 7.5s2.5 1.12 2.5 2.5-1.12 2.5-2.5 2.5z";

export const defaultPart4Precision07SpectrumSliderProps = {};

export const Part4Precision07SpectrumSlider: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // --- Scene fade out ---
  const sceneFadeOut = interpolate(
    frame,
    [SCENE_FADE_OUT_START, SCENE_FADE_OUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );

  // --- Spectrum bar ---
  const barWidth = interpolate(
    frame,
    [BAR_FADE_START, BAR_FADE_END],
    [0, BAR_WIDTH],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );
  const barOpacity = interpolate(
    frame,
    [BAR_FADE_START, BAR_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  ) * sceneFadeOut;

  // --- Labels ---
  const labelsOpacity = interpolate(
    frame,
    [LABELS_FADE_START, LABELS_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  ) * sceneFadeOut;

  // --- Ticks ---
  const ticksOpacity = interpolate(
    frame,
    [TICKS_FADE_START, TICKS_FADE_END],
    [0, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  ) * sceneFadeOut;

  // --- Balanced label color ---
  const balancedColor = interpolateColors(
    frame,
    [BALANCED_BRIGHTEN_START, BALANCED_BRIGHTEN_END],
    [BALANCED_DIM, BALANCED_BRIGHT]
  );

  // --- Handle scale (spring appearance) ---
  const handleScale = frame >= HANDLE_APPEAR_START
    ? spring({
        frame: frame - HANDLE_APPEAR_START,
        fps,
        config: HANDLE_SPRING,
      })
    : 0;

  // --- Handle position (center → left → right → center) ---
  const handlePosition = (() => {
    if (frame < HANDLE_SLIDE_LEFT_START) {
      return CENTER_POS;
    }
    if (frame < HANDLE_SLIDE_LEFT_END) {
      return interpolate(
        frame,
        [HANDLE_SLIDE_LEFT_START, HANDLE_SLIDE_LEFT_END],
        [CENTER_POS, LEFT_POS],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
      );
    }
    if (frame < HANDLE_SLIDE_RIGHT_START) {
      return LEFT_POS;
    }
    if (frame < HANDLE_SLIDE_RIGHT_END) {
      return interpolate(
        frame,
        [HANDLE_SLIDE_RIGHT_START, HANDLE_SLIDE_RIGHT_END],
        [LEFT_POS, RIGHT_POS],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
      );
    }
    if (frame < HANDLE_SLIDE_CENTER_START) {
      return RIGHT_POS;
    }
    if (frame < HANDLE_SLIDE_CENTER_END) {
      return interpolate(
        frame,
        [HANDLE_SLIDE_CENTER_START, HANDLE_SLIDE_CENTER_END],
        [RIGHT_POS, CENTER_POS],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
      );
    }
    return CENTER_POS;
  })();

  // --- Handle glow color (interpolated based on position) ---
  const glowColor = interpolateColors(
    handlePosition,
    [0, 0.17, 0.5, 0.83, 1],
    [BLUE, BLUE, BALANCED_DIM, AMBER, AMBER]
  );

  // --- Glow pulse (sinusoidal, 2s period = 60 frames at 30fps) ---
  const glowPulse = frame >= HANDLE_APPEAR_START
    ? interpolate(
        Math.sin(((frame - HANDLE_APPEAR_START) * Math.PI * 2) / 60),
        [-1, 1],
        [0.25, 0.5]
      )
    : 0.35;

  const handleOpacity = sceneFadeOut;

  // --- Greenfield card ---
  const greenfieldOpacity = (() => {
    if (frame < GREENFIELD_CARD_START) return 0;
    if (frame < GREENFIELD_CARD_FADE_IN_END) {
      return interpolate(
        frame,
        [GREENFIELD_CARD_START, GREENFIELD_CARD_FADE_IN_END],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );
    }
    if (frame < GREENFIELD_CARD_FADE_OUT_START) return 1;
    if (frame < GREENFIELD_CARD_FADE_OUT_END) {
      return interpolate(
        frame,
        [GREENFIELD_CARD_FADE_OUT_START, GREENFIELD_CARD_FADE_OUT_END],
        [1, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );
    }
    return 0;
  })() * sceneFadeOut;

  const greenfieldScale = frame >= GREENFIELD_CARD_START
    ? interpolate(
        frame,
        [GREENFIELD_CARD_START, GREENFIELD_CARD_FADE_IN_END],
        [0.9, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0.9;

  // --- Legacy card ---
  const legacyOpacity = (() => {
    if (frame < LEGACY_CARD_START) return 0;
    if (frame < LEGACY_CARD_FADE_IN_END) {
      return interpolate(
        frame,
        [LEGACY_CARD_START, LEGACY_CARD_FADE_IN_END],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );
    }
    if (frame < LEGACY_CARD_FADE_OUT_START) return 1;
    if (frame < LEGACY_CARD_FADE_OUT_END) {
      return interpolate(
        frame,
        [LEGACY_CARD_FADE_OUT_START, LEGACY_CARD_FADE_OUT_END],
        [1, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );
    }
    return 0;
  })() * sceneFadeOut;

  const legacyScale = frame >= LEGACY_CARD_START
    ? interpolate(
        frame,
        [LEGACY_CARD_START, LEGACY_CARD_FADE_IN_END],
        [0.9, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0.9;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part4_precision.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Spectrum bar, ticks, and labels */}
      <SpectrumBar
        barWidth={barWidth}
        barOpacity={barOpacity}
        labelsOpacity={labelsOpacity}
        ticksOpacity={ticksOpacity}
        balancedColor={balancedColor}
      />

      {/* Animated handle */}
      <SpectrumHandle
        position={handlePosition}
        scale={handleScale}
        glowColor={glowColor}
        glowPulse={glowPulse}
        opacity={handleOpacity}
      />

      {/* Greenfield card */}
      <ContextCard
        title="Greenfield Project"
        traits="Fast iteration · Light prompts · Exploratory tests"
        color={BLUE}
        bgColor={BLUE_BG}
        borderColor={BLUE_BORDER}
        position={LEFT_POS}
        opacity={greenfieldOpacity}
        scale={greenfieldScale}
        iconPath={ROCKET_PATH}
      />

      {/* Legacy card */}
      <ContextCard
        title="Legacy / Contract System"
        traits="Strict prompts · Heavy test walls · Precise contracts"
        color={AMBER}
        bgColor={AMBER_BG}
        borderColor={AMBER_BORDER}
        position={RIGHT_POS}
        opacity={legacyOpacity}
        scale={legacyScale}
        iconPath={SHIELD_PATH}
      />
    </AbsoluteFill>
  );
};

export default Part4Precision07SpectrumSlider;
