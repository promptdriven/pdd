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
  BLUE,
  AMBER,
  BALANCED_DIM,
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
  GREENFIELD_CARD_END,
  GREENFIELD_FADE_OUT_START,
  GREENFIELD_FADE_OUT_END,
  LEGACY_CARD_START,
  LEGACY_CARD_END,
  LEGACY_FADE_OUT_START,
  LEGACY_FADE_OUT_END,
  BALANCED_BRIGHTEN_START,
  BALANCED_BRIGHTEN_END,
  FADE_OUT_START,
  FADE_OUT_END,
} from "./constants";

export const defaultPart4Precision07SpectrumSliderProps = {};

/**
 * Compute the handle's normalized position (0-1) along the spectrum bar.
 * Sequence: center → left → right → center
 */
function getHandlePosition(frame: number): number {
  // Phase 1: center (before sliding starts)
  if (frame < HANDLE_SLIDE_LEFT_START) {
    return CENTER_POS;
  }
  // Phase 2: center → left
  if (frame < HANDLE_SLIDE_LEFT_END) {
    return interpolate(
      frame,
      [HANDLE_SLIDE_LEFT_START, HANDLE_SLIDE_LEFT_END],
      [CENTER_POS, LEFT_POS],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.quad),
      }
    );
  }
  // Phase 3: hold at left
  if (frame < HANDLE_SLIDE_RIGHT_START) {
    return LEFT_POS;
  }
  // Phase 4: left → right
  if (frame < HANDLE_SLIDE_RIGHT_END) {
    return interpolate(
      frame,
      [HANDLE_SLIDE_RIGHT_START, HANDLE_SLIDE_RIGHT_END],
      [LEFT_POS, RIGHT_POS],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.quad),
      }
    );
  }
  // Phase 5: hold at right
  if (frame < HANDLE_SLIDE_CENTER_START) {
    return RIGHT_POS;
  }
  // Phase 6: right → center
  if (frame < HANDLE_SLIDE_CENTER_END) {
    return interpolate(
      frame,
      [HANDLE_SLIDE_CENTER_START, HANDLE_SLIDE_CENTER_END],
      [RIGHT_POS, CENTER_POS],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.quad),
      }
    );
  }
  // Phase 7: hold at center
  return CENTER_POS;
}

export const Part4Precision07SpectrumSlider: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // --- Overall fade out ---
  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  // --- Bar expand (from center) ---
  const barExpandProgress =
    interpolate(
      frame,
      [BAR_FADE_START, BAR_FADE_END],
      [0, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.inOut(Easing.cubic),
      }
    );

  const barOpacity =
    interpolate(
      frame,
      [BAR_FADE_START, BAR_FADE_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ) * fadeOut;

  // --- Labels ---
  const labelsOpacity =
    interpolate(
      frame,
      [LABELS_FADE_START, LABELS_FADE_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ) * fadeOut;

  // --- Ticks ---
  const ticksOpacity =
    interpolate(
      frame,
      [TICKS_FADE_START, TICKS_FADE_END],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ) * fadeOut;

  // --- Handle ---
  const handleScale =
    frame >= HANDLE_APPEAR_START
      ? spring({
          frame: frame - HANDLE_APPEAR_START,
          fps,
          config: { damping: 14, stiffness: 200 },
        })
      : 0;

  const handlePosition = getHandlePosition(frame);

  // Glow color: interpolate based on handle position
  const glowColor = interpolateColors(
    handlePosition,
    [0, 0.17, 0.5, 0.83, 1],
    [BLUE, BLUE, BALANCED_DIM, AMBER, AMBER]
  );

  // Glow pulse: subtle breathing effect based on position hold phases
  const glowPulse =
    frame >= HANDLE_APPEAR_START
      ? 1 + 0.15 * Math.sin((frame * Math.PI * 2) / 45)
      : 1;

  const handleOpacity = (frame >= HANDLE_APPEAR_START ? 1 : 0) * fadeOut;

  // --- Greenfield card ---
  const greenfieldCardOpacity =
    interpolate(
      frame,
      [
        GREENFIELD_CARD_START,
        GREENFIELD_CARD_END,
        GREENFIELD_FADE_OUT_START,
        GREENFIELD_FADE_OUT_END,
      ],
      [0, 1, 1, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ) * fadeOut;

  const greenfieldCardScale =
    frame >= GREENFIELD_CARD_START
      ? interpolate(
          spring({
            frame: Math.max(0, frame - GREENFIELD_CARD_START),
            fps,
            config: { damping: 12, stiffness: 180 },
          }),
          [0, 1],
          [0.9, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        )
      : 0.9;

  // --- Legacy card ---
  const legacyCardOpacity =
    interpolate(
      frame,
      [
        LEGACY_CARD_START,
        LEGACY_CARD_END,
        LEGACY_FADE_OUT_START,
        LEGACY_FADE_OUT_END,
      ],
      [0, 1, 1, 0],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    ) * fadeOut;

  const legacyCardScale =
    frame >= LEGACY_CARD_START
      ? interpolate(
          spring({
            frame: Math.max(0, frame - LEGACY_CARD_START),
            fps,
            config: { damping: 12, stiffness: 180 },
          }),
          [0, 1],
          [0.9, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        )
      : 0.9;

  // --- Balanced label brightness ---
  const balancedBrightness = interpolate(
    frame,
    [BALANCED_BRIGHTEN_START, BALANCED_BRIGHTEN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

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

      {/* Semi-transparent overlay for readability */}
      <AbsoluteFill
        style={{ backgroundColor: "rgba(10, 22, 40, 0.55)" }}
      />

      {/* Spectrum bar, labels, ticks */}
      <SpectrumBar
        barExpandProgress={barExpandProgress}
        barOpacity={barOpacity}
        labelsOpacity={labelsOpacity}
        ticksOpacity={ticksOpacity}
        balancedBrightness={balancedBrightness}
      />

      {/* Sliding handle with glow */}
      <SpectrumHandle
        position={handlePosition}
        scale={handleScale * glowPulse}
        glowColor={glowColor}
        opacity={handleOpacity}
      />

      {/* Greenfield card (left) */}
      <ContextCard
        title="Greenfield Project"
        traits="Fast iteration · Light prompts · Exploratory tests"
        color={BLUE}
        position="left"
        opacity={greenfieldCardOpacity}
        scale={greenfieldCardScale}
        icon="rocket"
      />

      {/* Legacy card (right) */}
      <ContextCard
        title="Legacy / Contract System"
        traits="Strict prompts · Heavy test walls · Precise contracts"
        color={AMBER}
        position="right"
        opacity={legacyCardOpacity}
        scale={legacyCardScale}
        icon="shield"
      />
    </AbsoluteFill>
  );
};

export default Part4Precision07SpectrumSlider;
