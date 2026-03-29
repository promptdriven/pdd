import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import { BackgroundCode } from "./BackgroundCode";
import {
  BG_COLOR,
  TITLE_COLOR,
  RULE_COLOR,
  ACCENT_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  TITLE_Y_TOP,
  TITLE_Y_BOTTOM,
  TITLE_BOTTOM_OFFSET_X,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_FONT_FAMILY,
  RULE_Y,
  RULE_WIDTH,
  RULE_HEIGHT,
  RULE_OPACITY,
  ACCENT_GLOW_WIDTH,
  ACCENT_GLOW_HEIGHT,
  ACCENT_GLOW_Y,
  ACCENT_GLOW_OPACITY,
  OVERLAY_OPACITY,
  CODE_BG_OPACITY,
  OVERLAY_FADE_START,
  OVERLAY_FADE_END,
  TITLE_TOP_START,
  TITLE_TOP_END,
  TITLE_BOTTOM_START,
  TITLE_BOTTOM_END,
  RULE_DRAW_START,
  RULE_DRAW_END,
  ACCENT_PULSE_START,
  ACCENT_PULSE_END,
  SLIDE_DISTANCE,
} from "./constants";

export const defaultColdOpen09TitleCardPddProps = {};

export const ColdOpen09TitleCardPdd: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Overlay fade (frames 0-10): darken background code ---
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

  // Background code opacity: starts full, dims as overlay fades in
  const codeOpacity = interpolate(
    frame,
    [OVERLAY_FADE_START, OVERLAY_FADE_END],
    [0.4, CODE_BG_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // --- "PROMPT-DRIVEN" fade + slide (frames 10-25) ---
  const titleTopOpacity = interpolate(
    frame,
    [TITLE_TOP_START, TITLE_TOP_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );
  const titleTopY = interpolate(
    frame,
    [TITLE_TOP_START, TITLE_TOP_END],
    [TITLE_Y_TOP + SLIDE_DISTANCE, TITLE_Y_TOP],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // --- Horizontal rule draw from center (frames 25-30) ---
  const ruleProgress = interpolate(
    frame,
    [RULE_DRAW_START, RULE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );
  const ruleCurrentWidth = RULE_WIDTH * ruleProgress;

  // --- "DEVELOPMENT" fade + slide (frames 30-45) ---
  const titleBottomOpacity = interpolate(
    frame,
    [TITLE_BOTTOM_START, TITLE_BOTTOM_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );
  const titleBottomY = interpolate(
    frame,
    [TITLE_BOTTOM_START, TITLE_BOTTOM_END],
    [TITLE_Y_BOTTOM + SLIDE_DISTANCE, TITLE_Y_BOTTOM],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // --- Blue accent glow pulse (frames 45-48) ---
  // Single pulse: opacity ramps up then back down within 3 frames
  const accentPulseOpacity =
    frame >= ACCENT_PULSE_START
      ? interpolate(
          frame,
          [ACCENT_PULSE_START, (ACCENT_PULSE_START + ACCENT_PULSE_END) / 2, ACCENT_PULSE_END],
          [0, ACCENT_GLOW_OPACITY, 0],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.sin),
          }
        )
      : 0;

  // After pulse, hold at the low glow level
  const accentHoldOpacity = frame > ACCENT_PULSE_END ? ACCENT_GLOW_OPACITY * 0.6 : 0;
  const finalAccentOpacity = Math.max(accentPulseOpacity, accentHoldOpacity);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* Background: regenerated code at low opacity */}
      <AbsoluteFill style={{ opacity: codeOpacity }}>
        <BackgroundCode />
      </AbsoluteFill>

      {/* Darkening overlay */}
      <AbsoluteFill
        style={{
          backgroundColor: BG_COLOR,
          opacity: overlayOpacity,
        }}
      />

      {/* Title: PROMPT-DRIVEN */}
      <div
        style={{
          position: "absolute",
          top: titleTopY,
          left: 0,
          width: "100%",
          display: "flex",
          justifyContent: "center",
          opacity: titleTopOpacity,
        }}
      >
        <span
          style={{
            fontFamily: TITLE_FONT_FAMILY,
            fontSize: TITLE_FONT_SIZE,
            fontWeight: TITLE_FONT_WEIGHT,
            color: TITLE_COLOR,
            letterSpacing: "0.04em",
          }}
        >
          PROMPT-DRIVEN
        </span>
      </div>

      {/* Horizontal rule — draws from center outward */}
      {ruleProgress > 0 && (
        <div
          style={{
            position: "absolute",
            top: RULE_Y,
            left: CANVAS_WIDTH / 2 - ruleCurrentWidth / 2,
            width: ruleCurrentWidth,
            height: RULE_HEIGHT,
            backgroundColor: RULE_COLOR,
            opacity: RULE_OPACITY,
          }}
        />
      )}

      {/* Blue accent glow beneath rule */}
      {finalAccentOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: ACCENT_GLOW_Y,
            left: CANVAS_WIDTH / 2 - ACCENT_GLOW_WIDTH / 2,
            width: ACCENT_GLOW_WIDTH,
            height: ACCENT_GLOW_HEIGHT,
            backgroundColor: ACCENT_COLOR,
            opacity: finalAccentOpacity,
            boxShadow: `0 0 12px 4px ${ACCENT_COLOR}`,
          }}
        />
      )}

      {/* Title: DEVELOPMENT */}
      <div
        style={{
          position: "absolute",
          top: titleBottomY,
          left: TITLE_BOTTOM_OFFSET_X,
          width: "100%",
          display: "flex",
          justifyContent: "center",
          opacity: titleBottomOpacity,
        }}
      >
        <span
          style={{
            fontFamily: TITLE_FONT_FAMILY,
            fontSize: TITLE_FONT_SIZE,
            fontWeight: TITLE_FONT_WEIGHT,
            color: TITLE_COLOR,
            letterSpacing: "0.04em",
          }}
        >
          DEVELOPMENT
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen09TitleCardPdd;
