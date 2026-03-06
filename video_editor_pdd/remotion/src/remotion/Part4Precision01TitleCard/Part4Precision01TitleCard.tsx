import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame } from "remotion";
import { RadialGlow } from "./RadialGlow";
import { HorizontalRule } from "./HorizontalRule";
import {
  BG_COLOR,
  BG_FADE_IN_START,
  BG_FADE_IN_END,
  EYEBROW_FADE_START,
  EYEBROW_FADE_END,
  TITLE_FADE_START,
  TITLE_FADE_END,
  RULE_EXPAND_START,
  RULE_EXPAND_END,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
  EYEBROW_TEXT,
  TITLE_TEXT,
  AMBER,
  EYEBROW_FONT_SIZE,
  EYEBROW_LETTER_SPACING,
  EYEBROW_Y,
  TITLE_FONT_SIZE,
  TITLE_LETTER_SPACING,
  TITLE_Y,
  TEXT_SHADOW,
  RULE_MAX_WIDTH,
} from "./constants";

export const defaultPart4Precision01TitleCardProps = {};

export const Part4Precision01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade in/out
  const bgOpacity = interpolate(
    frame,
    [BG_FADE_IN_START, BG_FADE_IN_END, CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Eyebrow animation — easeOutCubic
  const eyebrowProgress = interpolate(
    frame,
    [EYEBROW_FADE_START, EYEBROW_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const eyebrowFadeOut = interpolate(
    frame,
    [CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );
  const eyebrowOpacity = eyebrowProgress * eyebrowFadeOut;
  const eyebrowTranslateY = interpolate(eyebrowProgress, [0, 1], [20, 0]);

  // Title animation — easeOutQuart
  const titleProgress = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );
  const titleFadeOut = interpolate(
    frame,
    [CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );
  const titleOpacity = titleProgress * titleFadeOut;
  const titleScale = interpolate(titleProgress, [0, 1], [0.9, 1.0]);

  // Horizontal rule — easeInOutCubic
  const ruleProgress = interpolate(
    frame,
    [RULE_EXPAND_START, RULE_EXPAND_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );
  const ruleFadeOut = interpolate(
    frame,
    [CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const ruleWidth = ruleProgress * RULE_MAX_WIDTH;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <AbsoluteFill style={{ opacity: bgOpacity }}>
        {/* Warm amber radial glow */}
        <RadialGlow opacity={1} />

        {/* Eyebrow label */}
        <div
          style={{
            position: "absolute",
            top: EYEBROW_Y,
            width: "100%",
            textAlign: "center",
            opacity: eyebrowOpacity,
            transform: `translateY(${eyebrowTranslateY}px)`,
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontSize: EYEBROW_FONT_SIZE,
            letterSpacing: EYEBROW_LETTER_SPACING,
            textTransform: "uppercase" as const,
            color: AMBER,
            textShadow: TEXT_SHADOW,
          }}
        >
          {EYEBROW_TEXT}
        </div>

        {/* Main title */}
        <div
          style={{
            position: "absolute",
            top: TITLE_Y,
            width: "100%",
            textAlign: "center",
            opacity: titleOpacity,
            transform: `scale(${titleScale})`,
            fontFamily: "Inter, sans-serif",
            fontWeight: 700,
            fontSize: TITLE_FONT_SIZE,
            letterSpacing: TITLE_LETTER_SPACING,
            color: "#FFFFFF",
            textShadow: TEXT_SHADOW,
          }}
        >
          {TITLE_TEXT}
        </div>

        {/* Horizontal rule */}
        <HorizontalRule width={ruleWidth} opacity={ruleFadeOut} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part4Precision01TitleCard;
