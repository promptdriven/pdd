import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  OffthreadVideo,
  staticFile,
} from "remotion";
import { RadialGlow } from "./RadialGlow";
import { HorizontalRule } from "./HorizontalRule";
import {
  QUOTE_TEXT,
  BYLINE_TEXT,
  SCRIM_COLOR_RGB,
  SCRIM_FADE_IN_START,
  SCRIM_FADE_IN_END,
  QUOTE_FADE_IN_START,
  QUOTE_FADE_IN_END,
  BYLINE_FADE_IN_START,
  BYLINE_FADE_IN_END,
  FADE_OUT_START,
  FADE_OUT_END,
  TEXT_CLUSTER_Y,
  BYLINE_Y,
  CANVAS_CENTER_X,
  QUOTE_FONT_SIZE,
  QUOTE_FONT_WEIGHT,
  QUOTE_LETTER_SPACING,
  QUOTE_SHADOW,
  QUOTE_COLOR,
  BYLINE_FONT_SIZE,
  BYLINE_FONT_WEIGHT,
  BYLINE_LETTER_SPACING,
  BYLINE_COLOR,
  BYLINE_MAX_OPACITY,
  QUOTE_SLIDE_DISTANCE,
  BYLINE_SLIDE_DISTANCE,
} from "./constants";

export const defaultPart5Compound10QuoteCardProps = {};

export const Part5Compound10QuoteCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Scrim opacity: fades in 0→0.75, then deepens to 1.0 on exit
  const scrimOpacity = interpolate(
    frame,
    [SCRIM_FADE_IN_START, SCRIM_FADE_IN_END, FADE_OUT_START, FADE_OUT_END],
    [0, 0.75, 0.75, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Quote text fade in + slide up
  const quoteFadeIn = interpolate(
    frame,
    [QUOTE_FADE_IN_START, QUOTE_FADE_IN_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  const quoteFadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  const quoteOpacity = quoteFadeIn * quoteFadeOut;

  const quoteTranslateY = interpolate(
    frame,
    [QUOTE_FADE_IN_START, QUOTE_FADE_IN_END],
    [QUOTE_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  // Byline fade in + slide up
  const bylineFadeIn = interpolate(
    frame,
    [BYLINE_FADE_IN_START, BYLINE_FADE_IN_END],
    [0, BYLINE_MAX_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const bylineFadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  const bylineOpacity = bylineFadeIn * bylineFadeOut;

  const bylineTranslateY = interpolate(
    frame,
    [BYLINE_FADE_IN_START, BYLINE_FADE_IN_END],
    [BYLINE_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Glow opacity follows scrim timing
  const glowOpacity = interpolate(
    frame,
    [SCRIM_FADE_IN_START, SCRIM_FADE_IN_END, FADE_OUT_START, FADE_OUT_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <AbsoluteFill>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part5_compound.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
        />
      </AbsoluteFill>

      {/* Dark scrim backdrop */}
      <AbsoluteFill
        style={{
          backgroundColor: `rgba(${SCRIM_COLOR_RGB}, ${scrimOpacity})`,
        }}
      />

      {/* Radial green glow behind text cluster */}
      <RadialGlow opacity={glowOpacity} />

      {/* Quote text */}
      <div
        style={{
          position: "absolute",
          top: TEXT_CLUSTER_Y,
          left: CANVAS_CENTER_X,
          transform: `translate(-50%, -50%) translateY(${quoteTranslateY}px)`,
          opacity: quoteOpacity,
          fontFamily: "'Inter', sans-serif",
          fontWeight: QUOTE_FONT_WEIGHT,
          fontSize: QUOTE_FONT_SIZE,
          letterSpacing: QUOTE_LETTER_SPACING,
          color: QUOTE_COLOR,
          textShadow: QUOTE_SHADOW,
          textAlign: "center" as const,
          whiteSpace: "nowrap" as const,
        }}
      >
        {QUOTE_TEXT}
      </div>

      {/* Horizontal rule */}
      <HorizontalRule />

      {/* Byline */}
      <div
        style={{
          position: "absolute",
          top: BYLINE_Y,
          left: CANVAS_CENTER_X,
          transform: `translate(-50%, 0) translateY(${bylineTranslateY}px)`,
          opacity: bylineOpacity,
          fontFamily: "'Inter', sans-serif",
          fontWeight: BYLINE_FONT_WEIGHT,
          fontSize: BYLINE_FONT_SIZE,
          fontStyle: "italic" as const,
          letterSpacing: BYLINE_LETTER_SPACING,
          color: BYLINE_COLOR,
          textAlign: "center" as const,
          whiteSpace: "nowrap" as const,
        }}
      >
        {BYLINE_TEXT}
      </div>
    </AbsoluteFill>
  );
};

export default Part5Compound10QuoteCard;
