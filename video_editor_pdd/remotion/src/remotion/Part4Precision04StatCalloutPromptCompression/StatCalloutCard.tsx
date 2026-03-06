import React from "react";
import {
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  spring,
} from "remotion";
import {
  CARD_X,
  CARD_Y,
  CARD_WIDTH,
  CARD_HEIGHT,
  CARD_BORDER_RADIUS,
  CARD_BG,
  CARD_BORDER,
  CARD_GLOW,
  ACCENT_BAR_WIDTH,
  ACCENT_BAR_COLOR,
  STAT_COLOR,
  DESCRIPTOR_COLOR,
  SOURCE_COLOR,
  QUALIFIER_COLOR,
  STAT_FONT_SIZE,
  DESCRIPTOR_FONT_SIZE,
  SOURCE_FONT_SIZE,
  QUALIFIER_FONT_SIZE,
  STAT_TEXT,
  DESCRIPTOR_TEXT,
  SOURCE_TEXT,
  QUALIFIER_TEXT,
  STAT_START,
  STAT_END,
  DESCRIPTOR_START,
  DESCRIPTOR_END,
  SOURCE_START,
  SOURCE_END,
  QUALIFIER_START,
  QUALIFIER_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
  SLIDE_DISTANCE,
} from "./constants";

export const StatCalloutCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Card slide in from right using spring (damping: 15, stiffness: 180)
  const slideInProgress = spring({
    frame,
    fps,
    config: { damping: 15, stiffness: 180 },
  });

  // Card slide out to right using easeInCubic
  const slideOutProgress = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  // Combined translateX: slide in from right, then slide out to right
  const slideInX = interpolate(slideInProgress, [0, 1], [SLIDE_DISTANCE, 0]);
  const slideOutX = interpolate(slideOutProgress, [0, 1], [0, SLIDE_DISTANCE]);
  const translateX = frame < SLIDE_OUT_START ? slideInX : slideOutX;

  // Opacity: spring-driven fade in, easeInCubic fade out
  const opacityIn = interpolate(slideInProgress, [0, 1], [0, 1]);
  const opacityOut = interpolate(slideOutProgress, [0, 1], [1, 0]);
  const cardOpacity = frame < SLIDE_OUT_START ? opacityIn : opacityOut;

  // Stat "10x" scale (0.8 → 1.0) and opacity (0 → 1), easeOutCubic
  const statScale = interpolate(
    frame,
    [STAT_START, STAT_END],
    [0.8, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );
  const statOpacity = interpolate(
    frame,
    [STAT_START, STAT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Descriptor fade (easeOutQuad)
  const descriptorOpacity = interpolate(
    frame,
    [DESCRIPTOR_START, DESCRIPTOR_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Source fade to 0.7 (easeOutQuad)
  const sourceOpacity = interpolate(
    frame,
    [SOURCE_START, SOURCE_END],
    [0, 0.7],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Qualifier fade (easeOutQuad)
  const qualifierOpacity = interpolate(
    frame,
    [QUALIFIER_START, QUALIFIER_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: CARD_X,
        top: CARD_Y,
        width: CARD_WIDTH,
        height: CARD_HEIGHT,
        transform: `translateX(${translateX}px)`,
        opacity: cardOpacity,
        borderRadius: CARD_BORDER_RADIUS,
        backgroundColor: CARD_BG,
        border: `1px solid ${CARD_BORDER}`,
        boxShadow: CARD_GLOW,
        backdropFilter: "blur(12px)",
        WebkitBackdropFilter: "blur(12px)",
        overflow: "hidden",
        display: "flex",
        flexDirection: "row",
      }}
    >
      {/* Left accent bar (amber) */}
      <div
        style={{
          width: ACCENT_BAR_WIDTH,
          height: "100%",
          backgroundColor: ACCENT_BAR_COLOR,
          flexShrink: 0,
        }}
      />

      {/* Card content */}
      <div
        style={{
          flex: 1,
          padding: "40px 48px",
          display: "flex",
          flexDirection: "column",
          justifyContent: "center",
        }}
      >
        {/* Stat "10x" */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 900,
            fontSize: STAT_FONT_SIZE,
            color: STAT_COLOR,
            lineHeight: 1,
            transform: `scale(${statScale})`,
            transformOrigin: "left center",
            opacity: statOpacity,
            marginBottom: 8,
          }}
        >
          {STAT_TEXT}
        </div>

        {/* Descriptor */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontSize: DESCRIPTOR_FONT_SIZE,
            color: DESCRIPTOR_COLOR,
            lineHeight: 1.3,
            opacity: descriptorOpacity,
            marginBottom: 24,
          }}
        >
          {DESCRIPTOR_TEXT}
        </div>

        {/* Source attribution */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 400,
            fontSize: SOURCE_FONT_SIZE,
            color: SOURCE_COLOR,
            lineHeight: 1.4,
            opacity: sourceOpacity,
            marginBottom: 16,
          }}
        >
          {SOURCE_TEXT}
        </div>

        {/* Qualifier */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 600,
            fontSize: QUALIFIER_FONT_SIZE,
            color: QUALIFIER_COLOR,
            lineHeight: 1.4,
            opacity: qualifierOpacity,
          }}
        >
          {QUALIFIER_TEXT}
        </div>
      </div>
    </div>
  );
};

export default StatCalloutCard;
