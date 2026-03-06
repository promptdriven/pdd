import React from "react";
import { useCurrentFrame, interpolate, Easing, spring } from "remotion";
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
  AMBER,
  DESCRIPTOR_COLOR,
  SOURCE_COLOR,
  QUALIFIER_COLOR,
  STAT_SIZE,
  DESCRIPTOR_SIZE,
  SOURCE_SIZE,
  QUALIFIER_SIZE,
  STAT_TEXT,
  DESCRIPTOR_TEXT,
  SOURCE_TEXT,
  QUALIFIER_TEXT,
  SLIDE_IN_START,
  SLIDE_IN_END,
  STAT_FADE_START,
  STAT_FADE_END,
  DESCRIPTOR_FADE_START,
  DESCRIPTOR_FADE_END,
  SOURCE_FADE_START,
  SOURCE_FADE_END,
  QUALIFIER_FADE_START,
  QUALIFIER_FADE_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
  SLIDE_DISTANCE,
} from "./constants";

export const StatCalloutCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Card slide in from right using spring
  const slideInProgress = spring({
    frame: frame - SLIDE_IN_START,
    fps: 30,
    config: { damping: 15, stiffness: 180 },
  });

  // Card slide out to right using easeInCubic
  const slideOutProgress = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );

  // Slide in from right (+200 → 0), slide out to right (0 → +200)
  const slideInX = interpolate(slideInProgress, [0, 1], [SLIDE_DISTANCE, 0]);
  const slideOutX = interpolate(slideOutProgress, [0, 1], [0, SLIDE_DISTANCE]);
  const translateX = frame < SLIDE_OUT_START ? slideInX : slideOutX;

  // Opacity: fade in with slide, fade out with slide
  const opacityIn = interpolate(
    frame,
    [SLIDE_IN_START, SLIDE_IN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const opacityOut = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const cardOpacity = Math.min(opacityIn, opacityOut);

  // Stat "10x" scale (0.8 → 1.0) and opacity (0 → 1)
  const statScale = interpolate(
    frame,
    [STAT_FADE_START, STAT_FADE_END],
    [0.8, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const statOpacity = interpolate(
    frame,
    [STAT_FADE_START, STAT_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Descriptor fade
  const descriptorOpacity = interpolate(
    frame,
    [DESCRIPTOR_FADE_START, DESCRIPTOR_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Source fade (max 0.7)
  const sourceOpacity = interpolate(
    frame,
    [SOURCE_FADE_START, SOURCE_FADE_END],
    [0, 0.7],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Qualifier fade
  const qualifierOpacity = interpolate(
    frame,
    [QUALIFIER_FADE_START, QUALIFIER_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
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
          padding: "32px 40px",
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
            fontSize: STAT_SIZE,
            color: AMBER,
            lineHeight: 1,
            transform: `scale(${statScale})`,
            transformOrigin: "left top",
            opacity: statOpacity,
          }}
        >
          {STAT_TEXT}
        </div>

        {/* Descriptor */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontSize: DESCRIPTOR_SIZE,
            color: DESCRIPTOR_COLOR,
            lineHeight: 1.3,
            opacity: descriptorOpacity,
            marginTop: 8,
          }}
        >
          {DESCRIPTOR_TEXT}
        </div>

        {/* Qualifier */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 600,
            fontSize: QUALIFIER_SIZE,
            color: QUALIFIER_COLOR,
            lineHeight: 1.4,
            opacity: qualifierOpacity,
            marginTop: 12,
          }}
        >
          {QUALIFIER_TEXT}
        </div>

        {/* Source attribution */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 400,
            fontSize: SOURCE_SIZE,
            color: SOURCE_COLOR,
            lineHeight: 1.4,
            opacity: sourceOpacity,
            marginTop: "auto",
            paddingTop: 16,
          }}
        >
          {SOURCE_TEXT}
        </div>
      </div>
    </div>
  );
};

export default StatCalloutCard;
