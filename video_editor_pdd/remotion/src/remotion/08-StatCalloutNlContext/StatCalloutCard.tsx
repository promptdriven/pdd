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
  GOLD,
  WHITE,
  DESCRIPTOR_COLOR,
  SECONDARY_DESCRIPTOR_COLOR,
  SOURCE_COLOR,
  DIVIDER_COLOR,
  PRIMARY_STAT_SIZE,
  PRIMARY_DESCRIPTOR_SIZE,
  QUALIFIER_SIZE,
  SECONDARY_STAT_SIZE,
  SECONDARY_DESCRIPTOR_SIZE,
  SOURCE_SIZE,
  PRIMARY_STAT_VALUE,
  PRIMARY_STAT_SUFFIX,
  PRIMARY_DESCRIPTOR,
  QUALIFIER_TEXT,
  SECONDARY_STAT_TEXT,
  SECONDARY_DESCRIPTOR,
  SOURCE_TEXT,
  SLIDE_IN_START,
  SLIDE_IN_END,
  STAT_COUNTER_START,
  STAT_COUNTER_END,
  DESCRIPTOR_FADE_START,
  DESCRIPTOR_FADE_END,
  QUALIFIER_FADE_START,
  QUALIFIER_FADE_END,
  DIVIDER_FADE_START,
  DIVIDER_FADE_END,
  SECONDARY_STAT_START,
  SECONDARY_STAT_END,
  SECONDARY_DESC_START,
  SECONDARY_DESC_END,
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

  // Primary stat counter (0 → 41)
  const counterValue = Math.round(
    interpolate(
      frame,
      [STAT_COUNTER_START, STAT_COUNTER_END],
      [0, PRIMARY_STAT_VALUE],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
    )
  );

  // Primary stat scale (0.8 → 1.0)
  const statScale = interpolate(
    frame,
    [STAT_COUNTER_START, STAT_COUNTER_END],
    [0.8, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Primary descriptor fade
  const descriptorOpacity = interpolate(
    frame,
    [DESCRIPTOR_FADE_START, DESCRIPTOR_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Qualifier fade (max 0.9)
  const qualifierOpacity = interpolate(
    frame,
    [QUALIFIER_FADE_START, QUALIFIER_FADE_END],
    [0, 0.9],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Divider fade
  const dividerOpacity = interpolate(
    frame,
    [DIVIDER_FADE_START, DIVIDER_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Secondary stat fade and scale
  const secondaryStatOpacity = interpolate(
    frame,
    [SECONDARY_STAT_START, SECONDARY_STAT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );
  const secondaryStatScale = interpolate(
    frame,
    [SECONDARY_STAT_START, SECONDARY_STAT_END],
    [0.9, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Secondary descriptor + source fade
  const secondaryDescOpacity = interpolate(
    frame,
    [SECONDARY_DESC_START, SECONDARY_DESC_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );
  const sourceOpacity = interpolate(
    frame,
    [SECONDARY_DESC_START, SECONDARY_DESC_END],
    [0, 0.7],
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
      {/* Left accent bar (gold) */}
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
          padding: "28px 40px",
          display: "flex",
          flexDirection: "column",
        }}
      >
        {/* Primary stat "41%" */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 900,
            fontSize: PRIMARY_STAT_SIZE,
            color: WHITE,
            lineHeight: 1,
            transform: `scale(${statScale})`,
            transformOrigin: "left top",
          }}
        >
          {counterValue}{PRIMARY_STAT_SUFFIX}
        </div>

        {/* Primary descriptor */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontSize: PRIMARY_DESCRIPTOR_SIZE,
            color: DESCRIPTOR_COLOR,
            lineHeight: 1.3,
            opacity: descriptorOpacity,
            marginTop: 4,
          }}
        >
          {PRIMARY_DESCRIPTOR}
        </div>

        {/* Qualifier */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontSize: QUALIFIER_SIZE,
            color: GOLD,
            lineHeight: 1.4,
            opacity: qualifierOpacity,
            marginTop: 6,
          }}
        >
          {QUALIFIER_TEXT}
        </div>

        {/* Divider */}
        <div
          style={{
            width: "100%",
            height: 1,
            backgroundColor: DIVIDER_COLOR,
            opacity: dividerOpacity,
            marginTop: 16,
            marginBottom: 16,
            flexShrink: 0,
          }}
        />

        {/* Secondary stat "30x" */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 900,
            fontSize: SECONDARY_STAT_SIZE,
            color: GOLD,
            lineHeight: 1,
            opacity: secondaryStatOpacity,
            transform: `scale(${secondaryStatScale})`,
            transformOrigin: "left center",
          }}
        >
          {SECONDARY_STAT_TEXT}
        </div>

        {/* Secondary descriptor */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 400,
            fontSize: SECONDARY_DESCRIPTOR_SIZE,
            color: SECONDARY_DESCRIPTOR_COLOR,
            lineHeight: 1.4,
            opacity: secondaryDescOpacity,
            marginTop: 6,
          }}
        >
          {SECONDARY_DESCRIPTOR}
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
            marginTop: 8,
          }}
        >
          {SOURCE_TEXT}
        </div>
      </div>
    </div>
  );
};

export default StatCalloutCard;
