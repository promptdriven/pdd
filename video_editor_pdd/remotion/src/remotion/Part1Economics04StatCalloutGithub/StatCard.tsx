import React from "react";
import { useCurrentFrame, interpolate, Easing, spring } from "remotion";
import { CautionIcon } from "./CautionIcon";
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
  STAT_VALUE,
  STAT_SUFFIX,
  DESCRIPTOR_TEXT,
  SOURCE_TEXT,
  QUALIFIER_TEXT,
  SLIDE_IN_START,
  SLIDE_IN_END,
  COUNTER_START,
  COUNTER_END,
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

export const StatCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Card slide in using spring
  const slideInProgress = spring({
    frame: frame - SLIDE_IN_START,
    fps: 30,
    config: { damping: 15, stiffness: 180 },
  });

  // Card slide out using easeInCubic
  const slideOutProgress = interpolate(
    frame,
    [SLIDE_OUT_START, SLIDE_OUT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.cubic) }
  );

  // Combined translateX: slide in from right, then slide out to right
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

  // Counter animation (0 → 55) with easeOutCubic
  const counterRaw = interpolate(
    frame,
    [COUNTER_START, COUNTER_END],
    [0, STAT_VALUE],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const counterValue = Math.round(counterRaw);

  // Counter scale (0.8 → 1.0)
  const counterScale = interpolate(
    frame,
    [COUNTER_START, COUNTER_END],
    [0.8, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Descriptor opacity
  const descriptorOpacity = interpolate(
    frame,
    [DESCRIPTOR_START, DESCRIPTOR_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Source opacity (fades to 0.7)
  const sourceOpacity = interpolate(
    frame,
    [SOURCE_START, SOURCE_END],
    [0, 0.7],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Qualifier opacity
  const qualifierOpacity = interpolate(
    frame,
    [QUALIFIER_START, QUALIFIER_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Subtle amber pulse for qualifier (cycles gently when visible)
  const qualifierBrightness =
    frame >= QUALIFIER_END
      ? 1 + 0.08 * Math.sin(((frame - QUALIFIER_END) / 30) * Math.PI * 2)
      : 1;

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
      {/* Left accent bar */}
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
        {/* Stat number */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 900,
            fontSize: STAT_FONT_SIZE,
            color: STAT_COLOR,
            lineHeight: 1,
            transform: `scale(${counterScale})`,
            transformOrigin: "left center",
            marginBottom: 8,
          }}
        >
          {counterValue}
          {STAT_SUFFIX}
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

        {/* Qualifier with caution icon */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 600,
            fontSize: QUALIFIER_FONT_SIZE,
            color: QUALIFIER_COLOR,
            lineHeight: 1.4,
            opacity: qualifierOpacity,
            filter: `brightness(${qualifierBrightness})`,
            display: "flex",
            alignItems: "center",
          }}
        >
          <CautionIcon color={QUALIFIER_COLOR} size={16} />
          {QUALIFIER_TEXT}
        </div>
      </div>
    </div>
  );
};

export default StatCard;
