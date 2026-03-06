import React from "react";
import { useCurrentFrame, interpolate, Easing, spring } from "remotion";
import { ErrorIcon } from "./ErrorIcon";
import { WarningIcon } from "./WarningIcon";
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
  DETAIL_RED,
  DETAIL_AMBER,
  STAT_FONT_SIZE,
  DESCRIPTOR_FONT_SIZE,
  DETAIL_FONT_SIZE,
  SOURCE_FONT_SIZE,
  ICON_SIZE,
  STAT_TEXT,
  DESCRIPTOR_TEXT,
  DETAIL_1_TEXT,
  DETAIL_2_TEXT,
  SOURCE_TEXT,
  SLIDE_IN_START,
  SLIDE_IN_END,
  STAT_START,
  STAT_END,
  DESCRIPTOR_START,
  DESCRIPTOR_END,
  DETAIL_1_START,
  DETAIL_1_END,
  DETAIL_2_START,
  DETAIL_2_END,
  SOURCE_START,
  SOURCE_END,
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

  // Stat "1.7x" scale (0.8 → 1.0) and opacity
  const statScale = interpolate(
    frame,
    [STAT_START, STAT_END],
    [0.8, 1.0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const statOpacity = interpolate(
    frame,
    [STAT_START, STAT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Descriptor opacity
  const descriptorOpacity = interpolate(
    frame,
    [DESCRIPTOR_START, DESCRIPTOR_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Detail row 1: "75% logic errors" — slide in from left + fade
  const detail1Opacity = interpolate(
    frame,
    [DETAIL_1_START, DETAIL_1_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );
  const detail1TranslateX = interpolate(
    frame,
    [DETAIL_1_START, DETAIL_1_END],
    [-20, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Detail row 2: "8x perf problems" — slide in from left + fade
  const detail2Opacity = interpolate(
    frame,
    [DETAIL_2_START, DETAIL_2_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );
  const detail2TranslateX = interpolate(
    frame,
    [DETAIL_2_START, DETAIL_2_END],
    [-20, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Source attribution opacity (fades to 0.7)
  const sourceOpacity = interpolate(
    frame,
    [SOURCE_START, SOURCE_END],
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
      {/* Left accent bar (red) */}
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
          padding: "36px 48px",
          display: "flex",
          flexDirection: "column",
          justifyContent: "center",
        }}
      >
        {/* Stat number: "1.7x" */}
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
            marginBottom: 28,
          }}
        >
          {DESCRIPTOR_TEXT}
        </div>

        {/* Detail row 1: "75% logic errors" */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 600,
            fontSize: DETAIL_FONT_SIZE,
            color: DETAIL_RED,
            lineHeight: 1.4,
            opacity: detail1Opacity,
            transform: `translateX(${detail1TranslateX}px)`,
            display: "flex",
            alignItems: "center",
            marginBottom: 12,
          }}
        >
          <ErrorIcon color={DETAIL_RED} size={ICON_SIZE} />
          {DETAIL_1_TEXT}
        </div>

        {/* Detail row 2: "8x perf problems" */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 600,
            fontSize: DETAIL_FONT_SIZE,
            color: DETAIL_AMBER,
            lineHeight: 1.4,
            opacity: detail2Opacity,
            transform: `translateX(${detail2TranslateX}px)`,
            display: "flex",
            alignItems: "center",
            marginBottom: 20,
          }}
        >
          <WarningIcon color={DETAIL_AMBER} size={ICON_SIZE} />
          {DETAIL_2_TEXT}
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
          }}
        >
          {SOURCE_TEXT}
        </div>
      </div>
    </div>
  );
};

export default StatCard;
