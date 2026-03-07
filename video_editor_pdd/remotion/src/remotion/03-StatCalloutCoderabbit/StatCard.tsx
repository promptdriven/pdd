import React from "react";
import {
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  spring,
} from "remotion";
import { DetailRow } from "./DetailRow";
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
  RED,
  AMBER,
  SOURCE_COLOR,
  STAT_FONT_SIZE,
  DESCRIPTOR_FONT_SIZE,
  SOURCE_FONT_SIZE,
  STAT_TEXT,
  DESCRIPTOR_TEXT,
  DETAIL_1_TEXT,
  DETAIL_2_TEXT,
  SOURCE_TEXT,
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
  DETAIL_SLIDE_DISTANCE,
} from "./constants";

export const StatCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Card slide in using spring (damping: 15, stiffness: 180)
  const slideInProgress = spring({
    frame,
    fps,
    config: { damping: 15, stiffness: 180 },
  });

  // Card slide out using easeInCubic
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

  // Combined translateX: slide in from right, slide out to right
  const slideInX = interpolate(slideInProgress, [0, 1], [SLIDE_DISTANCE, 0]);
  const slideOutX = interpolate(slideOutProgress, [0, 1], [0, SLIDE_DISTANCE]);
  const translateX = frame < SLIDE_OUT_START ? slideInX : slideOutX;

  // Opacity: spring-driven fade in, easeInCubic fade out
  const opacityIn = interpolate(slideInProgress, [0, 1], [0, 1]);
  const opacityOut = interpolate(slideOutProgress, [0, 1], [1, 0]);
  const cardOpacity = frame < SLIDE_OUT_START ? opacityIn : opacityOut;

  // Stat "1.7x" scale and opacity (easeOutCubic)
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

  // Descriptor text fade in (easeOutQuad)
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

  // Detail row 1: "75% logic errors" (easeOutQuad)
  const detail1Opacity = interpolate(
    frame,
    [DETAIL_1_START, DETAIL_1_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );
  const detail1TranslateX = interpolate(
    frame,
    [DETAIL_1_START, DETAIL_1_END],
    [-DETAIL_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Detail row 2: "8x perf problems" (easeOutQuad)
  const detail2Opacity = interpolate(
    frame,
    [DETAIL_2_START, DETAIL_2_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );
  const detail2TranslateX = interpolate(
    frame,
    [DETAIL_2_START, DETAIL_2_END],
    [-DETAIL_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Source opacity (fades to 0.7, easeOutQuad)
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
        {/* Main stat: "1.7x" */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 900,
            fontSize: STAT_FONT_SIZE,
            color: STAT_COLOR,
            lineHeight: 1.0,
            opacity: statOpacity,
            transform: `scale(${statScale})`,
            transformOrigin: "left center",
          }}
        >
          {STAT_TEXT}
        </div>

        {/* Descriptor: "more issues in AI-generated code" */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 500,
            fontSize: DESCRIPTOR_FONT_SIZE,
            color: DESCRIPTOR_COLOR,
            lineHeight: 1.4,
            opacity: descriptorOpacity,
            marginTop: 8,
          }}
        >
          {DESCRIPTOR_TEXT}
        </div>

        {/* Detail rows */}
        <div
          style={{
            display: "flex",
            flexDirection: "column",
            gap: 14,
            marginTop: 28,
          }}
        >
          <DetailRow
            icon="error"
            text={DETAIL_1_TEXT}
            color={RED}
            opacity={detail1Opacity}
            translateX={detail1TranslateX}
          />
          <DetailRow
            icon="warning"
            text={DETAIL_2_TEXT}
            color={AMBER}
            opacity={detail2Opacity}
            translateX={detail2TranslateX}
          />
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
            marginTop: 24,
          }}
        >
          {SOURCE_TEXT}
        </div>
      </div>
    </div>
  );
};

export default StatCard;
