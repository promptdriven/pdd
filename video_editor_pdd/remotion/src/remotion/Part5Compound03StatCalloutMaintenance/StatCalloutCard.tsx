import React from "react";
import {
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  spring,
} from "remotion";
import { AccentBar } from "./AccentBar";
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
  WHITE,
  DESCRIPTOR_COLOR,
  SOURCE_COLOR,
  STAT_SIZE,
  DESCRIPTOR_SIZE,
  SOURCE_SIZE,
  STAT_TEXT,
  DESCRIPTOR_TEXT,
  DETAIL_1_TEXT,
  DETAIL_1_COLOR,
  DETAIL_2_TEXT,
  DETAIL_2_COLOR,
  SOURCE_TEXT,
  SLIDE_IN_START,
  SLIDE_IN_END,
  STAT_FADE_START,
  STAT_FADE_END,
  DESCRIPTOR_FADE_START,
  DESCRIPTOR_FADE_END,
  DETAIL_1_START,
  DETAIL_1_END,
  DETAIL_2_START,
  DETAIL_2_END,
  SOURCE_FADE_START,
  SOURCE_FADE_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
  SLIDE_DISTANCE,
  DETAIL_SLIDE_OFFSET,
} from "./constants";

export const StatCalloutCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Card slide in from right using spring
  const slideInProgress = spring({
    frame: frame - SLIDE_IN_START,
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

  // Stat "80–90%" scale (0.8 → 1.0) and opacity
  const statScale = interpolate(
    frame,
    [STAT_FADE_START, STAT_FADE_END],
    [0.8, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );
  const statOpacity = interpolate(
    frame,
    [STAT_FADE_START, STAT_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Descriptor fade in
  const descriptorOpacity = interpolate(
    frame,
    [DESCRIPTOR_FADE_START, DESCRIPTOR_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Detail row 1: "Not features" — slide + fade
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
    [-DETAIL_SLIDE_OFFSET, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Detail row 2: "Not launch" — slide + fade
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
    [-DETAIL_SLIDE_OFFSET, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Source fade in (max 0.7)
  const sourceOpacity = interpolate(
    frame,
    [SOURCE_FADE_START, SOURCE_FADE_END],
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
      <AccentBar />

      {/* Card content */}
      <div
        style={{
          flex: 1,
          padding: "32px 40px",
          display: "flex",
          flexDirection: "column",
          justifyContent: "space-between",
        }}
      >
        {/* Top section */}
        <div>
          {/* Stat "80–90%" */}
          <div
            style={{
              fontFamily: "Inter, sans-serif",
              fontWeight: 900,
              fontSize: STAT_SIZE,
              color: WHITE,
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

          {/* Detail rows */}
          <div style={{ marginTop: 20 }}>
            <DetailRow
              text={DETAIL_1_TEXT}
              color={DETAIL_1_COLOR}
              opacity={detail1Opacity}
              translateX={detail1TranslateX}
            />
            <DetailRow
              text={DETAIL_2_TEXT}
              color={DETAIL_2_COLOR}
              opacity={detail2Opacity}
              translateX={detail2TranslateX}
            />
          </div>
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
          }}
        >
          {SOURCE_TEXT}
        </div>
      </div>
    </div>
  );
};

export default StatCalloutCard;
