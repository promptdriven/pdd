import React from "react";
import {
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  spring,
} from "remotion";
import { DualStatSection } from "./DualStatSection";
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
  LABEL_COLOR,
  RED,
  GREEN,
  SOURCE_COLOR,
  DIVIDER_COLOR,
  SOURCE_FONT_SIZE,
  WITHOUT_TESTS_LABEL,
  WITHOUT_TESTS_RESULT,
  WITH_TESTS_LABEL,
  WITH_TESTS_RESULT,
  SOURCE_TEXT,
  TOP_SECTION_START,
  TOP_SECTION_END,
  DIVIDER_START,
  DIVIDER_END,
  BOTTOM_SECTION_START,
  BOTTOM_SECTION_END,
  PULSE_START,
  PULSE_END,
  SOURCE_START,
  SOURCE_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
  SLIDE_DISTANCE,
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

  // Combined translateX: slide in from left, then slide out to left
  const slideInX = interpolate(slideInProgress, [0, 1], [-SLIDE_DISTANCE, 0]);
  const slideOutX = interpolate(slideOutProgress, [0, 1], [0, -SLIDE_DISTANCE]);
  const translateX = frame < SLIDE_OUT_START ? slideInX : slideOutX;

  // Opacity: spring-driven fade in, easeInCubic fade out
  const opacityIn = interpolate(slideInProgress, [0, 1], [0, 1]);
  const opacityOut = interpolate(slideOutProgress, [0, 1], [1, 0]);
  const cardOpacity = frame < SLIDE_OUT_START ? opacityIn : opacityOut;

  // Top section opacity (easeOutQuad)
  const topOpacity = interpolate(
    frame,
    [TOP_SECTION_START, TOP_SECTION_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Divider opacity
  const dividerOpacity = interpolate(
    frame,
    [DIVIDER_START, DIVIDER_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Bottom section opacity (easeOutQuad)
  const bottomOpacity = interpolate(
    frame,
    [BOTTOM_SECTION_START, BOTTOM_SECTION_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Green pulse: scale 1.0 → 1.05 → 1.0, brightness increase
  const pulseProgress = interpolate(
    frame,
    [PULSE_START, PULSE_END],
    [0, Math.PI],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.sin),
    }
  );
  const pulseScale =
    frame >= PULSE_START && frame <= PULSE_END
      ? 1 + 0.05 * Math.sin(pulseProgress)
      : 1;
  const pulseBrightness =
    frame >= PULSE_START && frame <= PULSE_END
      ? 1 + 0.2 * Math.sin(pulseProgress)
      : 1;

  // Source opacity (fades to 0.7)
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
          padding: "32px 48px",
          display: "flex",
          flexDirection: "column",
          justifyContent: "center",
        }}
      >
        {/* Top section: AI without tests */}
        <DualStatSection
          label={WITHOUT_TESTS_LABEL}
          arrow="down"
          arrowColor={RED}
          result={WITHOUT_TESTS_RESULT}
          resultColor={RED}
          opacity={topOpacity}
        />

        {/* Horizontal divider */}
        <div
          style={{
            width: "100%",
            height: 1,
            backgroundColor: DIVIDER_COLOR,
            opacity: dividerOpacity,
            marginTop: 24,
            marginBottom: 24,
          }}
        />

        {/* Bottom section: AI with tests */}
        <DualStatSection
          label={WITH_TESTS_LABEL}
          arrow="up"
          arrowColor={GREEN}
          result={WITH_TESTS_RESULT}
          resultColor={GREEN}
          opacity={bottomOpacity}
          scale={pulseScale}
          brightness={pulseBrightness}
        />

        {/* Source attribution */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 400,
            fontSize: SOURCE_FONT_SIZE,
            color: SOURCE_COLOR,
            lineHeight: 1.4,
            opacity: sourceOpacity,
            marginTop: 20,
          }}
        >
          {SOURCE_TEXT}
        </div>
      </div>
    </div>
  );
};

export default StatCard;
