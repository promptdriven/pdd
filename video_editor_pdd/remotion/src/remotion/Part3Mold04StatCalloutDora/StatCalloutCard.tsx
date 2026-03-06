import React from "react";
import { useCurrentFrame, interpolate, Easing, spring } from "remotion";
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
  RED,
  GREEN,
  DIVIDER_COLOR,
  SOURCE_COLOR,
  SOURCE_FONT_SIZE,
  TOP_LABEL,
  TOP_RESULT,
  BOTTOM_LABEL,
  BOTTOM_RESULT,
  SOURCE_TEXT,
  SLIDE_IN_START,
  SLIDE_IN_END,
  TOP_FADE_START,
  TOP_FADE_END,
  DIVIDER_FADE_START,
  DIVIDER_FADE_END,
  BOTTOM_FADE_START,
  BOTTOM_FADE_END,
  PULSE_START,
  PULSE_END,
  SOURCE_FADE_START,
  SOURCE_FADE_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
  SLIDE_DISTANCE,
} from "./constants";

export const StatCalloutCard: React.FC = () => {
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

  // Slide in from left (-200 → 0), slide out to left (0 → -200)
  const slideInX = interpolate(slideInProgress, [0, 1], [-SLIDE_DISTANCE, 0]);
  const slideOutX = interpolate(slideOutProgress, [0, 1], [0, -SLIDE_DISTANCE]);
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

  // Top section opacity (frames 20-40)
  const topOpacity = interpolate(
    frame,
    [TOP_FADE_START, TOP_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Divider opacity (frames 35-50, max 0.1 per spec but we use full alpha on the rgba color)
  const dividerOpacity = interpolate(
    frame,
    [DIVIDER_FADE_START, DIVIDER_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Bottom section opacity (frames 45-65)
  const bottomOpacity = interpolate(
    frame,
    [BOTTOM_FADE_START, BOTTOM_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Green result pulse (frames 60-75): scale 1.0 → 1.05 → 1.0, brightness increase
  const pulseProgress = interpolate(
    frame,
    [PULSE_START, PULSE_END],
    [0, Math.PI],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const pulseScale = frame >= PULSE_START && frame <= PULSE_END
    ? 1 + 0.05 * Math.sin(pulseProgress)
    : 1;
  const pulseBrightness = frame >= PULSE_START && frame <= PULSE_END
    ? 1 + 0.2 * Math.sin(pulseProgress)
    : 1;

  // Source opacity (frames 70-85, max 0.7)
  const sourceOpacity = interpolate(
    frame,
    [SOURCE_FADE_START, SOURCE_FADE_END],
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
      {/* Left accent bar (green) */}
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
          position: "relative",
        }}
      >
        {/* Top section: AI without tests */}
        <DualStatSection
          label={TOP_LABEL}
          arrow="down"
          arrowColor={RED}
          result={TOP_RESULT}
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
            flexShrink: 0,
          }}
        />

        {/* Bottom section: AI with tests */}
        <DualStatSection
          label={BOTTOM_LABEL}
          arrow="up"
          arrowColor={GREEN}
          result={BOTTOM_RESULT}
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
