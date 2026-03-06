import React from "react";
import {
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  spring,
} from "remotion";
import { StatBar } from "./StatBar";
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
  ACCENT_GRADIENT_TOP,
  ACCENT_GRADIENT_BOTTOM,
  HEADLINE_COLOR,
  HEADLINE_FONT_SIZE,
  HEADLINE_TEXT,
  SOURCE_COLOR,
  SOURCE_FONT_SIZE,
  SOURCE_TEXT,
  CHURN_LABEL,
  CHURN_VALUE,
  CHURN_PREFIX,
  CHURN_FILL,
  CHURN_GRADIENT_START,
  CHURN_GRADIENT_END,
  CHURN_BAR_START,
  CHURN_BAR_END,
  REFACTOR_LABEL,
  REFACTOR_VALUE,
  REFACTOR_PREFIX,
  REFACTOR_FILL,
  REFACTOR_GRADIENT_START,
  REFACTOR_GRADIENT_END,
  REFACTOR_BAR_START,
  REFACTOR_BAR_END,
  HEADLINE_START,
  HEADLINE_END,
  SOURCE_START,
  SOURCE_END,
  SLIDE_OUT_START,
  SLIDE_OUT_END,
  SLIDE_DISTANCE,
} from "./constants";

export const StatCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Card slide in using spring (damping: 14, stiffness: 170 per spec)
  const slideInProgress = spring({
    frame,
    fps,
    config: { damping: 14, stiffness: 170 },
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

  // Combined translateX
  const slideInX = interpolate(slideInProgress, [0, 1], [SLIDE_DISTANCE, 0]);
  const slideOutX = interpolate(slideOutProgress, [0, 1], [0, SLIDE_DISTANCE]);
  const translateX = frame < SLIDE_OUT_START ? slideInX : slideOutX;

  // Opacity
  const opacityIn = interpolate(slideInProgress, [0, 1], [0, 1]);
  const opacityOut = interpolate(slideOutProgress, [0, 1], [1, 0]);
  const cardOpacity = frame < SLIDE_OUT_START ? opacityIn : opacityOut;

  // Headline fade in
  const headlineOpacity = interpolate(
    frame,
    [HEADLINE_START, HEADLINE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Source fade in (to 0.6 opacity per spec)
  const sourceOpacity = interpolate(
    frame,
    [SOURCE_START, SOURCE_END],
    [0, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
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
      {/* Left accent bar with gradient */}
      <div
        style={{
          width: ACCENT_BAR_WIDTH,
          height: "100%",
          background: `linear-gradient(to bottom, ${ACCENT_GRADIENT_TOP}, ${ACCENT_GRADIENT_BOTTOM})`,
          flexShrink: 0,
        }}
      />

      {/* Card content */}
      <div
        style={{
          flex: 1,
          padding: "36px 44px",
          display: "flex",
          flexDirection: "column",
          justifyContent: "space-between",
        }}
      >
        {/* Headline */}
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 700,
            fontSize: HEADLINE_FONT_SIZE,
            color: HEADLINE_COLOR,
            lineHeight: 1.2,
            opacity: headlineOpacity,
            marginBottom: 28,
          }}
        >
          {HEADLINE_TEXT}
        </div>

        {/* Stat bars */}
        <div>
          <StatBar
            label={CHURN_LABEL}
            targetValue={CHURN_VALUE}
            prefix={CHURN_PREFIX}
            fillTarget={CHURN_FILL}
            gradientStart={CHURN_GRADIENT_START}
            gradientEnd={CHURN_GRADIENT_END}
            arrowDirection="up"
            barStart={CHURN_BAR_START}
            barEnd={CHURN_BAR_END}
            gradientId="churnGrad"
          />
          <StatBar
            label={REFACTOR_LABEL}
            targetValue={REFACTOR_VALUE}
            prefix={REFACTOR_PREFIX}
            fillTarget={REFACTOR_FILL}
            gradientStart={REFACTOR_GRADIENT_START}
            gradientEnd={REFACTOR_GRADIENT_END}
            arrowDirection="down"
            barStart={REFACTOR_BAR_START}
            barEnd={REFACTOR_BAR_END}
            gradientId="refactorGrad"
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
          }}
        >
          {SOURCE_TEXT}
        </div>
      </div>
    </div>
  );
};

export default StatCard;
