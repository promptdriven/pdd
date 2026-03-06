import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, spring, Easing } from "remotion";
import { AccentBar } from "./AccentBar";
import { StatBar } from "./StatBar";
import {
  BG_COLOR,
  CARD_X,
  CARD_Y,
  CARD_WIDTH,
  CARD_HEIGHT,
  CARD_BORDER_RADIUS,
  CARD_BG,
  CARD_BORDER,
  SLIDE_OFFSET,
  CARD_SLIDE_IN_END,
  HEADLINE_FADE_START,
  HEADLINE_FADE_END,
  CHURN_BAR_START,
  CHURN_BAR_END,
  REFACTOR_BAR_START,
  REFACTOR_BAR_END,
  CHURN_GRADIENT,
  REFACTOR_GRADIENT,
  CHURN_FILL,
  REFACTOR_FILL,
  SOURCE_FADE_START,
  SOURCE_FADE_END,
  CARD_SLIDE_OUT_START,
  CARD_SLIDE_OUT_END,
  HEADLINE_FONT_SIZE,
  SOURCE_FONT_SIZE,
  WHITE,
  SOURCE_COLOR,
} from "./constants";

export const defaultPart1Economics07StatCalloutGitclearProps = {};

export const Part1Economics07StatCalloutGitclear: React.FC = () => {
  const frame = useCurrentFrame();

  // Card slide in (spring)
  const slideInProgress = spring({
    frame,
    fps: 30,
    config: { damping: 14, stiffness: 170 },
    durationInFrames: CARD_SLIDE_IN_END,
  });

  // Card slide out (easeInCubic)
  const slideOutProgress = interpolate(
    frame,
    [CARD_SLIDE_OUT_START, CARD_SLIDE_OUT_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  const translateX =
    SLIDE_OFFSET * (1 - slideInProgress) + SLIDE_OFFSET * slideOutProgress;

  const cardOpacity = interpolate(
    frame,
    [0, 10, CARD_SLIDE_OUT_START, CARD_SLIDE_OUT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Headline fade
  const headlineOpacity = interpolate(
    frame,
    [HEADLINE_FADE_START, HEADLINE_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Source fade
  const sourceOpacity = interpolate(
    frame,
    [SOURCE_FADE_START, SOURCE_FADE_END],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Card */}
      <div
        style={{
          position: "absolute",
          left: CARD_X,
          top: CARD_Y,
          width: CARD_WIDTH,
          height: CARD_HEIGHT,
          borderRadius: CARD_BORDER_RADIUS,
          backgroundColor: CARD_BG,
          border: `1px solid ${CARD_BORDER}`,
          backdropFilter: "blur(12px)",
          transform: `translateX(${translateX}px)`,
          opacity: cardOpacity,
          overflow: "hidden",
          display: "flex",
          flexDirection: "column",
          padding: "32px 40px 24px 48px",
        }}
      >
        {/* Left accent bar */}
        <AccentBar />

        {/* Headline */}
        <div
          style={{
            fontFamily: "'Inter', sans-serif",
            fontWeight: 700,
            fontSize: HEADLINE_FONT_SIZE,
            color: WHITE,
            opacity: headlineOpacity,
            marginBottom: 32,
          }}
        >
          211 million lines analyzed
        </div>

        {/* Stat bars container */}
        <div style={{ flex: 1, display: "flex", flexDirection: "column", justifyContent: "center" }}>
          <StatBar
            label="Code Churn"
            maxValue={44}
            prefix="+"
            suffix="%"
            fillTarget={CHURN_FILL}
            gradient={CHURN_GRADIENT}
            direction="up"
            animStart={CHURN_BAR_START}
            animEnd={CHURN_BAR_END}
          />
          <StatBar
            label="Refactoring"
            maxValue={60}
            prefix="-"
            suffix="%"
            fillTarget={REFACTOR_FILL}
            gradient={REFACTOR_GRADIENT}
            direction="down"
            animStart={REFACTOR_BAR_START}
            animEnd={REFACTOR_BAR_END}
          />
        </div>

        {/* Source */}
        <div
          style={{
            fontFamily: "'Inter', sans-serif",
            fontWeight: 400,
            fontSize: SOURCE_FONT_SIZE,
            color: SOURCE_COLOR,
            opacity: sourceOpacity,
            textAlign: "right",
          }}
        >
          GitClear, 2024
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics07StatCalloutGitclear;
