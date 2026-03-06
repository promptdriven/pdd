import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  Sequence,
  useCurrentFrame,
  interpolate,
  spring,
  useVideoConfig,
  Easing,
} from "remotion";
import { AccentBar } from "./AccentBar";
import { StatBar } from "./StatBar";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  CARD_X,
  CARD_Y,
  CARD_WIDTH,
  CARD_HEIGHT,
  CARD_BORDER_RADIUS,
  CARD_BG,
  ACCENT_BAR_WIDTH,
  SLIDE_DISTANCE,
  CARD_SLIDE_IN_END,
  CARD_SLIDE_OUT_START,
  CARD_SLIDE_OUT_END,
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
  HEADLINE_FONT_SIZE,
  SOURCE_FONT_SIZE,
  WHITE,
  SOURCE_COLOR,
  BORDER_PULSE_SPEED,
  BORDER_PULSE_MIN,
  BORDER_PULSE_MAX,
} from "./constants";

export const defaultPart1Economics07StatCalloutGitclearProps = {};

export const Part1Economics07StatCalloutGitclear: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Card slide in: spring animation
  const slideInProgress = spring({
    frame,
    fps,
    config: { damping: 14, stiffness: 170 },
    durationInFrames: CARD_SLIDE_IN_END,
  });

  // Card slide out: easeInCubic
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

  // Slide from right: in from +200, hold at 0, out to +200
  const translateX =
    frame < CARD_SLIDE_OUT_START
      ? interpolate(slideInProgress, [0, 1], [SLIDE_DISTANCE, 0])
      : interpolate(slideOutProgress, [0, 1], [0, SLIDE_DISTANCE]);

  // Opacity: fade in then fade out
  const opacity =
    frame < CARD_SLIDE_OUT_START
      ? interpolate(slideInProgress, [0, 1], [0, 1])
      : interpolate(slideOutProgress, [0, 1], [1, 0]);

  // Border pulse: sinusoidal red glow
  const borderAlpha = interpolate(
    Math.sin(frame * BORDER_PULSE_SPEED),
    [-1, 1],
    [BORDER_PULSE_MIN, BORDER_PULSE_MAX]
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
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part1_economics.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Stat callout card */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div
          style={{
            position: "absolute",
            left: CARD_X,
            top: CARD_Y,
            width: CARD_WIDTH,
            height: CARD_HEIGHT,
            backgroundColor: CARD_BG,
            backdropFilter: "blur(12px)",
            WebkitBackdropFilter: "blur(12px)",
            borderRadius: CARD_BORDER_RADIUS,
            border: `1px solid rgba(239, 68, 68, ${borderAlpha})`,
            boxShadow: `0 0 20px rgba(239, 68, 68, ${borderAlpha * 0.3}), 0 8px 32px rgba(0, 0, 0, 0.4)`,
            transform: `translateX(${translateX}px)`,
            opacity,
            overflow: "hidden",
          }}
        >
          {/* Red→amber accent bar */}
          <AccentBar />

          {/* Card content */}
          <div
            style={{
              position: "absolute",
              left: ACCENT_BAR_WIDTH + 40,
              top: 32,
              right: 40,
              bottom: 24,
              display: "flex",
              flexDirection: "column",
            }}
          >
            {/* Headline */}
            <div
              style={{
                fontFamily: "'Inter', sans-serif",
                fontWeight: 700,
                fontSize: HEADLINE_FONT_SIZE,
                color: WHITE,
                opacity: headlineOpacity,
                marginBottom: 28,
              }}
            >
              211 million lines analyzed
            </div>

            {/* Stat bars */}
            <div
              style={{
                flex: 1,
                display: "flex",
                flexDirection: "column",
                justifyContent: "center",
              }}
            >
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

            {/* Source attribution */}
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
        </div>
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics07StatCalloutGitclear;
