// Part1Economics01SectionTitleCard.tsx — Section 1.1 title card
import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import "../_shared/load-inter-font";
import { BlueprintGrid } from "./BlueprintGrid";
import { GhostCrossingLines } from "./GhostCrossingLines";
import {
  WIDTH,
  HEIGHT,
  BG_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  TITLE_COLOR,
  SECTION_LABEL_COLOR,
  RULE_COLOR,
  GHOST_LINE_A_COLOR,
  GHOST_LINE_B_COLOR,
  GHOST_LINE_OPACITY,
  GHOST_GLOW_COLOR,
  GHOST_GLOW_OPACITY,
  GHOST_GLOW_RADIUS,
  GHOST_STROKE_WIDTH,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  SECTION_LABEL_FONT_SIZE,
  SECTION_LABEL_FONT_WEIGHT,
  SECTION_LABEL_LETTER_SPACING,
  SECTION_LABEL_OPACITY,
  SECTION_LABEL_Y,
  TITLE_LINE1_Y,
  RULE_Y,
  TITLE_LINE2_Y,
  TITLE_LINE2_OFFSET_X,
  RULE_WIDTH,
  RULE_THICKNESS,
  RULE_OPACITY,
  BG_FADE_START,
  BG_FADE_END,
  LABEL_FADE_START,
  LABEL_FADE_END,
  GHOST_DRAW_START,
  GHOST_DRAW_END,
  TITLE1_TYPE_START,
  TITLE1_CHAR_DELAY,
  TITLE1_TEXT,
  RULE_DRAW_START,
  RULE_DRAW_END,
  TITLE2_FADE_START,
  TITLE2_FADE_END,
  TITLE2_SLIDE_DISTANCE,
  TITLE2_TEXT,
  FADEOUT_START,
  FADEOUT_END,
  PULSE_CYCLE_FRAMES,
} from "./constants";

export const defaultPart1Economics01SectionTitleCardProps = {};

export const Part1Economics01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Background fade-in from black (frame 0-15) ---
  const bgOpacity = interpolate(frame, [BG_FADE_START, BG_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // --- Section label "PART 1" fade-in (frame 15-35) ---
  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_END],
    [0, SECTION_LABEL_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // --- Ghost crossing lines draw progress (frame 15-45) ---
  const ghostDrawProgress = interpolate(
    frame,
    [GHOST_DRAW_START, GHOST_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // --- "THE ECONOMICS" typewriter (frame 40+, 2 frames per char) ---
  const title1TotalChars = TITLE1_TEXT.length;
  const title1CharsVisible = Math.min(
    title1TotalChars,
    Math.max(
      0,
      Math.floor((frame - TITLE1_TYPE_START) / TITLE1_CHAR_DELAY) + 1
    )
  );
  const title1Visible = frame >= TITLE1_TYPE_START;
  const title1DisplayText = TITLE1_TEXT.slice(0, title1CharsVisible);

  // --- Horizontal rule draw from center (frame 60-70) ---
  const ruleProgress = interpolate(
    frame,
    [RULE_DRAW_START, RULE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );
  const ruleCurrentWidth = RULE_WIDTH * ruleProgress;

  // --- "OF DARNING" fade-in + slide-up (frame 70-90) ---
  const title2Opacity = interpolate(
    frame,
    [TITLE2_FADE_START, TITLE2_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );
  const title2SlideY = interpolate(
    frame,
    [TITLE2_FADE_START, TITLE2_FADE_END],
    [TITLE2_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // --- Final fade-out (frame 660-720) ---
  const fadeOutOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // Combine overall opacity: fade-in then fade-out
  const contentOpacity = bgOpacity * fadeOutOpacity;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#000000",
        width: WIDTH,
        height: HEIGHT,
      }}
    >
      <AbsoluteFill style={{ opacity: contentOpacity }}>
        {/* Background color fill */}
        <AbsoluteFill style={{ backgroundColor: BG_COLOR }} />

        {/* Blueprint grid */}
        <BlueprintGrid
          spacing={GRID_SPACING}
          color={GRID_COLOR}
          opacity={GRID_OPACITY}
          width={WIDTH}
          height={HEIGHT}
        />

        {/* Ghost crossing lines */}
        {frame >= GHOST_DRAW_START && (
          <GhostCrossingLines
            drawProgress={ghostDrawProgress}
            pulseFrame={frame}
            pulseCycleFrames={PULSE_CYCLE_FRAMES}
            lineAColor={GHOST_LINE_A_COLOR}
            lineBColor={GHOST_LINE_B_COLOR}
            lineOpacity={GHOST_LINE_OPACITY}
            strokeWidth={GHOST_STROKE_WIDTH}
            glowColor={GHOST_GLOW_COLOR}
            glowOpacity={GHOST_GLOW_OPACITY}
            glowRadius={GHOST_GLOW_RADIUS}
            width={WIDTH}
            height={HEIGHT}
          />
        )}

        {/* Section label: "PART 1" */}
        <AbsoluteFill
          style={{
            display: "flex",
            justifyContent: "center",
            alignItems: "flex-start",
          }}
        >
          <div
            style={{
              position: "absolute",
              top: SECTION_LABEL_Y,
              width: "100%",
              textAlign: "center",
              fontFamily: "Inter, sans-serif",
              fontSize: SECTION_LABEL_FONT_SIZE,
              fontWeight: SECTION_LABEL_FONT_WEIGHT,
              color: SECTION_LABEL_COLOR,
              letterSpacing: SECTION_LABEL_LETTER_SPACING,
              opacity: labelOpacity,
            }}
          >
            PART 1
          </div>
        </AbsoluteFill>

        {/* Title line 1: "THE ECONOMICS" — typewriter */}
        {title1Visible && (
          <AbsoluteFill>
            <div
              style={{
                position: "absolute",
                top: TITLE_LINE1_Y,
                width: "100%",
                textAlign: "center",
                fontFamily: "Inter, sans-serif",
                fontSize: TITLE_FONT_SIZE,
                fontWeight: TITLE_FONT_WEIGHT,
                color: TITLE_COLOR,
                lineHeight: 1,
                whiteSpace: "pre",
              }}
            >
              {title1DisplayText}
              {title1CharsVisible < title1TotalChars && (
                <span
                  style={{
                    opacity: frame % 6 < 3 ? 1 : 0,
                    color: TITLE_COLOR,
                  }}
                >
                  |
                </span>
              )}
            </div>
          </AbsoluteFill>
        )}

        {/* Horizontal rule — draws from center */}
        {frame >= RULE_DRAW_START && (
          <AbsoluteFill>
            <div
              style={{
                position: "absolute",
                top: RULE_Y,
                left: "50%",
                transform: "translateX(-50%)",
                width: ruleCurrentWidth,
                height: RULE_THICKNESS,
                backgroundColor: RULE_COLOR,
                opacity: RULE_OPACITY,
              }}
            />
          </AbsoluteFill>
        )}

        {/* Title line 2: "OF DARNING" — fade + slide up */}
        {frame >= TITLE2_FADE_START && (
          <AbsoluteFill>
            <div
              style={{
                position: "absolute",
                top: TITLE_LINE2_Y + title2SlideY,
                width: "100%",
                textAlign: "center",
                fontFamily: "Inter, sans-serif",
                fontSize: TITLE_FONT_SIZE,
                fontWeight: TITLE_FONT_WEIGHT,
                color: TITLE_COLOR,
                opacity: title2Opacity,
                lineHeight: 1,
                paddingLeft: TITLE_LINE2_OFFSET_X,
              }}
            >
              {TITLE2_TEXT}
            </div>
          </AbsoluteFill>
        )}
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics01SectionTitleCard;
