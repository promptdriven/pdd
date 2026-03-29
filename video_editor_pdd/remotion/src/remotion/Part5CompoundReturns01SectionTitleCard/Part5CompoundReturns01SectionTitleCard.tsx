import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

import { BlueprintGrid } from "./BlueprintGrid";
import { DivergingCurves } from "./DivergingCurves";
import { TypewriterText } from "./TypewriterText";
import {
  BG_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  TOTAL_FRAMES,
  TITLE_COLOR,
  SECTION_LABEL_COLOR,
  SECTION_LABEL_OPACITY,
  SECTION_LABEL_FONT_SIZE,
  SECTION_LABEL_FONT_WEIGHT,
  SECTION_LABEL_LETTER_SPACING,
  SECTION_LABEL_Y,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_LINE1_Y,
  TITLE_LINE2_Y,
  TITLE_LINE2_OFFSET_X,
  RULE_Y,
  RULE_WIDTH,
  RULE_THICKNESS,
  RULE_COLOR,
  RULE_OPACITY,
  BG_FADE_START,
  BG_FADE_END,
  LABEL_FADE_START,
  LABEL_FADE_DURATION,
  CURVES_DRAW_START,
  COMPOUND_TYPE_START,
  COMPOUND_CHAR_DELAY,
  RULE_DRAW_START,
  RULE_DRAW_DURATION,
  RETURNS_FADE_START,
  RETURNS_FADE_DURATION,
  RETURNS_SLIDE_DISTANCE,
  FADEOUT_START,
  FADEOUT_DURATION,
} from "./constants";

export const defaultPart5CompoundReturns01SectionTitleCardProps = {};

export const Part5CompoundReturns01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Background fade from black ──
  const bgOpacity = interpolate(frame, [BG_FADE_START, BG_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // ── "PART 5" label fade ──
  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_START + LABEL_FADE_DURATION],
    [0, SECTION_LABEL_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Horizontal rule draw from center outward ──
  const ruleProgress = interpolate(
    frame,
    [RULE_DRAW_START, RULE_DRAW_START + RULE_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );
  const ruleCurrentWidth = RULE_WIDTH * ruleProgress;

  // ── "RETURNS" fade-in + slide-up ──
  const returnsOpacity = interpolate(
    frame,
    [RETURNS_FADE_START, RETURNS_FADE_START + RETURNS_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );
  const returnsSlideY = interpolate(
    frame,
    [RETURNS_FADE_START, RETURNS_FADE_START + RETURNS_FADE_DURATION],
    [RETURNS_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.bezier(0.33, 1, 0.68, 1)), // easeOut(cubic)
    }
  );

  // ── Final fade-out ──
  const fadeOutOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // Master opacity combines bg fade-in and final fade-out
  const masterOpacity = bgOpacity * fadeOutOpacity;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        opacity: masterOpacity,
      }}
    >
      {/* Blueprint grid */}
      <BlueprintGrid />

      {/* Ghost diverging curves */}
      <Sequence from={CURVES_DRAW_START} durationInFrames={TOTAL_FRAMES - CURVES_DRAW_START}>
        <DivergingCurves globalFrame={frame} />
      </Sequence>

      {/* Section label: PART 5 */}
      <div
        style={{
          position: "absolute",
          top: SECTION_LABEL_Y,
          left: 0,
          width: "100%",
          display: "flex",
          justifyContent: "center",
          opacity: labelOpacity,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: SECTION_LABEL_FONT_SIZE,
            fontWeight: SECTION_LABEL_FONT_WEIGHT,
            color: SECTION_LABEL_COLOR,
            letterSpacing: SECTION_LABEL_LETTER_SPACING,
            lineHeight: 1,
          }}
        >
          PART 5
        </span>
      </div>

      {/* Title: COMPOUND (typewriter) */}
      <Sequence from={COMPOUND_TYPE_START} durationInFrames={TOTAL_FRAMES - COMPOUND_TYPE_START}>
        <TypewriterText
          text="COMPOUND"
          charDelay={COMPOUND_CHAR_DELAY}
          fontSize={TITLE_FONT_SIZE}
          fontWeight={TITLE_FONT_WEIGHT}
          color={TITLE_COLOR}
          y={TITLE_LINE1_Y}
        />
      </Sequence>

      {/* Horizontal rule */}
      {frame >= RULE_DRAW_START && (
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
      )}

      {/* Title: RETURNS (fade-in + slide-up) */}
      {frame >= RETURNS_FADE_START && (
        <div
          style={{
            position: "absolute",
            top: TITLE_LINE2_Y + returnsSlideY,
            left: 0,
            width: "100%",
            display: "flex",
            justifyContent: "center",
            opacity: returnsOpacity,
          }}
        >
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: TITLE_FONT_SIZE,
              fontWeight: TITLE_FONT_WEIGHT,
              color: TITLE_COLOR,
              letterSpacing: 2,
              lineHeight: 1,
              transform: `translateX(${TITLE_LINE2_OFFSET_X}px)`,
            }}
          >
            RETURNS
          </span>
        </div>
      )}
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns01SectionTitleCard;
