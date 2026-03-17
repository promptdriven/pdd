import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { BlueprintGrid } from "./BlueprintGrid";
import { GhostShapes } from "./GhostShapes";
import { TypewriterText } from "./TypewriterText";
import {
  BG_COLOR,
  BG_FADE_START,
  BG_FADE_END,
  LABEL_FADE_START,
  LABEL_FADE_END,
  LABEL_Y,
  LABEL_TEXT,
  LABEL_COLOR,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_LETTER_SPACING,
  RULE_DRAW_START,
  RULE_DRAW_END,
  RULE_Y,
  RULE_WIDTH,
  RULE_HEIGHT,
  RULE_COLOR,
  SHIFT_FADE_START,
  SHIFT_FADE_END,
  SHIFT_SLIDE_DISTANCE,
  TITLE_LINE2_Y,
  TITLE_LINE2_OFFSET_X,
  TITLE_LINE2_TEXT,
  TITLE_COLOR,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  CANVAS_WIDTH,
} from "./constants";

export const defaultPart2ParadigmShift01SectionTitleCardProps = {};

export const Part2ParadigmShift01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade in from black
  const bgOpacity = interpolate(frame, [BG_FADE_START, BG_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // "PART 2" label fade in
  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_END],
    [0, 0.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Horizontal rule draws from center outward
  const ruleWidth = interpolate(
    frame,
    [RULE_DRAW_START, RULE_DRAW_END],
    [0, RULE_WIDTH],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );

  // "SHIFT" fade in + slide up
  const shiftOpacity = interpolate(
    frame,
    [SHIFT_FADE_START, SHIFT_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const shiftTranslateY = interpolate(
    frame,
    [SHIFT_FADE_START, SHIFT_FADE_END],
    [SHIFT_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#000000" }}>
      <AbsoluteFill style={{ backgroundColor: BG_COLOR, opacity: bgOpacity }}>
        {/* Blueprint grid background */}
        <BlueprintGrid opacity={bgOpacity} />

        {/* Ghost shapes — mold cavity + circuit schematic */}
        <GhostShapes />

        {/* Section label: "PART 2" */}
        <div
          style={{
            position: "absolute",
            top: LABEL_Y,
            left: 0,
            right: 0,
            display: "flex",
            justifyContent: "center",
            opacity: labelOpacity,
            fontFamily: "'Inter', sans-serif",
            fontWeight: LABEL_FONT_WEIGHT,
            fontSize: LABEL_FONT_SIZE,
            color: LABEL_COLOR,
            letterSpacing: LABEL_LETTER_SPACING,
            textTransform: "uppercase" as const,
            textAlign: "center" as const,
          }}
        >
          {LABEL_TEXT}
        </div>

        {/* Title line 1: "THE PARADIGM" — typewriter effect */}
        <TypewriterText />

        {/* Horizontal rule between title lines */}
        <div
          style={{
            position: "absolute",
            top: RULE_Y,
            left: CANVAS_WIDTH / 2 - ruleWidth / 2,
            width: ruleWidth,
            height: RULE_HEIGHT,
            backgroundColor: RULE_COLOR,
            opacity: 0.5,
          }}
        />

        {/* Title line 2: "SHIFT" — fade in + slide up */}
        <div
          style={{
            position: "absolute",
            top: TITLE_LINE2_Y,
            left: TITLE_LINE2_OFFSET_X,
            right: 0,
            display: "flex",
            justifyContent: "center",
            opacity: shiftOpacity,
            transform: `translateY(${shiftTranslateY}px)`,
            fontFamily: "'Inter', sans-serif",
            fontWeight: TITLE_FONT_WEIGHT,
            fontSize: TITLE_FONT_SIZE,
            color: TITLE_COLOR,
            textAlign: "center" as const,
            whiteSpace: "nowrap" as const,
          }}
        >
          {TITLE_LINE2_TEXT}
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift01SectionTitleCard;
