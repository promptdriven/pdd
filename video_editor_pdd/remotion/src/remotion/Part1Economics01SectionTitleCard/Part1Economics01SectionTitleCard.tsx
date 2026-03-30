import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { BlueprintGrid } from "./BlueprintGrid";
import { CrossingLines } from "./CrossingLines";
import {
  WIDTH,
  HEIGHT,
  BG_COLOR,
  SECTION_LABEL,
  SECTION_LABEL_SIZE,
  SECTION_LABEL_WEIGHT,
  SECTION_LABEL_COLOR,
  SECTION_LABEL_OPACITY,
  SECTION_LABEL_LETTER_SPACING,
  SECTION_LABEL_Y,
  TITLE_LINE_1,
  TITLE_LINE_2,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_TEXT_COLOR,
  TITLE_LINE_1_Y,
  TITLE_LINE_2_Y,
  TITLE_LINE_2_OFFSET_X,
  RULE_Y,
  RULE_HALF_WIDTH,
  RULE_THICKNESS,
  RULE_COLOR,
  RULE_OPACITY,
  BG_FADE_START,
  BG_FADE_END,
  LABEL_FADE_START,
  LABEL_FADE_DURATION,
  GHOST_DRAW_START,
  GHOST_DRAW_DURATION,
  TYPEWRITER_START,
  TYPEWRITER_CHAR_DELAY,
  RULE_DRAW_START,
  RULE_DRAW_DURATION,
  LINE2_FADE_START,
  LINE2_FADE_DURATION,
  LINE2_SLIDE_DISTANCE,
  FADEOUT_START,
  FADEOUT_DURATION,
} from "./constants";

// ── Default props (required by export contract) ──
export const defaultPart1Economics01SectionTitleCardProps = {};

// ── Main Component ──
export const Part1Economics01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Global opacity layers ──

  // Background fade-in: 0→15 frames
  const bgOpacity = interpolate(frame, [BG_FADE_START, BG_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Final fade-out: 660→720 frames
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

  // Combined master opacity
  const masterOpacity = bgOpacity * fadeOutOpacity;

  // ── Section label ("PART 1") ──
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

  // ── Ghost crossing lines draw progress ──
  const ghostDraw = interpolate(
    frame,
    [GHOST_DRAW_START, GHOST_DRAW_START + GHOST_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // ── Typewriter: "THE ECONOMICS" ──
  const totalTypewriterFrames = TITLE_LINE_1.length * TYPEWRITER_CHAR_DELAY;
  const typewriterProgress = interpolate(
    frame,
    [TYPEWRITER_START, TYPEWRITER_START + totalTypewriterFrames],
    [0, TITLE_LINE_1.length],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );
  const visibleChars = Math.floor(typewriterProgress);
  const typedText = TITLE_LINE_1.slice(0, visibleChars);
  // Show cursor while typing, hide after
  const showCursor =
    frame >= TYPEWRITER_START &&
    frame < TYPEWRITER_START + totalTypewriterFrames + 10;
  const cursorBlink = Math.floor(frame / 8) % 2 === 0;

  // ── Horizontal rule draw from center ──
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
  const ruleWidth = RULE_HALF_WIDTH * 2 * ruleProgress;

  // ── "OF DARNING" fade + slide up ──
  const line2Opacity = interpolate(
    frame,
    [LINE2_FADE_START, LINE2_FADE_START + LINE2_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );
  const line2SlideY = interpolate(
    frame,
    [LINE2_FADE_START, LINE2_FADE_START + LINE2_FADE_DURATION],
    [LINE2_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
        overflow: "hidden",
      }}
    >
      <AbsoluteFill style={{ opacity: masterOpacity }}>
        {/* Blueprint grid */}
        <BlueprintGrid opacity={bgOpacity} />

        {/* Ghost crossing lines */}
        <CrossingLines drawProgress={ghostDraw} />

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
              fontSize: SECTION_LABEL_SIZE,
              fontWeight: SECTION_LABEL_WEIGHT,
              color: SECTION_LABEL_COLOR,
              letterSpacing: SECTION_LABEL_LETTER_SPACING,
              opacity: labelOpacity,
            }}
          >
            {SECTION_LABEL}
          </div>
        </AbsoluteFill>

        {/* Title line 1: "THE ECONOMICS" — typewriter */}
        <AbsoluteFill>
          <div
            style={{
              position: "absolute",
              top: TITLE_LINE_1_Y,
              width: "100%",
              textAlign: "center",
              fontFamily: "Inter, sans-serif",
              fontSize: TITLE_FONT_SIZE,
              fontWeight: TITLE_FONT_WEIGHT,
              color: TITLE_TEXT_COLOR,
              lineHeight: 1,
              whiteSpace: "pre",
            }}
          >
            {typedText}
            {showCursor && (
              <span style={{ opacity: cursorBlink ? 0.8 : 0 }}>|</span>
            )}
          </div>
        </AbsoluteFill>

        {/* Horizontal rule */}
        {ruleProgress > 0 && (
          <AbsoluteFill>
            <div
              style={{
                position: "absolute",
                top: RULE_Y,
                left: WIDTH / 2 - ruleWidth / 2,
                width: ruleWidth,
                height: RULE_THICKNESS,
                backgroundColor: RULE_COLOR,
                opacity: RULE_OPACITY,
              }}
            />
          </AbsoluteFill>
        )}

        {/* Title line 2: "OF DARNING" — fade + slide up */}
        <AbsoluteFill>
          <div
            style={{
              position: "absolute",
              top: TITLE_LINE_2_Y + line2SlideY,
              width: "100%",
              textAlign: "center",
              fontFamily: "Inter, sans-serif",
              fontSize: TITLE_FONT_SIZE,
              fontWeight: TITLE_FONT_WEIGHT,
              color: TITLE_TEXT_COLOR,
              opacity: line2Opacity,
              lineHeight: 1,
              paddingLeft: TITLE_LINE_2_OFFSET_X,
            }}
          >
            {TITLE_LINE_2}
          </div>
        </AbsoluteFill>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics01SectionTitleCard;
