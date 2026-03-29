import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import "../_shared/load-inter-font";
import { BlueprintGrid } from "./BlueprintGrid";
import { GhostCurve } from "./GhostCurve";
import {
  WIDTH,
  HEIGHT,
  BG_COLOR,
  FONT_FAMILY,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_COLOR,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_LETTER_SPACING,
  SECTION_LABEL_COLOR,
  SECTION_LABEL_OPACITY,
  RULE_COLOR,
  RULE_OPACITY,
  RULE_WIDTH,
  RULE_THICKNESS,
  LABEL_Y,
  TITLE_LINE1_Y,
  RULE_Y,
  TITLE_LINE2_Y,
  TITLE_LINE2_OFFSET_X,
  BG_FADE_START,
  BG_FADE_END,
  LABEL_FADE_START,
  LABEL_FADE_DURATION,
  TYPEWRITER_START,
  TYPEWRITER_CHAR_DELAY,
  RULE_DRAW_START,
  RULE_DRAW_DURATION,
  LINE2_FADE_START,
  LINE2_FADE_DURATION,
  LINE2_SLIDE_DISTANCE,
  FADEOUT_START,
  FADEOUT_DURATION,
  DURATION_FRAMES,
  SECTION_LABEL_TEXT,
  TITLE_LINE1_TEXT,
  TITLE_LINE2_TEXT,
} from "./constants";

// ── Default props (required by export contract) ─────────────────────────────
export const defaultPart4PrecisionTradeoff01SectionTitleCardProps = {};

// ── Main Component ──────────────────────────────────────────────────────────
export const Part4PrecisionTradeoff01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Black overlay that fades out to reveal BG_COLOR ─────────────────
  const blackOverlayOpacity = interpolate(
    frame,
    [BG_FADE_START, BG_FADE_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── "PART 4" label fade-in ────────────────────────────────────────────
  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_START + LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── "THE PRECISION" typewriter ────────────────────────────────────────
  const typewriterElapsed = Math.max(0, frame - TYPEWRITER_START);
  const visibleChars = Math.min(
    TITLE_LINE1_TEXT.length,
    Math.floor(typewriterElapsed / TYPEWRITER_CHAR_DELAY)
  );
  const line1Text = TITLE_LINE1_TEXT.slice(0, visibleChars);

  // ── Horizontal rule draw from center ──────────────────────────────────
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

  // ── "TRADEOFF" fade-in with slide-up ──────────────────────────────────
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

  // ── Final fade-out ────────────────────────────────────────────────────
  const fadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
      }}
    >
      {/* Black overlay that fades out to reveal background */}
      <AbsoluteFill
        style={{
          backgroundColor: "#000000",
          opacity: blackOverlayOpacity,
          zIndex: 1,
        }}
      />

      {/* All content fades out together at the end */}
      <AbsoluteFill style={{ opacity: fadeOut }}>
        {/* Blueprint grid */}
        <BlueprintGrid opacity={1} />

        {/* Ghost inverse curve */}
        <Sequence from={0} durationInFrames={DURATION_FRAMES}>
          <GhostCurve />
        </Sequence>

        {/* Section label: PART 4 */}
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
              top: LABEL_Y,
              width: "100%",
              textAlign: "center",
              fontFamily: FONT_FAMILY,
              fontSize: LABEL_FONT_SIZE,
              fontWeight: LABEL_FONT_WEIGHT,
              color: SECTION_LABEL_COLOR,
              opacity: labelOpacity * SECTION_LABEL_OPACITY,
              letterSpacing: LABEL_LETTER_SPACING,
            }}
          >
            {SECTION_LABEL_TEXT}
          </div>
        </AbsoluteFill>

        {/* Title line 1: THE PRECISION (typewriter) */}
        <AbsoluteFill>
          <div
            style={{
              position: "absolute",
              top: TITLE_LINE1_Y,
              width: "100%",
              textAlign: "center",
              fontFamily: FONT_FAMILY,
              fontSize: TITLE_FONT_SIZE,
              fontWeight: TITLE_FONT_WEIGHT,
              color: TITLE_COLOR,
              lineHeight: 1,
              whiteSpace: "pre",
            }}
          >
            {line1Text}
            {/* Blinking cursor during typewriting */}
            {visibleChars < TITLE_LINE1_TEXT.length && visibleChars > 0 && (
              <span
                style={{
                  opacity: frame % 10 < 5 ? 0.8 : 0,
                  color: TITLE_COLOR,
                }}
              >
                |
              </span>
            )}
          </div>
        </AbsoluteFill>

        {/* Horizontal rule (draws from center outward) */}
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
              borderRadius: 1,
            }}
          />
        </AbsoluteFill>

        {/* Title line 2: TRADEOFF (fade-in + slide-up) */}
        <AbsoluteFill>
          <div
            style={{
              position: "absolute",
              top: TITLE_LINE2_Y + line2SlideY,
              width: "100%",
              textAlign: "center",
              fontFamily: FONT_FAMILY,
              fontSize: TITLE_FONT_SIZE,
              fontWeight: TITLE_FONT_WEIGHT,
              color: TITLE_COLOR,
              opacity: line2Opacity,
              lineHeight: 1,
              paddingLeft: TITLE_LINE2_OFFSET_X,
            }}
          >
            {TITLE_LINE2_TEXT}
          </div>
        </AbsoluteFill>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff01SectionTitleCard;
