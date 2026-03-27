import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  CANVAS_W,
  LABEL_COLOR,
  LABEL_OPACITY,
  LABEL_FONT_SIZE,
  LABEL_Y,
  TITLE_COLOR,
  TITLE_FONT_SIZE,
  TITLE_LINE2_Y,
  TITLE_LINE2_OFFSET_X,
  RULE_Y,
  RULE_COLOR,
  RULE_OPACITY,
  RULE_WIDTH,
  RULE_THICKNESS,
  BG_FADE_START,
  BG_FADE_END,
  LABEL_FADE_START,
  LABEL_FADE_DURATION,
  TYPEWRITER_START,
  CHARS_PER_FRAME,
  RULE_DRAW_START,
  RULE_DRAW_DURATION,
  LINE2_FADE_START,
  LINE2_FADE_DURATION,
  LINE2_SLIDE_DISTANCE,
  FADEOUT_START,
  FADEOUT_DURATION,
} from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { GhostMold } from "./GhostMold";
import { TypeWriterText } from "./TypeWriterText";

export const defaultPart3MoldParts01SectionTitleCardProps = {};

export const Part3MoldParts01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Background fade-in ──────────────────────────────────────────
  const bgOpacity = interpolate(
    frame,
    [BG_FADE_START, BG_FADE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // ── "PART 3" label fade-in ──────────────────────────────────────
  const labelOpacity = interpolate(
    frame,
    [LABEL_FADE_START, LABEL_FADE_START + LABEL_FADE_DURATION],
    [0, LABEL_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Horizontal rule draw from center ────────────────────────────
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

  // ── "THREE PARTS" fade + slide-up ──────────────────────────────
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

  const line2TranslateY = interpolate(
    frame,
    [LINE2_FADE_START, LINE2_FADE_START + LINE2_FADE_DURATION],
    [LINE2_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // ── Final fade-out ─────────────────────────────────────────────
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
        opacity: bgOpacity,
      }}
    >
      {/* Blueprint grid */}
      <BlueprintGrid />

      {/* Ghost mold cross-section */}
      <GhostMold />

      {/* Overlay container for text elements — fades out at end */}
      <AbsoluteFill style={{ opacity: fadeOut }}>
        {/* Section label: "PART 3" */}
        <div
          style={{
            position: "absolute",
            top: LABEL_Y,
            left: 0,
            width: CANVAS_W,
            display: "flex",
            justifyContent: "center",
            opacity: labelOpacity,
          }}
        >
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: LABEL_FONT_SIZE,
              fontWeight: 600,
              color: LABEL_COLOR,
              letterSpacing: "4px",
              textTransform: "uppercase",
            }}
          >
            PART 3
          </span>
        </div>

        {/* Title line 1: "THE MOLD HAS" — typewriter effect */}
        <TypeWriterText
          text="THE MOLD HAS"
          startFrame={TYPEWRITER_START}
          framesPerChar={CHARS_PER_FRAME}
          y={460}
        />

        {/* Horizontal rule — draws from center outward */}
        {frame >= RULE_DRAW_START && (
          <div
            style={{
              position: "absolute",
              top: RULE_Y,
              left: (CANVAS_W - ruleCurrentWidth) / 2,
              width: ruleCurrentWidth,
              height: RULE_THICKNESS,
              backgroundColor: RULE_COLOR,
              opacity: RULE_OPACITY,
            }}
          />
        )}

        {/* Title line 2: "THREE PARTS" — fade + slide-up */}
        {frame >= LINE2_FADE_START && (
          <div
            style={{
              position: "absolute",
              top: TITLE_LINE2_Y,
              left: 0,
              width: CANVAS_W,
              display: "flex",
              justifyContent: "center",
              opacity: line2Opacity,
              transform: `translateY(${line2TranslateY}px)`,
            }}
          >
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontSize: TITLE_FONT_SIZE,
                fontWeight: 700,
                color: TITLE_COLOR,
                letterSpacing: "2px",
                marginLeft: TITLE_LINE2_OFFSET_X,
              }}
            >
              THREE PARTS
            </span>
          </div>
        )}
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3MoldParts01SectionTitleCard;
