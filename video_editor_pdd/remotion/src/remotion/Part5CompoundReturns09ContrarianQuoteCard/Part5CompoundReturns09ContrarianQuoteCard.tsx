import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  useCurrentFrame,
} from "remotion";

import {
  BG_COLOR,
  QUOTE_TEXT_COLOR,
  QUOTE_MARK_COLOR,
  RULE_COLOR,
  ATTRIBUTION_COLOR,
  ACCENT_GLOW_COLOR,
  QUOTE_MARK_OPACITY,
  RULE_OPACITY,
  ATTRIBUTION_OPACITY,
  ACCENT_GLOW_OPACITY,
  QUOTE_MARK_SIZE,
  QUOTE_MARK_WEIGHT,
  QUOTE_FONT_SIZE,
  QUOTE_LINE_HEIGHT,
  ATTRIBUTION_FONT_SIZE,
  QUOTE_MARK_X,
  QUOTE_MARK_Y,
  QUOTE_CENTER_X,
  QUOTE_LINE1_Y,
  QUOTE_LINE2_Y,
  QUOTE_LINE3_Y,
  RULE_Y,
  RULE_HALF_WIDTH,
  ATTRIBUTION_Y,
  GLOW_RADIUS,
  QUOTE_MARK_START,
  QUOTE_MARK_FADE_DUR,
  LINE1_START,
  LINE2_START,
  LINE3_START,
  SPECTACULARLY_GLOW_START,
  SPECTACULARLY_GLOW_DUR,
  RULE_DRAW_START,
  RULE_DRAW_DUR,
  ATTRIBUTION_START,
  ATTRIBUTION_FADE_DUR,
  FADE_OUT_START,
  FADE_OUT_DUR,
  FRAMES_PER_CHAR,
  QUOTE_LINE_1,
  QUOTE_LINE_2,
  QUOTE_LINE_3,
  ATTRIBUTION_TEXT,
} from "./constants";

// ── Helpers ─────────────────────────────────────────────────────────────────

/** Returns the visible substring of `text` based on a typewriter effect. */
function useTypedText(text: string, startFrame: number, frame: number): string {
  if (frame < startFrame) return "";
  const elapsed = frame - startFrame;
  const charsVisible = Math.min(
    text.length,
    Math.floor(elapsed / FRAMES_PER_CHAR)
  );
  return text.slice(0, charsVisible);
}

// ── Default props ───────────────────────────────────────────────────────────

export const defaultPart5CompoundReturns09ContrarianQuoteCardProps = {};

// ── Main component ──────────────────────────────────────────────────────────

export const Part5CompoundReturns09ContrarianQuoteCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Quotation mark fade-in ────────────────────────────────────────────────
  const quoteMarkOpacity = interpolate(
    frame,
    [QUOTE_MARK_START, QUOTE_MARK_START + QUOTE_MARK_FADE_DUR],
    [0, QUOTE_MARK_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Typewriter lines ──────────────────────────────────────────────────────
  const typedLine1 = useTypedText(QUOTE_LINE_1, LINE1_START, frame);
  const typedLine2 = useTypedText(QUOTE_LINE_2, LINE2_START, frame);
  const typedLine3 = useTypedText(QUOTE_LINE_3, LINE3_START, frame);

  // ── Spectacularly glow ────────────────────────────────────────────────────
  const glowOpacity = interpolate(
    frame,
    [SPECTACULARLY_GLOW_START, SPECTACULARLY_GLOW_START + SPECTACULARLY_GLOW_DUR],
    [0, ACCENT_GLOW_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Horizontal rule draw from center ──────────────────────────────────────
  const ruleProgress = interpolate(
    frame,
    [RULE_DRAW_START, RULE_DRAW_START + RULE_DRAW_DUR],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );
  const ruleWidth = RULE_HALF_WIDTH * 2 * ruleProgress; // 0 → 160px

  // ── Attribution fade-in ───────────────────────────────────────────────────
  const attributionOpacity = interpolate(
    frame,
    [ATTRIBUTION_START, ATTRIBUTION_START + ATTRIBUTION_FADE_DUR],
    [0, ATTRIBUTION_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Final fade-out ────────────────────────────────────────────────────────
  const fadeOutOpacity = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DUR],
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
        fontFamily: "Inter, sans-serif",
        opacity: fadeOutOpacity,
      }}
    >
      {/* ── Decorative opening quotation mark ─────────────────────────────── */}
      <div
        style={{
          position: "absolute",
          left: QUOTE_MARK_X,
          top: QUOTE_MARK_Y,
          fontSize: QUOTE_MARK_SIZE,
          fontWeight: QUOTE_MARK_WEIGHT,
          color: QUOTE_MARK_COLOR,
          opacity: quoteMarkOpacity,
          lineHeight: 1,
          userSelect: "none",
        }}
      >
        {"\u201C"}
      </div>

      {/* ── Quote line 1 ──────────────────────────────────────────────────── */}
      <div
        style={{
          position: "absolute",
          top: QUOTE_LINE1_Y,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontSize: QUOTE_FONT_SIZE,
          fontWeight: 400,
          color: QUOTE_TEXT_COLOR,
          lineHeight: `${QUOTE_LINE_HEIGHT}px`,
          whiteSpace: "pre",
        }}
      >
        {typedLine1}
      </div>

      {/* ── Quote line 2 ──────────────────────────────────────────────────── */}
      <div
        style={{
          position: "absolute",
          top: QUOTE_LINE2_Y,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontSize: QUOTE_FONT_SIZE,
          fontWeight: 400,
          color: QUOTE_TEXT_COLOR,
          lineHeight: `${QUOTE_LINE_HEIGHT}px`,
          whiteSpace: "pre",
        }}
      >
        {typedLine2}
      </div>

      {/* ── Quote line 3 — italic with subtle glow ────────────────────────── */}
      <div
        style={{
          position: "absolute",
          top: QUOTE_LINE3_Y,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontSize: QUOTE_FONT_SIZE,
          fontWeight: 400,
          fontStyle: "italic",
          color: QUOTE_TEXT_COLOR,
          lineHeight: `${QUOTE_LINE_HEIGHT}px`,
          whiteSpace: "pre",
        }}
      >
        {typedLine3}
      </div>

      {/* ── Subtle radial glow behind "spectacularly" ─────────────────────── */}
      <div
        style={{
          position: "absolute",
          top: QUOTE_LINE3_Y + QUOTE_FONT_SIZE / 2 - GLOW_RADIUS,
          left: QUOTE_CENTER_X - GLOW_RADIUS,
          width: GLOW_RADIUS * 2,
          height: GLOW_RADIUS * 2,
          borderRadius: "50%",
          background: `radial-gradient(circle, ${ACCENT_GLOW_COLOR} 0%, transparent 70%)`,
          opacity: glowOpacity,
          pointerEvents: "none",
        }}
      />

      {/* ── Horizontal rule (drawn from center outward) ───────────────────── */}
      <div
        style={{
          position: "absolute",
          top: RULE_Y,
          left: QUOTE_CENTER_X - ruleWidth / 2,
          width: ruleWidth,
          height: 2, // minimum 2px thickness per overlay contract
          backgroundColor: RULE_COLOR,
          opacity: RULE_OPACITY,
        }}
      />

      {/* ── Attribution ───────────────────────────────────────────────────── */}
      <div
        style={{
          position: "absolute",
          top: ATTRIBUTION_Y,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontSize: ATTRIBUTION_FONT_SIZE,
          fontWeight: 400,
          color: ATTRIBUTION_COLOR,
          opacity: attributionOpacity,
        }}
      >
        {ATTRIBUTION_TEXT}
      </div>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns09ContrarianQuoteCard;
