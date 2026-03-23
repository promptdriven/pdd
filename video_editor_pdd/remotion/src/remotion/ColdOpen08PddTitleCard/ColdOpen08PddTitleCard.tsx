import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  useCurrentFrame,
} from "remotion";
import {
  BG_COLOR,
  OVERLAY_BG,
  PDD_BLUE,
  PDD_BLUE_GLOW,
  CODE_DIM_START,
  CODE_DIM_END,
  CODE_UNDERLAY_OPACITY,
  TITLE_FADE_START,
  TITLE_FADE_END,
  TITLE_OPACITY,
  TITLE_SLIDE_DISTANCE,
  TITLE_FONT_SIZE,
  TITLE_LETTER_SPACING,
  TITLE_Y,
  GLOW_BLOOM_START,
  GLOW_BLOOM_END,
  RULE_DRAW_START,
  RULE_DRAW_END,
  RULE_Y,
  RULE_WIDTH,
  RULE_HEIGHT,
  RULE_OPACITY,
  TERMINAL_FADE_START,
  TERMINAL_FADE_END,
  TERMINAL_OPACITY_FROM,
  TERMINAL_OPACITY_TO,
} from "./constants";
import { CodeUnderlay } from "./CodeUnderlay";
import { TerminalOverlay } from "./TerminalOverlay";

export const defaultColdOpen08PddTitleCardProps = {};

export const ColdOpen08PddTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Phase 1: Dark overlay fades in to dim code (frames 0–10) ──
  const overlayOpacity = interpolate(
    frame,
    [CODE_DIM_START, CODE_DIM_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Phase 2: Title fade-in + slide up (frames 10–30) ──
  const titleOpacity = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [0, TITLE_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const titleTranslateY = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [TITLE_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // ── Phase 2b: Blue glow bloom (frames 10–35) ──
  const glowIntensity = interpolate(
    frame,
    [GLOW_BLOOM_START, GLOW_BLOOM_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );
  const glowBlur = 40 * glowIntensity;
  const glowAlpha = 0.15 * glowIntensity;

  // ── Phase 3: Horizontal rule draws from center (frames 35–45) ──
  const ruleProgress = interpolate(
    frame,
    [RULE_DRAW_START, RULE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );
  const ruleCurrentWidth = RULE_WIDTH * ruleProgress;

  // ── Terminal opacity reduction (frames 0–15) ──
  const terminalOpacity = interpolate(
    frame,
    [TERMINAL_FADE_START, TERMINAL_FADE_END],
    [TERMINAL_OPACITY_FROM, TERMINAL_OPACITY_TO],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Code underlay — always visible at low opacity */}
      <CodeUnderlay opacity={CODE_UNDERLAY_OPACITY} />

      {/* Dark overlay — fades in to dim code further */}
      <AbsoluteFill
        style={{
          backgroundColor: OVERLAY_BG,
          opacity: overlayOpacity,
        }}
      />

      {/* Title: "Prompt-Driven Development" */}
      <AbsoluteFill
        style={{
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "flex-start",
        }}
      >
        <div
          style={{
            position: "absolute",
            top: TITLE_Y - TITLE_FONT_SIZE / 2,
            width: "100%",
            textAlign: "center",
            opacity: titleOpacity,
            transform: `translateY(${titleTranslateY}px)`,
          }}
        >
          <span
            style={{
              fontFamily: "'Inter', 'Helvetica Neue', sans-serif",
              fontSize: TITLE_FONT_SIZE,
              fontWeight: 700,
              color: PDD_BLUE,
              letterSpacing: TITLE_LETTER_SPACING,
              textShadow: `0 0 ${glowBlur}px rgba(74, 144, 217, ${glowAlpha})`,
            }}
          >
            Prompt-Driven Development
          </span>
        </div>

        {/* Horizontal rule — draws from center outward */}
        <div
          style={{
            position: "absolute",
            top: RULE_Y,
            left: "50%",
            transform: "translateX(-50%)",
            width: ruleCurrentWidth,
            height: RULE_HEIGHT,
            backgroundColor: PDD_BLUE,
            opacity: ruleProgress > 0 ? RULE_OPACITY : 0,
            borderRadius: 1,
          }}
        />
      </AbsoluteFill>

      {/* Terminal overlay — persists from spec 07, fading to lower opacity */}
      <TerminalOverlay opacity={terminalOpacity} />
    </AbsoluteFill>
  );
};

export default ColdOpen08PddTitleCard;
