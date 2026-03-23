import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { GlowingBracket } from "./GlowingBracket";
import { TerminalCursor } from "./TerminalCursor";
import {
  BG_DEEP_NAVY,
  ACCENT_BLUE,
  ACCENT_CYAN,
  ACCENT_GREEN,
  TEXT_PRIMARY,
  TEXT_SECONDARY,
  GLOW_BLUE,
  GLOW_CYAN,
  BRACKET_COLOR,
  DIVIDER_COLOR,
  FONT_MONO,
  FONT_SANS,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CENTER_X,
  CENTER_Y,
  FPS,
  PHASE_BRACKET_DRAW,
  PHASE_PDD_REVEAL,
  PHASE_SUBTITLE_IN,
  PHASE_DIVIDER_IN,
  PHASE_TAGLINE_IN,
  PHASE_GLOW_PULSE,
  PHASE_CURSOR_BLINK,
} from "./constants";

export const defaultColdOpen08PddTitleCardProps = {};

export const ColdOpen08PddTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ─── Bracket Draw Animation ────────────────────────────────────
  const bracketDraw = interpolate(
    frame,
    [PHASE_BRACKET_DRAW.start, PHASE_BRACKET_DRAW.end],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  // ─── PDD Letters Reveal ────────────────────────────────────────
  const pddRevealRaw = interpolate(
    frame,
    [PHASE_PDD_REVEAL.start, PHASE_PDD_REVEAL.end],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  // Individual letter staggers
  const letterDelays = [0, 0.15, 0.3];

  const getLetterProgress = (index: number) => {
    const delayed = interpolate(
      pddRevealRaw,
      [letterDelays[index], letterDelays[index] + 0.55],
      [0, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
    );
    return delayed;
  };

  // ─── Subtitle Fade-in ──────────────────────────────────────────
  const subtitleOpacity = interpolate(
    frame,
    [PHASE_SUBTITLE_IN.start, PHASE_SUBTITLE_IN.end],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );
  const subtitleY = interpolate(
    frame,
    [PHASE_SUBTITLE_IN.start, PHASE_SUBTITLE_IN.end],
    [14, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  // ─── Divider line ──────────────────────────────────────────────
  const dividerScale = interpolate(
    frame,
    [PHASE_DIVIDER_IN.start, PHASE_DIVIDER_IN.end],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  // ─── Tagline ───────────────────────────────────────────────────
  const taglineOpacity = interpolate(
    frame,
    [PHASE_TAGLINE_IN.start, PHASE_TAGLINE_IN.end],
    [0, 0.85],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );
  const taglineY = interpolate(
    frame,
    [PHASE_TAGLINE_IN.start, PHASE_TAGLINE_IN.end],
    [12, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  // ─── Glow Pulse (breathing effect) ────────────────────────────
  const glowIntensity =
    frame >= PHASE_GLOW_PULSE.start
      ? interpolate(
          Math.sin(
            ((frame - PHASE_GLOW_PULSE.start) / FPS) * Math.PI * 1.2
          ),
          [-1, 1],
          [0, 1]
        )
      : 0;

  // ─── Background Grid Lines (subtle) ────────────────────────────
  const gridOpacity = interpolate(frame, [0, 20], [0.03, 0.06], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ─── Cursor Blink Phase ────────────────────────────────────────
  const cursorVisible = frame >= PHASE_CURSOR_BLINK.start;

  // ─── Radial Glow Behind PDD ────────────────────────────────────
  const centralGlowOpacity = interpolate(
    frame,
    [PHASE_PDD_REVEAL.start, PHASE_PDD_REVEAL.end, PHASE_GLOW_PULSE.start],
    [0, 0.3, 0.25],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // ─── Title "P·D·D" letters ─────────────────────────────────────
  const pddLetters = ["P", "D", "D"];
  const pddSeparator = " · ";

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_DEEP_NAVY,
        fontFamily: FONT_SANS,
        overflow: "hidden",
      }}
    >
      {/* ── Background Grid Pattern ─────────────────────────────── */}
      <AbsoluteFill style={{ opacity: gridOpacity }}>
        <svg width={CANVAS_WIDTH} height={CANVAS_HEIGHT}>
          {/* Vertical lines */}
          {Array.from({ length: 25 }, (_, i) => {
            const x = (i + 1) * (CANVAS_WIDTH / 26);
            return (
              <line
                key={`v-${i}`}
                x1={x}
                y1={0}
                x2={x}
                y2={CANVAS_HEIGHT}
                stroke={ACCENT_BLUE}
                strokeWidth={0.5}
              />
            );
          })}
          {/* Horizontal lines */}
          {Array.from({ length: 14 }, (_, i) => {
            const y = (i + 1) * (CANVAS_HEIGHT / 15);
            return (
              <line
                key={`h-${i}`}
                x1={0}
                y1={y}
                x2={CANVAS_WIDTH}
                y2={y}
                stroke={ACCENT_BLUE}
                strokeWidth={0.5}
              />
            );
          })}
        </svg>
      </AbsoluteFill>

      {/* ── Central Radial Glow ──────────────────────────────────── */}
      <div
        style={{
          position: "absolute",
          top: CENTER_Y - 300,
          left: CENTER_X - 400,
          width: 800,
          height: 600,
          borderRadius: "50%",
          background: `radial-gradient(ellipse, ${GLOW_BLUE} 0%, ${GLOW_CYAN} 40%, transparent 70%)`,
          opacity: centralGlowOpacity,
          filter: "blur(60px)",
          pointerEvents: "none",
        }}
      />

      {/* ── Main Title Block ─────────────────────────────────────── */}
      <AbsoluteFill
        style={{
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        {/* Bracket + PDD Row */}
        <div
          style={{
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            gap: 28,
            marginBottom: 16,
          }}
        >
          {/* Left Bracket */}
          <div style={{ width: 56, height: 140, flexShrink: 0 }}>
            <GlowingBracket
              side="left"
              drawProgress={bracketDraw}
              glowIntensity={glowIntensity}
              bracketColor={BRACKET_COLOR}
              glowColor={GLOW_BLUE}
              height={130}
              strokeWidth={4}
              armLength={44}
            />
          </div>

          {/* PDD Letters */}
          <div
            style={{
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              gap: 0,
            }}
          >
            {pddLetters.map((letter, i) => {
              const progress = getLetterProgress(i);
              const letterOpacity = interpolate(progress, [0, 0.5], [0, 1], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              });
              const letterScale = interpolate(progress, [0, 1], [0.7, 1], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              });
              const letterY = interpolate(progress, [0, 1], [20, 0], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              });

              return (
                <React.Fragment key={i}>
                  {i > 0 && (
                    <span
                      style={{
                        fontSize: 72,
                        fontFamily: FONT_MONO,
                        color: ACCENT_CYAN,
                        opacity: Math.min(
                          letterOpacity,
                          getLetterProgress(i - 1) > 0.3 ? 0.8 : 0
                        ),
                        fontWeight: 300,
                        lineHeight: 1,
                        userSelect: "none",
                      }}
                    >
                      {pddSeparator}
                    </span>
                  )}
                  <span
                    style={{
                      fontSize: 128,
                      fontFamily: FONT_MONO,
                      fontWeight: 700,
                      color: TEXT_PRIMARY,
                      opacity: letterOpacity,
                      transform: `translateY(${letterY}px) scale(${letterScale})`,
                      display: "inline-block",
                      lineHeight: 1,
                      textShadow: `0 0 ${20 + glowIntensity * 15}px ${GLOW_BLUE}, 0 0 ${40 + glowIntensity * 20}px ${GLOW_CYAN}`,
                      letterSpacing: "0.05em",
                    }}
                  >
                    {letter}
                  </span>
                </React.Fragment>
              );
            })}

            {/* Blinking cursor after the last D */}
            <div
              style={{
                display: "inline-flex",
                alignItems: "center",
                height: 128,
                marginLeft: 6,
              }}
            >
              <TerminalCursor
                visible={cursorVisible}
                color={ACCENT_GREEN}
                width={4}
                height={90}
                blinkRate={18}
              />
            </div>
          </div>

          {/* Right Bracket */}
          <div style={{ width: 56, height: 140, flexShrink: 0 }}>
            <GlowingBracket
              side="right"
              drawProgress={bracketDraw}
              glowIntensity={glowIntensity}
              bracketColor={BRACKET_COLOR}
              glowColor={GLOW_BLUE}
              height={130}
              strokeWidth={4}
              armLength={44}
            />
          </div>
        </div>

        {/* Subtitle: "Prompt-Driven Development" */}
        <div
          style={{
            opacity: subtitleOpacity,
            transform: `translateY(${subtitleY}px)`,
            fontSize: 36,
            fontFamily: FONT_SANS,
            fontWeight: 400,
            color: TEXT_PRIMARY,
            letterSpacing: "0.18em",
            textTransform: "uppercase",
            marginTop: 8,
            textShadow: `0 0 12px ${GLOW_BLUE}`,
          }}
        >
          Prompt-Driven Development
        </div>

        {/* Divider */}
        <div
          style={{
            width: 480,
            height: 2,
            marginTop: 28,
            marginBottom: 28,
            overflow: "hidden",
          }}
        >
          <div
            style={{
              width: "100%",
              height: "100%",
              background: `linear-gradient(90deg, transparent 0%, ${DIVIDER_COLOR} 20%, ${ACCENT_BLUE} 50%, ${DIVIDER_COLOR} 80%, transparent 100%)`,
              transform: `scaleX(${dividerScale})`,
              opacity: 0.85,
            }}
          />
        </div>

        {/* Tagline */}
        <div
          style={{
            opacity: taglineOpacity,
            transform: `translateY(${taglineY}px)`,
            fontSize: 22,
            fontFamily: FONT_MONO,
            fontWeight: 400,
            color: TEXT_SECONDARY,
            letterSpacing: "0.06em",
            textAlign: "center",
            lineHeight: 1.6,
            maxWidth: 700,
          }}
        >
          When the prompt <span style={{ color: ACCENT_GREEN }}>is</span> the
          program
        </div>
      </AbsoluteFill>

      {/* ── Corner Decorations ───────────────────────────────────── */}
      {/* Top-left code hint */}
      <div
        style={{
          position: "absolute",
          top: 48,
          left: 56,
          fontFamily: FONT_MONO,
          fontSize: 15,
          color: TEXT_SECONDARY,
          opacity: interpolate(frame, [10, 30], [0, 0.5], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
          letterSpacing: "0.04em",
        }}
      >
        <span style={{ color: ACCENT_BLUE }}>{"// "}</span>
        cold_open_08
      </div>

      {/* Bottom-right version tag */}
      <div
        style={{
          position: "absolute",
          bottom: 48,
          right: 56,
          fontFamily: FONT_MONO,
          fontSize: 14,
          color: TEXT_SECONDARY,
          opacity: interpolate(frame, [40, 60], [0, 0.45], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
          letterSpacing: "0.03em",
        }}
      >
        <span style={{ color: ACCENT_CYAN }}>v</span>0.8.0
      </div>

      {/* ── Scan-line Effect (very subtle) ───────────────────────── */}
      <AbsoluteFill
        style={{
          background:
            "repeating-linear-gradient(0deg, transparent, transparent 3px, rgba(0,0,0,0.03) 3px, rgba(0,0,0,0.03) 4px)",
          pointerEvents: "none",
          opacity: 0.4,
        }}
      />
    </AbsoluteFill>
  );
};

export default ColdOpen08PddTitleCard;
