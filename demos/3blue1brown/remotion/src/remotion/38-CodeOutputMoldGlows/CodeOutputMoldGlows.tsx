import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, GENERATED_CODE, CodeOutputMoldGlowsPropsType } from "./constants";

// Helper: convert hex color to RGB string for rgba() usage
const hexToRgb = (hex: string): string => {
  const r = parseInt(hex.slice(1, 3), 16);
  const g = parseInt(hex.slice(3, 5), 16);
  const b = parseInt(hex.slice(5, 7), 16);
  return `${r}, ${g}, ${b}`;
};

// MiniComponent: a single labeled mold component box with individual glow
const MiniComponent: React.FC<{
  label: string;
  color: string;
  glowIntensity: number;
}> = ({ label, color, glowIntensity }) => {
  const rgb = hexToRgb(color);
  return (
    <div
      style={{
        padding: "12px 24px",
        background: `rgba(${rgb}, ${0.1 + 0.1 * glowIntensity})`,
        border: `2px solid ${color}`,
        borderRadius: 8,
        boxShadow: `0 0 ${20 * glowIntensity}px ${color}`,
        fontSize: 14,
        fontWeight: "bold",
        color: color,
        fontFamily: "monospace",
        textAlign: "center",
        minWidth: 100,
      }}
    >
      {label}
    </div>
  );
};

// MoldSystem: three labeled component boxes in a horizontal layout
const MoldSystem: React.FC<{ glowIntensity: number }> = ({ glowIntensity }) => {
  return (
    <div
      style={{
        position: "absolute",
        top: 100,
        left: "50%",
        transform: "translateX(-50%)",
      }}
    >
      <div
        style={{
          display: "flex",
          gap: 30,
          marginBottom: 30,
        }}
      >
        <MiniComponent
          label="PROMPT"
          color={COLORS.PROMPT_BLUE}
          glowIntensity={glowIntensity}
        />
        <MiniComponent
          label="TESTS"
          color={COLORS.TESTS_AMBER}
          glowIntensity={glowIntensity}
        />
        <MiniComponent
          label="GROUNDING"
          color={COLORS.GROUNDING_GREEN}
          glowIntensity={glowIntensity}
        />
      </div>
    </div>
  );
};

// GeneratedCode: actual readable code with glow border that fades
const GeneratedCode: React.FC<{
  glowIntensity: number;
  opacity: number;
}> = ({ glowIntensity, opacity }) => {
  const glowColor = `rgba(138, 156, 175, ${0.5 * glowIntensity})`;

  return (
    <div
      style={{
        position: "absolute",
        bottom: 180,
        left: "50%",
        transform: "translateX(-50%)",
        opacity,
      }}
    >
      <div
        style={{
          width: 500,
          padding: 20,
          background: "#1E1E2E",
          borderRadius: 8,
          boxShadow:
            glowIntensity > 0.1
              ? `0 0 ${40 * glowIntensity}px ${glowColor}`
              : "none",
          border:
            glowIntensity > 0.1
              ? `1px solid rgba(138, 156, 175, ${0.3 * glowIntensity})`
              : "1px solid #333",
        }}
      >
        <pre
          style={{
            fontSize: 12,
            fontFamily: "'JetBrains Mono', monospace",
            color: `rgba(160, 160, 160, ${0.5 + opacity * 0.5})`,
            margin: 0,
            whiteSpace: "pre",
            lineHeight: 1.5,
          }}
        >
          {GENERATED_CODE}
        </pre>
      </div>
    </div>
  );
};

// FinalMessage: two lines of text that fade in sequentially
const FinalMessage: React.FC<{
  line1: string;
  line2: string;
  line1Opacity: number;
  line2Opacity: number;
  moldGlowIntensity: number;
}> = ({ line1, line2, line1Opacity, line2Opacity, moldGlowIntensity }) => {
  return (
    <div
      style={{
        position: "absolute",
        bottom: 60,
        left: "50%",
        transform: "translateX(-50%)",
        textAlign: "center",
      }}
    >
      <div
        style={{
          fontSize: 24,
          color: "#888",
          opacity: line1Opacity,
          marginBottom: 12,
        }}
      >
        {line1}
      </div>
      <div
        style={{
          fontSize: 28,
          color: "#FFF",
          fontWeight: "bold",
          opacity: line2Opacity,
          textShadow:
            moldGlowIntensity > 0.5
              ? `
              0 0 30px rgba(${hexToRgb(COLORS.PROMPT_BLUE)}, ${0.4 * moldGlowIntensity}),
              0 0 30px rgba(${hexToRgb(COLORS.TESTS_AMBER)}, ${0.3 * moldGlowIntensity}),
              0 0 30px rgba(${hexToRgb(COLORS.GROUNDING_GREEN)}, ${0.3 * moldGlowIntensity})
            `
              : "none",
        }}
      >
        {line2}
      </div>
    </div>
  );
};

export const CodeOutputMoldGlows: React.FC<CodeOutputMoldGlowsPropsType> = ({
  showMessages = true,
  durationFrames,
}) => {
  const frame = useCurrentFrame();

  // Scale factor: when durationFrames is provided, proportionally compress
  // all animation keyframes so the full five-phase sequence fits within
  // the available time. Default is 1.0 (20s / 600 frames).
  const totalFrames = durationFrames ?? BEATS.TOTAL_FRAMES;
  const scale = totalFrames / BEATS.TOTAL_FRAMES;

  // Helper to scale a frame number
  const sf = (f: number) => Math.round(f * scale);

  // ── Phase 1 (0-4s): Code glows brightly ──────────────────────────
  // Code glow holds at 1.0 for the first 4s then fades to 0 by 10s
  const codeGlow = interpolate(
    frame,
    [0, sf(BEATS.CODE_GLOW_HOLD_END), sf(BEATS.CODE_FADE_END)],
    [1, 1, 0],
    { extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  // ── Phase 2 (4-10s): Code opacity dims but stays visible ────────
  // Code starts fully visible (1.0) and dims to 0.5
  const codeOpacity = interpolate(
    frame,
    [0, sf(BEATS.CODE_FADE_END)],
    [1, 0.5],
    { extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  // ── Phase 3 (10-14s): Mold glow increases ───────────────────────
  // Mold glow starts at 0.5 and rises to 1.0 with easeOutQuad
  const moldGlow = interpolate(
    frame,
    [sf(BEATS.MOLD_GLOW_START), sf(BEATS.MOLD_GLOW_END)],
    [0.5, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Phase 4 (14-18s): First message appears ─────────────────────
  const message1Opacity = showMessages
    ? interpolate(
        frame,
        [sf(BEATS.MESSAGE_1_START), sf(BEATS.MESSAGE_1_END)],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
      )
    : 0;

  // ── Phase 5 (18-20s): Second message appears ────────────────────
  const message2Opacity = showMessages
    ? interpolate(
        frame,
        [sf(BEATS.MESSAGE_2_START), sf(BEATS.MESSAGE_2_END)],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
      )
    : 0;

  // Final mold glow boost when the second message appears
  const finalGlowBoost = interpolate(
    frame,
    [sf(BEATS.MESSAGE_2_START), sf(BEATS.MESSAGE_2_END)],
    [1.0, 1.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const finalMoldGlow = moldGlow * finalGlowBoost;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Mold system: three labeled component boxes */}
      <MoldSystem glowIntensity={finalMoldGlow} />

      {/* Generated code: actual readable Python code with glow border */}
      <GeneratedCode glowIntensity={codeGlow} opacity={codeOpacity} />

      {/* Final messages */}
      <FinalMessage
        line1="The code is output."
        line2="The mold is what matters."
        line1Opacity={message1Opacity}
        line2Opacity={message2Opacity}
        moldGlowIntensity={finalMoldGlow}
      />
    </AbsoluteFill>
  );
};
