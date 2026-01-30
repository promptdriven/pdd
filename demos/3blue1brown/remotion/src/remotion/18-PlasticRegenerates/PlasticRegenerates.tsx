import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { ParticleSystem } from "./ParticleSystem";
import {
  COLORS,
  BEATS,
  PART,
  MOLD,
  PlasticRegeneratesPropsType,
} from "./constants";

/**
 * 18-PlasticRegenerates: A plastic part dissolves into particles
 * and regenerates from the mold direction, demonstrating infinite
 * reproducibility.
 *
 * Animation sequence (300 frames @ 30fps = 10s):
 *   0-30:   Part visible, mold glowing in background
 *   30-90:  Dissolution into 300 particles
 *   90-120: Beat of absence (particles fade)
 *   120-180: Regeneration from mold direction
 *   180-240: Part reformed with completion glow
 *   240-300: Hold with narration
 */
export const PlasticRegenerates: React.FC<PlasticRegeneratesPropsType> = ({
  showNarration = true,
}) => {
  const frame = useCurrentFrame();

  // --- Part visibility ---
  // Visible during setup, fades out at dissolve start, reappears at reformed
  const partOpacityDissolve = interpolate(
    frame,
    [BEATS.SETUP_END, BEATS.DISSOLVE_START + 15],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const partOpacityRegen = interpolate(
    frame,
    [BEATS.REGEN_END - 10, BEATS.REFORMED_START],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const showPartSolid =
    frame < BEATS.DISSOLVE_START + 15 || frame >= BEATS.REGEN_END - 10;
  const partOpacity =
    frame < BEATS.ABSENCE_START ? partOpacityDissolve : partOpacityRegen;

  // --- Mold glow pulse ---
  const moldBaseOpacity = 0.5;
  const moldGlowPulse =
    Math.sin(frame * 0.08) * 0.1 + moldBaseOpacity;
  // Brighter during regeneration
  const moldRegenBoost = interpolate(
    frame,
    [BEATS.REGEN_START, BEATS.REGEN_START + 20, BEATS.REGEN_END - 10, BEATS.REGEN_END],
    [0, 0.3, 0.3, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const moldOpacity = Math.min(moldGlowPulse + moldRegenBoost, 1);

  // --- Completion glow ---
  const completionGlow = interpolate(
    frame,
    [BEATS.REFORMED_START, BEATS.REFORMED_START + 10, BEATS.REFORMED_START + 30, BEATS.REFORMED_END],
    [0, 1, 0.6, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // --- Narration fade ---
  const narrationOpacity = showNarration
    ? interpolate(
        frame,
        [BEATS.NARRATION_START, BEATS.NARRATION_START + 30],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        }
      )
    : 0;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          {/* Metallic gradient for mold body */}
          <linearGradient id="regenMoldGrad" x1="0" y1="0" x2="0" y2="1">
            <stop offset="0%" stopColor="#7a8a9a" />
            <stop offset="50%" stopColor={COLORS.MOLD_BODY} />
            <stop offset="100%" stopColor="#4a5a6a" />
          </linearGradient>
          {/* Gold aura glow for mold */}
          <radialGradient id="moldAura" cx="50%" cy="50%" r="60%">
            <stop offset="0%" stopColor={COLORS.MOLD_GLOW_GOLD} />
            <stop offset="50%" stopColor={COLORS.MOLD_GLOW_WHITE} />
            <stop offset="100%" stopColor="rgba(0,0,0,0)" />
          </radialGradient>
          {/* Completion glow */}
          <radialGradient id="completionGlow" cx="50%" cy="50%" r="50%">
            <stop offset="0%" stopColor={COLORS.COMPLETION_GLOW} />
            <stop offset="60%" stopColor="rgba(217,148,74,0.3)" />
            <stop offset="100%" stopColor="rgba(0,0,0,0)" />
          </radialGradient>
          {/* Drop shadow for mold */}
          <filter
            id="regenMoldShadow"
            x="-20%"
            y="-20%"
            width="140%"
            height="140%"
          >
            <feDropShadow
              dx="2"
              dy="2"
              stdDeviation="4"
              floodColor="#000"
              floodOpacity="0.4"
            />
          </filter>
          {/* Soft glow filter for aura */}
          <filter id="auraBlur" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="30" />
          </filter>
          {/* Glow filter for completion pulse */}
          <filter
            id="completionBlur"
            x="-50%"
            y="-50%"
            width="200%"
            height="200%"
          >
            <feGaussianBlur stdDeviation="20" />
          </filter>
        </defs>

        {/* ====== Mold (background, left side) ====== */}
        <g opacity={moldOpacity}>
          {/* Aura glow behind mold */}
          <ellipse
            cx={MOLD.centerX}
            cy={MOLD.centerY}
            rx={MOLD.width * 1.2}
            ry={MOLD.height * 1.4}
            fill="url(#moldAura)"
            filter="url(#auraBlur)"
          />
          {/* Mold body */}
          <rect
            x={MOLD.centerX - MOLD.width / 2}
            y={MOLD.centerY - MOLD.height / 2}
            width={MOLD.width}
            height={MOLD.height}
            rx={6}
            fill="url(#regenMoldGrad)"
            stroke={COLORS.MOLD_EDGE}
            strokeWidth={2}
            filter="url(#regenMoldShadow)"
          />
          {/* Cavity */}
          <rect
            x={MOLD.centerX - MOLD.cavityWidth / 2}
            y={MOLD.centerY - MOLD.cavityHeight / 2}
            width={MOLD.cavityWidth}
            height={MOLD.cavityHeight}
            rx={6}
            fill={COLORS.MOLD_CAVITY}
          />
        </g>

        {/* ====== Particle System (dissolve + regenerate) ====== */}
        <ParticleSystem />

        {/* ====== Solid Part ====== */}
        {showPartSolid && partOpacity > 0.01 && (
          <rect
            x={PART.centerX - PART.width / 2}
            y={PART.centerY - PART.height / 2}
            width={PART.width}
            height={PART.height}
            rx={PART.rx}
            fill={COLORS.PART_AMBER}
            opacity={partOpacity}
          />
        )}

        {/* ====== Completion Glow ====== */}
        {completionGlow > 0.01 && (
          <ellipse
            cx={PART.centerX}
            cy={PART.centerY}
            rx={PART.width * 1.5}
            ry={PART.height * 2}
            fill="url(#completionGlow)"
            opacity={completionGlow}
            filter="url(#completionBlur)"
          />
        )}
      </svg>

      {/* ====== Narration Overlay ====== */}
      {narrationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 120,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narrationOpacity,
          }}
        >
          <div
            style={{
              fontSize: 32,
              fontFamily: "sans-serif",
              fontWeight: 400,
              color: "rgba(255, 255, 255, 0.95)",
              lineHeight: 1.6,
              maxWidth: 900,
              margin: "0 auto",
              letterSpacing: 0.5,
            }}
          >
            The plastic part? Disposable. Regenerate it at will.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
