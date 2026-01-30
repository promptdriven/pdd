import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { AuraEffect } from "./AuraEffect";
import { ChairSilhouette } from "./ChairSilhouette";
import { MoldScene } from "./MoldScene";
import { COLORS, BEATS, ValueAuraPropsType } from "./constants";

export const ValueAura: React.FC<ValueAuraPropsType> = ({
  showNarration = true,
}) => {
  const frame = useCurrentFrame();

  // --- Left aura (chair): fades in frame 90-180, stays through end ---
  const leftAuraOpacity = interpolate(
    frame,
    [BEATS.LEFT_AURA_START, BEATS.LEFT_AURA_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // --- Right aura (mold): fades in frame 180-270, stays through end ---
  const rightAuraOpacity = interpolate(
    frame,
    [BEATS.RIGHT_AURA_START, BEATS.RIGHT_AURA_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // --- Labels: fade in frame 360-400 ---
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_START + 40],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  // --- Narration 1: fades in at frame 90, fades out at frame 240 ---
  const narration1Opacity = showNarration
    ? interpolate(
        frame,
        [
          BEATS.NARRATION_1_START,
          BEATS.NARRATION_1_START + 30,
          BEATS.RIGHT_AURA_START + 60,
          BEATS.RIGHT_AURA_START + 90,
        ],
        [0, 1, 1, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
      )
    : 0;

  // --- Narration 2: fades in at frame 270, stays ---
  const narration2Opacity = showNarration
    ? interpolate(
        frame,
        [BEATS.NARRATION_2_START, BEATS.NARRATION_2_START + 30],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
      )
    : 0;

  // --- Subtle scene preparation: very gentle brightness increase 0-90 ---
  const prepareBrightness = interpolate(
    frame,
    [BEATS.PREPARE_START, BEATS.PREPARE_END],
    [0.92, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  return (
    <AbsoluteFill
      style={{
        filter: `brightness(${prepareBrightness})`,
      }}
    >
      {/* === LEFT PANEL: Crafted chair on warm background === */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: 960,
          height: 1080,
          overflow: "hidden",
          background: `linear-gradient(180deg, ${COLORS.LEFT_BG} 0%, ${COLORS.LEFT_BG_GRADIENT_END} 100%)`,
        }}
      >
        {/* Chair aura (behind the chair) */}
        <AuraEffect
          centerX={480}
          centerY={490}
          radiusX={220}
          radiusY={260}
          opacity={leftAuraOpacity}
        />

        {/* Chair silhouette */}
        <ChairSilhouette />

        {/* Label: "Value in Object" */}
        {labelOpacity > 0 && (
          <div
            style={{
              position: "absolute",
              bottom: 80,
              left: 0,
              right: 0,
              textAlign: "center",
              opacity: labelOpacity,
            }}
          >
            <span
              style={{
                fontFamily: "sans-serif",
                fontSize: 24,
                fontWeight: 600,
                color: COLORS.LABEL_WHITE,
                textTransform: "uppercase" as const,
                letterSpacing: 3,
                textShadow: "0 2px 10px rgba(0,0,0,0.7)",
              }}
            >
              Value in Object
            </span>
          </div>
        )}
      </div>

      {/* === RIGHT PANEL: Mold + parts on dark background === */}
      <div
        style={{
          position: "absolute",
          right: 0,
          top: 0,
          width: 960,
          height: 1080,
          overflow: "hidden",
          background: `linear-gradient(180deg, ${COLORS.RIGHT_BG} 0%, ${COLORS.RIGHT_BG_GRADIENT_END} 100%)`,
        }}
      >
        {/* Mold aura (around the mold, NOT the parts) */}
        <AuraEffect
          centerX={480}
          centerY={400}
          radiusX={240}
          radiusY={140}
          opacity={rightAuraOpacity}
        />

        {/* Mold cross-section + dim parts */}
        <MoldScene />

        {/* Label: "Value in Specification" */}
        {labelOpacity > 0 && (
          <div
            style={{
              position: "absolute",
              bottom: 80,
              left: 0,
              right: 0,
              textAlign: "center",
              opacity: labelOpacity,
            }}
          >
            <span
              style={{
                fontFamily: "sans-serif",
                fontSize: 24,
                fontWeight: 600,
                color: COLORS.LABEL_WHITE,
                textTransform: "uppercase" as const,
                letterSpacing: 3,
                textShadow: "0 2px 10px rgba(0,0,0,0.7)",
              }}
            >
              Value in Specification
            </span>
          </div>
        )}
      </div>

      {/* === CENTER DIVIDER === */}
      <div
        style={{
          position: "absolute",
          left: 960,
          top: 0,
          width: 1,
          height: 1080,
          backgroundColor: COLORS.DIVIDER,
          pointerEvents: "none",
        }}
      />

      {/* === NARRATION OVERLAYS === */}
      {/* Narration 1: "In crafting, value lives in the object..." */}
      {narration1Opacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 40,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narration1Opacity,
            pointerEvents: "none",
          }}
        >
          <div
            style={{
              fontSize: 30,
              fontFamily: "sans-serif",
              fontWeight: 400,
              color: "rgba(255, 255, 255, 0.95)",
              lineHeight: 1.6,
              maxWidth: 800,
              margin: "0 auto",
              letterSpacing: 0.5,
              textShadow: "0 2px 12px rgba(0,0,0,0.8)",
            }}
          >
            In crafting, value lives in the object...
          </div>
        </div>
      )}

      {/* Narration 2: "In molding, value lives in the specification -- the mold." */}
      {narration2Opacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 40,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narration2Opacity,
            pointerEvents: "none",
          }}
        >
          <div
            style={{
              fontSize: 30,
              fontFamily: "sans-serif",
              fontWeight: 400,
              color: "rgba(255, 255, 255, 0.95)",
              lineHeight: 1.6,
              maxWidth: 900,
              margin: "0 auto",
              letterSpacing: 0.5,
              textShadow: "0 2px 12px rgba(0,0,0,0.8)",
            }}
          >
            In molding, value lives in the specification — the mold.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
