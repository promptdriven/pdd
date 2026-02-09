import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
  OffthreadVideo,
  staticFile,
} from "remotion";
import {
  COLORS,
  PATCH_CYCLE_FPS,
  PATCH_CYCLE_VIDEO_FILE,
  PatchCyclePropsType,
} from "./constants";

/**
 * Patch Cycle composition — Section 1.9 (spec 10_patch_cycle)
 *
 * Displays a Veo 3.1 video of a developer sighing and beginning another
 * patch cycle. This is the emotional low point of Part 1, depicting the
 * Sisyphean maintenance grind.
 *
 * When the video asset is unavailable (usePlaceholder=true), renders a
 * styled placeholder with a dark workstation aesthetic and descriptive text.
 */
export const PatchCycle: React.FC<PatchCyclePropsType> = ({
  usePlaceholder = true,
}) => {
  const frame = useCurrentFrame();

  // Subtle slow push-in zoom for placeholder (matches spec: "static or very slow push-in camera")
  const scale = interpolate(
    frame,
    [0, PATCH_CYCLE_FPS * 10],
    [1.0, 1.03],
    { extrapolateRight: "clamp" }
  );

  // Fade in at start
  const fadeIn = interpolate(
    frame,
    [0, 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Placeholder text fade-in (staggered)
  const titleOpacity = interpolate(
    frame,
    [10, 35],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const subtitleOpacity = interpolate(
    frame,
    [30, 55],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Breathing glow effect for monitor light
  const glowIntensity = interpolate(
    Math.sin(frame * 0.04),
    [-1, 1],
    [0.08, 0.2]
  );

  if (!usePlaceholder) {
    // Render the actual Veo video
    return (
      <AbsoluteFill style={{ opacity: fadeIn }}>
        <OffthreadVideo
          src={staticFile(PATCH_CYCLE_VIDEO_FILE)}
          style={{
            width: "100%",
            height: "100%",
            objectFit: "cover",
          }}
        />
      </AbsoluteFill>
    );
  }

  // Placeholder: dark workstation scene with descriptive text
  return (
    <AbsoluteFill
      style={{
        opacity: fadeIn,
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT} 100%)`,
        overflow: "hidden",
      }}
    >
      {/* Simulated monitor glow */}
      <div
        style={{
          position: "absolute",
          top: "20%",
          left: "30%",
          width: "40%",
          height: "35%",
          background: `radial-gradient(ellipse, rgba(70, 130, 220, ${glowIntensity}) 0%, transparent 70%)`,
          transform: `scale(${scale})`,
          transformOrigin: "center center",
        }}
      />

      {/* Secondary ambient glow (warm, from desk lamp) */}
      <div
        style={{
          position: "absolute",
          bottom: "15%",
          right: "20%",
          width: "25%",
          height: "25%",
          background: `radial-gradient(ellipse, rgba(200, 160, 100, ${glowIntensity * 0.5}) 0%, transparent 70%)`,
        }}
      />

      {/* Center content */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          right: 0,
          bottom: 0,
          display: "flex",
          flexDirection: "column",
          alignItems: "center",
          justifyContent: "center",
          transform: `scale(${scale})`,
          transformOrigin: "center center",
        }}
      >
        {/* Placeholder label */}
        <div
          style={{
            opacity: titleOpacity,
            fontSize: 48,
            fontFamily: "sans-serif",
            fontWeight: 600,
            color: COLORS.LABEL_WHITE,
            letterSpacing: 2,
            marginBottom: 16,
          }}
        >
          Patch Cycle
        </div>

        <div
          style={{
            opacity: subtitleOpacity,
            fontSize: 22,
            fontFamily: "sans-serif",
            fontWeight: 300,
            color: COLORS.LABEL_DIM,
            letterSpacing: 0.5,
            maxWidth: 700,
            textAlign: "center",
            lineHeight: 1.6,
          }}
        >
          Veo 3.1 &mdash; Developer sighs, accepts, begins another patch
        </div>

        {/* Asset-needed indicator */}
        <div
          style={{
            opacity: subtitleOpacity * 0.6,
            marginTop: 40,
            padding: "8px 20px",
            borderRadius: 6,
            border: `1px solid ${COLORS.ACCENT_BLUE}`,
            fontSize: 14,
            fontFamily: "monospace",
            color: COLORS.ACCENT_BLUE,
            letterSpacing: 1,
          }}
        >
          AWAITING VIDEO ASSET: {PATCH_CYCLE_VIDEO_FILE}
        </div>
      </div>
    </AbsoluteFill>
  );
};
