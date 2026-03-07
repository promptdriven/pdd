import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame } from "remotion";
import { TricolorBar } from "./TricolorBar";

// Part 3 specific constants
const BG_COLOR = "#0F172A";
const EYEBROW_COLOR = "#A855F7";
const TITLE_COLOR = "#FFFFFF";
const TEXT_SHADOW = "0 4px 24px rgba(168, 85, 247, 0.3)";

const BG_FADE_IN_END = 20;
const EYEBROW_FADE_START = 15;
const EYEBROW_FADE_END = 35;
const TITLE_FADE_START = 25;
const TITLE_FADE_END = 50;
const CARD_FADE_OUT_START = 120;
const CARD_FADE_OUT_END = 150;

const GLOW_CENTER_X = 960;
const GLOW_CENTER_Y = 450;
const GLOW_RADIUS = 600;

const EYEBROW_Y = 350;
const TITLE_Y = 450;

export const defaultPart3Mold01TitleCardProps = {};

export const Part3Mold01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(frame, [0, BG_FADE_IN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const fadeOut = interpolate(
    frame,
    [CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  const bgOpacity = fadeIn * fadeOut;

  // Eyebrow animations
  const eyebrowFadeIn = interpolate(
    frame,
    [EYEBROW_FADE_START, EYEBROW_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const eyebrowTranslateY = interpolate(
    frame,
    [EYEBROW_FADE_START, EYEBROW_FADE_END],
    [20, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Title animations
  const titleFadeIn = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  const titleScale = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [0.9, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR, opacity: bgOpacity }}>
      {/* Tricolor radial glow (green/gold/purple blend) */}
      <AbsoluteFill
        style={{
          background: `
            radial-gradient(circle ${GLOW_RADIUS}px at ${GLOW_CENTER_X}px ${GLOW_CENTER_Y}px,
              rgba(34, 197, 94, 0.15),
              rgba(245, 158, 11, 0.1) 40%,
              rgba(168, 85, 247, 0.08) 70%,
              transparent
            )
          `,
          opacity: bgOpacity * 0.6,
        }}
      />

      {/* Eyebrow "PART 3" */}
      <div
        style={{
          position: "absolute",
          top: EYEBROW_Y,
          left: 0,
          right: 0,
          display: "flex",
          justifyContent: "center",
          opacity: eyebrowFadeIn * fadeOut,
          transform: `translateY(${eyebrowTranslateY}px)`,
          fontFamily: "'Inter', sans-serif",
          fontWeight: 500,
          fontSize: 24,
          color: EYEBROW_COLOR,
          letterSpacing: "0.2em",
          textTransform: "uppercase" as const,
          textShadow: TEXT_SHADOW,
          textAlign: "center" as const,
        }}
      >
        PART 3
      </div>

      {/* Main title */}
      <div
        style={{
          position: "absolute",
          top: TITLE_Y,
          left: 0,
          right: 0,
          display: "flex",
          justifyContent: "center",
          opacity: titleFadeIn * fadeOut,
        }}
      >
        <div
          style={{
            transform: `scale(${titleScale})`,
            transformOrigin: "center center",
            fontFamily: "'Inter', sans-serif",
            fontWeight: 700,
            fontSize: 64,
            color: TITLE_COLOR,
            letterSpacing: "-0.02em",
            textShadow: TEXT_SHADOW,
            textAlign: "center" as const,
            whiteSpace: "nowrap" as const,
          }}
        >
          The Mold Has Three Parts
        </div>
      </div>

      {/* Tricolor accent bar */}
      <TricolorBar />
    </AbsoluteFill>
  );
};

export default Part3Mold01TitleCard;
