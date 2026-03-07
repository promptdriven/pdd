import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame } from "remotion";

// Part 4 specific constants
const BG_COLOR = "#0F172A";
const AMBER = "#F59E0B";
const GLOW_COLOR = "#3D2B0A";
const TITLE_COLOR = "#FFFFFF";
const TEXT_SHADOW = "0 4px 24px rgba(245, 158, 11, 0.3)";

const BG_FADE_IN_END = 20;
const EYEBROW_FADE_START = 15;
const EYEBROW_FADE_END = 35;
const TITLE_FADE_START = 25;
const TITLE_FADE_END = 50;
const RULE_EXPAND_START = 40;
const RULE_EXPAND_END = 60;
const CARD_FADE_OUT_START = 120;
const CARD_FADE_OUT_END = 150;

const GLOW_CENTER_X = 960;
const GLOW_CENTER_Y = 480;
const GLOW_RADIUS = 800;

const EYEBROW_Y = 360;
const TITLE_Y = 460;
const RULE_Y = 520;
const RULE_MAX_WIDTH = 360;
const RULE_HEIGHT = 2;
const RULE_OPACITY = 0.6;

export const defaultPart4Precision01TitleCardProps = {};

export const Part4Precision01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fade in
  const fadeIn = interpolate(frame, [0, BG_FADE_IN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Card fade out
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

  // Horizontal rule animation
  const ruleWidth = interpolate(
    frame,
    [RULE_EXPAND_START, RULE_EXPAND_END],
    [0, RULE_MAX_WIDTH],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR, opacity: bgOpacity }}>
      {/* Warm amber radial glow */}
      <AbsoluteFill
        style={{
          background: `radial-gradient(circle ${GLOW_RADIUS}px at ${GLOW_CENTER_X}px ${GLOW_CENTER_Y}px, ${GLOW_COLOR}, transparent)`,
          opacity: bgOpacity * 0.6,
        }}
      />

      {/* Eyebrow "PART 4" */}
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
          color: AMBER,
          letterSpacing: "0.2em",
          textTransform: "uppercase" as const,
          textShadow: TEXT_SHADOW,
          textAlign: "center" as const,
        }}
      >
        PART 4
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
          Precision Brings Cost
        </div>
      </div>

      {/* Horizontal rule expanding from center */}
      <div
        style={{
          position: "absolute",
          top: RULE_Y,
          left: "50%",
          transform: "translateX(-50%)",
          width: ruleWidth,
          height: RULE_HEIGHT,
          backgroundColor: AMBER,
          opacity: RULE_OPACITY * fadeOut,
        }}
      />
    </AbsoluteFill>
  );
};

export default Part4Precision01TitleCard;
