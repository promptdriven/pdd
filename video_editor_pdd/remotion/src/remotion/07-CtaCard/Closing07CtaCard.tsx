import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  OffthreadVideo,
  staticFile,
} from "remotion";
import { PDDLogo } from "./PDDLogo";
import { Tagline } from "./Tagline";
import { AmberDivider } from "./AmberDivider";
import { CtaText } from "./CtaText";
import { UrlLink } from "./UrlLink";
import {
  CARD_FADE_IN_START,
  CARD_FADE_IN_END,
  FINAL_FADE_START,
  FINAL_FADE_END,
  GLOW_PULSE_CYCLE,
  GLOW_MIN_OPACITY,
  GLOW_MAX_OPACITY,
  CARD_WIDTH,
  CARD_HEIGHT,
  CARD_BORDER_RADIUS,
  CARD_PADDING,
  BG_COLOR,
  BG_OVERLAY_COLOR,
  CARD_BORDER_COLOR,
  BRAND_BLUE,
  BLACK,
} from "./constants";

export const defaultClosing07CtaCardProps = {};

export const Closing07CtaCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Card backing fade in (easeOutCubic) and fade out (easeInCubic)
  const cardOpacity = interpolate(
    frame,
    [CARD_FADE_IN_START, CARD_FADE_IN_END, FINAL_FADE_START, FINAL_FADE_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Final black overlay that fades in at the end
  const blackOverlay = interpolate(
    frame,
    [FINAL_FADE_START, FINAL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  // Ambient glow pulse (sinusoidal oscillation)
  const glowPulse = interpolate(
    Math.sin((frame / GLOW_PULSE_CYCLE) * Math.PI * 2),
    [-1, 1],
    [GLOW_MIN_OPACITY, GLOW_MAX_OPACITY]
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Background video layer */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/closing.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          startFrom={510}
        />
      </AbsoluteFill>

      {/* Semi-transparent dark overlay for contrast */}
      <AbsoluteFill
        style={{
          backgroundColor: "rgba(10, 22, 40, 0.6)",
        }}
      />

      {/* Final black fade layer */}
      <AbsoluteFill
        style={{
          backgroundColor: BLACK,
          opacity: blackOverlay,
        }}
      />

      {/* Centered CTA card */}
      <AbsoluteFill
        style={{
          display: "flex",
          justifyContent: "center",
          alignItems: "center",
          opacity: cardOpacity,
        }}
      >
        <div
          style={{
            width: CARD_WIDTH,
            height: CARD_HEIGHT,
            borderRadius: CARD_BORDER_RADIUS,
            backgroundColor: BG_OVERLAY_COLOR,
            border: `1px solid ${CARD_BORDER_COLOR}`,
            backdropFilter: "blur(16px)",
            WebkitBackdropFilter: "blur(16px)",
            boxShadow: `0 0 60px rgba(59, 130, 246, ${glowPulse}), 0 25px 50px rgba(0, 0, 0, 0.4)`,
            display: "flex",
            flexDirection: "column",
            alignItems: "center",
            justifyContent: "center",
            padding: CARD_PADDING,
          }}
        >
          {/* PDD Logo mark */}
          <PDDLogo />

          {/* Tagline */}
          <Tagline />

          {/* Amber divider */}
          <AmberDivider />

          {/* CTA text */}
          <CtaText />

          {/* URL link */}
          <UrlLink />
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Closing07CtaCard;
