import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing, OffthreadVideo, staticFile } from "remotion";
import { RadialGlow } from "./RadialGlow";
import { QuoteText } from "./QuoteText";
import { HorizontalRule } from "./HorizontalRule";
import { Byline } from "./Byline";
import {
  SCRIM_COLOR_RGB,
  SCRIM_FADE_IN_END,
  SCRIM_MAX_OPACITY,
  FADE_OUT_START,
  FADE_OUT_END,
} from "./constants";

export const defaultPart5Compound10QuoteCardProps = {};

export const Part5Compound10QuoteCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Scrim fades in 0→0.75, then deepens to 1.0 during fade-out (full black)
  const scrimOpacity = interpolate(
    frame,
    [0, SCRIM_FADE_IN_END, FADE_OUT_START, FADE_OUT_END],
    [0, SCRIM_MAX_OPACITY, SCRIM_MAX_OPACITY, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing:
        frame <= SCRIM_FADE_IN_END
          ? Easing.out(Easing.cubic)
          : Easing.in(Easing.quad),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#000000" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part5_compound.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
        />
      </AbsoluteFill>

      {/* Dark scrim overlay */}
      <AbsoluteFill
        style={{
          backgroundColor: `rgba(${SCRIM_COLOR_RGB}, ${scrimOpacity})`,
        }}
      />

      {/* Subtle green radial glow behind text cluster */}
      <RadialGlow opacity={scrimOpacity > 0 ? 1 : 0} />

      {/* Quote text */}
      <QuoteText />

      {/* Expanding horizontal rule */}
      <HorizontalRule />

      {/* Byline */}
      <Byline />
    </AbsoluteFill>
  );
};

export default Part5Compound10QuoteCard;
