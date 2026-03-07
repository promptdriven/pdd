import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { Part5RadialGlow } from "./Part5RadialGlow";
import { Part5EyebrowLabel } from "./Part5EyebrowLabel";
import { Part5TitleText } from "./Part5TitleText";
import { Part5HorizontalRule } from "./Part5HorizontalRule";
import {
  BG_COLOR,
  BG_FADE_IN_END,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
} from "./part5Constants";

export const defaultPart5Compound01TitleCardProps = {};

export const Part5Compound01TitleCard: React.FC = () => {
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

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR, opacity: bgOpacity }}>
      {/* Cool blue-green radial glow */}
      <Part5RadialGlow opacity={bgOpacity} />

      {/* Eyebrow "PART 5" */}
      <Part5EyebrowLabel />

      {/* Main title */}
      <Part5TitleText />

      {/* Expanding horizontal rule */}
      <Part5HorizontalRule />
    </AbsoluteFill>
  );
};

export default Part5Compound01TitleCard;
