import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { RadialGlow } from "./RadialGlow";
import { EyebrowLabel } from "./EyebrowLabel";
import { TitleText } from "./TitleText";
import { HorizontalRule } from "./HorizontalRule";
import {
  BG_COLOR,
  BG_FADE_IN_END,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
} from "./constants";

export const defaultPart2ParadigmShift01TitleCardProps = {};

export const Part2ParadigmShift01TitleCard: React.FC = () => {
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
      {/* Warm radial glow behind text */}
      <RadialGlow opacity={bgOpacity} />

      {/* Eyebrow "PART 2" in molten orange */}
      <EyebrowLabel />

      {/* Main title */}
      <TitleText />

      {/* Expanding horizontal rule with orange→blue gradient */}
      <HorizontalRule />
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift01TitleCard;
