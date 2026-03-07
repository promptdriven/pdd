import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame } from "remotion";
import { Part1RadialGlow } from "./Part1RadialGlow";
import { Part1EyebrowLabel } from "./Part1EyebrowLabel";
import { Part1TitleText } from "./Part1TitleText";
import { Part1HorizontalRule } from "./Part1HorizontalRule";
import {
  BG_COLOR,
  BG_FADE_IN_END,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
} from "./part1Constants";

export const defaultPart1Economics01TitleCardProps = {};

export const Part1Economics01TitleCard: React.FC = () => {
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
      {/* Radial glow behind text cluster */}
      <Part1RadialGlow opacity={bgOpacity} />

      {/* Eyebrow "PART 1" */}
      <Part1EyebrowLabel />

      {/* Main title */}
      <Part1TitleText />

      {/* Expanding horizontal rule */}
      <Part1HorizontalRule />
    </AbsoluteFill>
  );
};

export default Part1Economics01TitleCard;
