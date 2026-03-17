import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { EyebrowLabel } from "./EyebrowLabel";
import { TitleText } from "./TitleText";
import { HorizontalRule } from "./HorizontalRule";
import { SubtitleText } from "./SubtitleText";
import { BG_COLOR, BG_FADE_START, BG_FADE_END } from "./constants";

export const defaultPart1Economics01SectionTitleCardProps = {};

export const Part1Economics01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  const bgOpacity = interpolate(frame, [BG_FADE_START, BG_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR, opacity: bgOpacity }}>
      {/* "PART 1" eyebrow label */}
      <EyebrowLabel />

      {/* Main title */}
      <TitleText />

      {/* Expanding horizontal rule */}
      <HorizontalRule />

      {/* Italic subtitle */}
      <SubtitleText />
    </AbsoluteFill>
  );
};

export default Part1Economics01SectionTitleCard;
