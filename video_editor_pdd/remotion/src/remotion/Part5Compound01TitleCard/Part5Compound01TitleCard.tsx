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

export const defaultPart5Compound01TitleCardProps = {};

export const Part5Compound01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  const bgOpacity = interpolate(
    frame,
    [0, BG_FADE_IN_END, CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing:
        frame <= BG_FADE_IN_END
          ? Easing.out(Easing.cubic)
          : Easing.in(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR, opacity: bgOpacity }}>
      {/* Radial glow behind text */}
      <RadialGlow opacity={bgOpacity} />

      {/* Eyebrow "PART 5" */}
      <EyebrowLabel />

      {/* Main title */}
      <TitleText />

      {/* Expanding horizontal rule */}
      <HorizontalRule />
    </AbsoluteFill>
  );
};

export default Part5Compound01TitleCard;
