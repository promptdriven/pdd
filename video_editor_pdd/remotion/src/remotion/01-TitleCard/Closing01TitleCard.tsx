import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { ClosingRadialGlow } from "./ClosingRadialGlow";
import { ClosingEyebrowLabel } from "./ClosingEyebrowLabel";
import { ClosingTitleText } from "./ClosingTitleText";
import { ClosingHorizontalRule } from "./ClosingHorizontalRule";
import {
  BG_COLOR,
  BG_FADE_IN_END,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
} from "./closingConstants";

export const defaultClosing01TitleCardProps = {};

export const Closing01TitleCard: React.FC = () => {
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
      {/* Dual amber-blue radial glow */}
      <ClosingRadialGlow opacity={bgOpacity} />

      {/* Eyebrow "PART 6" */}
      <ClosingEyebrowLabel />

      {/* Main title */}
      <ClosingTitleText />

      {/* Expanding horizontal rule */}
      <ClosingHorizontalRule />
    </AbsoluteFill>
  );
};

export default Closing01TitleCard;
