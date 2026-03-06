import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { TricolorGlow } from "./TricolorGlow";
import { EyebrowLabel } from "./EyebrowLabel";
import { TitleText } from "./TitleText";
import { TricolorBar } from "./TricolorBar";
import {
  BG_FADE_IN_END,
  CARD_FADE_OUT_START,
  CARD_FADE_OUT_END,
} from "./constants";

export const defaultPart3Mold01TitleCardProps = {};

export const Part3Mold01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  const scrimOpacity = interpolate(
    frame,
    [0, BG_FADE_IN_END, CARD_FADE_OUT_START, CARD_FADE_OUT_END],
    [0, 0.7, 0.7, 0],
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
    <AbsoluteFill>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part3_mold.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
        />
      </AbsoluteFill>

      {/* Semi-transparent scrim overlay */}
      <AbsoluteFill
        style={{
          backgroundColor: `rgba(15, 23, 42, ${scrimOpacity})`,
        }}
      >
        {/* Tricolor radial glow */}
        <TricolorGlow opacity={scrimOpacity} />

        {/* Eyebrow "PART 3" in purple */}
        <EyebrowLabel />

        {/* Main title */}
        <TitleText />

        {/* Tricolor accent bar: green / gold / purple */}
        <TricolorBar />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3Mold01TitleCard;
