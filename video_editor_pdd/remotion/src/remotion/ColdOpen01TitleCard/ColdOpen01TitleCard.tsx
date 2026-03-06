import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile, Sequence } from "remotion";
import { ScrimOverlay } from "./ScrimOverlay";
import { TitleText } from "./TitleText";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";

export const defaultColdOpen01TitleCardProps = {};

export const ColdOpen01TitleCard: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/cold_open.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
        />
      </AbsoluteFill>

      {/* Scrim + title overlay — 120 frames (4s at 30fps) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ScrimOverlay />
        <TitleText />
      </Sequence>
    </AbsoluteFill>
  );
};

export default ColdOpen01TitleCard;
