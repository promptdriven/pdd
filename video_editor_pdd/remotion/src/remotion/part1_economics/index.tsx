import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 15.288;
  const durationSeconds = 382.176;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part1_economics/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part1_economics.mp4")} style={{ width: "100%", height: "100%" }} />
    </Sequence>
  );
};

export default Part1EconomicsSection;
