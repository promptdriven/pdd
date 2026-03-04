import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { TitleCard } from "../title_card";

export const Part4PrecisionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 873.9839999999999;
  const durationSeconds = 96.912;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part4_precision/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part4_precision.mp4")} style={{ width: "100%", height: "100%" }} />
      <TitleCard />
    </Sequence>
  );
};

export default Part4PrecisionSection;
