import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { TitleCard } from "../title_card";

export const Part5CompoundSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 970.896;
  const durationSeconds = 98.424;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part5_compound/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part5_compound.mp4")} style={{ width: "100%", height: "100%" }} />
      <TitleCard />
    </Sequence>
  );
};

export default Part5CompoundSection;
