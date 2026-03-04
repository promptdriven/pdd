import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { TitleCard } from "../title_card";

export const Part3MoldSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 593.256;
  const durationSeconds = 280.728;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part3_mold/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part3_mold.mp4")} style={{ width: "100%", height: "100%" }} />
      <TitleCard />
    </Sequence>
  );
};

export default Part3MoldSection;
