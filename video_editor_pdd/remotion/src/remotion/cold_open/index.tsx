import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { TitleCard } from "../title_card";

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 15.288;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("cold_open/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/cold_open.mp4")} style={{ width: "100%", height: "100%" }} />
      <TitleCard />
    </Sequence>
  );
};

export default ColdOpenSection;
