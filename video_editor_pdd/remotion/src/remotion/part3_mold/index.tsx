import React from "react";
import { Sequence, OffthreadVideo, staticFile } from "remotion";

import { Part3MoldThreeParts as Part3MoldSectionBase } from "./Part3MoldThreeParts";

export const Part3MoldSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 593.850667;
  const durationSeconds = 280.728;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <OffthreadVideo src={staticFile("veo/part3_mold.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part3MoldSectionBase />
    </Sequence>
  );
};

export default Part3MoldSection;
