import React from "react";
import { Sequence, OffthreadVideo, staticFile } from "remotion";

import { Part5CompoundReturns as Part5CompoundSectionBase } from "./Part5CompoundReturns";

export const Part5CompoundSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 971.490667;
  const durationSeconds = 98.424;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <OffthreadVideo src={staticFile("veo/part5_compound.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part5CompoundSectionBase />
    </Sequence>
  );
};

export default Part5CompoundSection;
