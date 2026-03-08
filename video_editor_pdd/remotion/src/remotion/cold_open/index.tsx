import React from "react";
import { Sequence, OffthreadVideo, staticFile } from "remotion";

import { ColdOpenSection as ColdOpenSectionBase } from "./ColdOpenSection";

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 15.744;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <OffthreadVideo src={staticFile("veo/cold_open.mp4")} style={{ width: "100%", height: "100%" }} />
      <ColdOpenSectionBase />
    </Sequence>
  );
};

export default ColdOpenSection;
