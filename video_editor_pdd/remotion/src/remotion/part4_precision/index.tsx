import React from "react";
import { Sequence, OffthreadVideo, staticFile } from "remotion";

import { Part4PrecisionTradeoff as Part4PrecisionSectionBase } from "./Part4PrecisionTradeoff";

export const Part4PrecisionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 874.578667;
  const durationSeconds = 96.912;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <OffthreadVideo src={staticFile("veo/part4_precision.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part4PrecisionSectionBase />
    </Sequence>
  );
};

export default Part4PrecisionSection;
