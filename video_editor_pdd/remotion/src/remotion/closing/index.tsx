import React from "react";
import { Sequence, OffthreadVideo, staticFile } from "remotion";

import { ClosingSection as ClosingSectionBase } from "./ClosingSection";

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 1069.914667;
  const durationSeconds = 21.072;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <OffthreadVideo src={staticFile("veo/closing.mp4")} style={{ width: "100%", height: "100%" }} />
      <ClosingSectionBase />
    </Sequence>
  );
};

export default ClosingSection;
