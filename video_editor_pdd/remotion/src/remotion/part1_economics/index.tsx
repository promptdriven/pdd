import React from "react";
import { Sequence, OffthreadVideo, staticFile } from "remotion";

import { Part1Economics as Part1EconomicsSectionBase } from "./Part1Economics";

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 15.744;
  const durationSeconds = 382.314667;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <OffthreadVideo src={staticFile("veo/part1_economics.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part1EconomicsSectionBase />
    </Sequence>
  );
};

export default Part1EconomicsSection;
