import React from "react";
import { Sequence } from "remotion";

import { Part2ParadigmShift as Part2ParadigmShiftSectionBase } from "./Part2ParadigmShift";

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 398.058667;
  const durationSeconds = 195.792;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Part2ParadigmShiftSectionBase />
    </Sequence>
  );
};

export default Part2ParadigmShiftSection;
