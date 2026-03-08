import React from "react";
import { Sequence } from "remotion";

import { Part1Economics as Part1EconomicsSectionBase } from "./Part1Economics";

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 15.744;
  const durationSeconds = 382.314667;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Part1EconomicsSectionBase />
    </Sequence>
  );
};

export default Part1EconomicsSection;
