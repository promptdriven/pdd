import React from "react";
import { Sequence } from "remotion";

import { Part3MoldThreeParts as Part3MoldSectionBase } from "./Part3MoldThreeParts";

export const Part3MoldSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 593.850667;
  const durationSeconds = 280.728;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Part3MoldSectionBase />
    </Sequence>
  );
};

export default Part3MoldSection;
