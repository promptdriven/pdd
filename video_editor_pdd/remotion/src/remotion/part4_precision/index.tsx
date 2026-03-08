import React from "react";
import { Sequence } from "remotion";

import { Part4PrecisionTradeoff as Part4PrecisionSectionBase } from "./Part4PrecisionTradeoff";

export const Part4PrecisionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 874.578667;
  const durationSeconds = 96.912;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Part4PrecisionSectionBase />
    </Sequence>
  );
};

export default Part4PrecisionSection;
