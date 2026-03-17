import React from "react";
import { Sequence } from "remotion";

import { ClosingSection as ClosingSectionBase } from "./ClosingSection";

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 832.6399160000001;
  const durationSeconds = 20.903208;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <ClosingSectionBase />
    </Sequence>
  );
};

export default ClosingSection;
