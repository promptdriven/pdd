import React from "react";
import { Sequence } from "remotion";

import { ClosingSection as ClosingSectionBase } from "./ClosingSection";

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 1069.914667;
  const durationSeconds = 21.072;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <ClosingSectionBase />
    </Sequence>
  );
};

export default ClosingSection;
