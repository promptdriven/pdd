import React from "react";
import { Sequence } from "remotion";

import { ColdOpenSection as ColdOpenSectionBase } from "./ColdOpenSection";

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 0.149333;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <ColdOpenSectionBase />
    </Sequence>
  );
};

export default ColdOpenSection;
