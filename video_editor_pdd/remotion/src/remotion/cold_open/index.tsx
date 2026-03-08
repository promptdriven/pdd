import React from "react";
import { Sequence } from "remotion";

import { ColdOpenSection as ColdOpenSectionBase } from "./ColdOpenSection";

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 15.744;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <ColdOpenSectionBase />
    </Sequence>
  );
};

export default ColdOpenSection;
