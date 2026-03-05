import React from "react";
import { Sequence } from "remotion";

import { ColdOpenSection as ColdOpenSectionBase } from "../ColdOpenSection";
import { ColdOpenTitleCard } from "../cold_open_title_card";

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 15.552;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <ColdOpenSectionBase />
      <Sequence from={Math.round(0.0 * fps)} durationInFrames={Math.ceil(5.0 * fps)}>
        <ColdOpenTitleCard />
      </Sequence>
    </Sequence>
  );
};

export default ColdOpenSection;
