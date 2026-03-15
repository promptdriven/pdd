import React from "react";
import { Sequence } from "remotion";

import { Part2ParadigmShiftMain } from "../part2_paradigm_shift_main";

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 0;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Part2ParadigmShiftMain />
    </Sequence>
  );
};

export default Part2ParadigmShiftSection;
