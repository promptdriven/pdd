import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part2ParadigmShiftMain } from "../part2_paradigm_shift_main";

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 397.728;
  const durationSeconds = 195.792;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part2_paradigm_shift/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part2_paradigm_shift.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part2ParadigmShiftMain />
    </Sequence>
  );
};

export default Part2ParadigmShiftSection;
