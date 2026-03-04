import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 397.464;
  const durationSeconds = 195.792;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part2_paradigm_shift/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part2_paradigm_shift.mp4")} style={{ width: "100%", height: "100%" }} />
    </Sequence>
  );
};

export default Part2ParadigmShiftSection;
