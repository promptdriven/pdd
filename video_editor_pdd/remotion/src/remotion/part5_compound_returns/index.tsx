import React from "react";
import { Sequence, Audio, staticFile } from "remotion";

export const Part5CompoundReturnsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 684.621208;
  const durationSeconds = 115.321625;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part5_compound_returns/narration.wav")} />
      {/* Sub-compositions will be added here */}
    </Sequence>
  );
};

export default Part5CompoundReturnsSection;
