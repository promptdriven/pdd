import React from "react";
import { Sequence, Audio, staticFile } from "remotion";

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0.085333;
  const durationSeconds = 0.085333;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part1_economics/narration.wav")} />
      {/* Sub-compositions will be added here */}
    </Sequence>
  );
};

export default Part1EconomicsSection;
