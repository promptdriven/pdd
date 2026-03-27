import React from "react";
import { Sequence, Audio, staticFile } from "remotion";

export const Part3MoldPartsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 730.651292;
  const durationSeconds = 345.88;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part3_mold_parts/narration.wav")} />
      {/* Sub-compositions will be added here */}
    </Sequence>
  );
};

export default Part3MoldPartsSection;
