import React from "react";
import { Sequence, Audio, staticFile } from "remotion";

export const Part4PrecisionTradeoffSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 572.620541;
  const durationSeconds = 112.000667;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part4_precision_tradeoff/narration.wav")} />
      {/* Sub-compositions will be added here */}
    </Sequence>
  );
};

export default Part4PrecisionTradeoffSection;
