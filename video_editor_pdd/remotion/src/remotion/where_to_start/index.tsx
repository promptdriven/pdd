import React from "react";
import { Sequence, Audio, staticFile } from "remotion";

export const WhereToStartSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 800.0708330000001;
  const durationSeconds = 32.569083;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("where_to_start/narration.wav")} />
      {/* Sub-compositions will be added here */}
    </Sequence>
  );
};

export default WhereToStartSection;
