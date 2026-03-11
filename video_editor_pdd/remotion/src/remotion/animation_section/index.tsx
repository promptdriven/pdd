import React from "react";
import { Sequence, Audio, staticFile } from "remotion";

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 12;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("animation_section/narration.wav")} />
      {/* Sub-compositions will be added here */}
    </Sequence>
  );
};

export default AnimationSectionSection;
