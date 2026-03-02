import React from "react";
import { Sequence, Audio, staticFile } from "remotion";

import { AnimationSectionMain } from "../animation_section_main";

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 7.032;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("animation_section/narration.wav")} />
      <AnimationSectionMain />
    </Sequence>
  );
};

export default AnimationSectionSection;
