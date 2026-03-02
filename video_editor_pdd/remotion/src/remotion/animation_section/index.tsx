import React from "react";
import { Sequence, Audio, staticFile } from "remotion";

import { Animation01BlueCircle } from "../animation_01_blue_circle";
import { Animation02TransformSlide } from "../animation_02_transform_slide";

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 7.032;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("animation_section/narration.wav")} />
      <Animation01BlueCircle />
      <Animation02TransformSlide />
    </Sequence>
  );
};

export default AnimationSectionSection;
