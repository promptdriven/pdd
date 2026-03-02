import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { VeoSectionMain } from "../veo_section_main";

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 7.032;
  const durationSeconds = 7.416;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/veo_section.mp4")} style={{ width: "100%", height: "100%" }} />
      <VeoSectionMain />
    </Sequence>
  );
};

export default VeoSectionSection;
