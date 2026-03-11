import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 12;
  const durationSeconds = 12;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      <OffthreadVideo src={staticFile("veo_section.mp4")} style={{ width: "100%", height: "100%" }} />
    </Sequence>
  );
};

export default VeoSectionSection;
