import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part4PrecisionSplitPromptDetailVsTests } from "../part4_precision_split_prompt_detail_vs_tests";
import { Part4PrecisionStatCalloutPromptCompression } from "../part4_precision_stat_callout_prompt_compression";
import { Part4PrecisionTitleCard } from "../part4_precision_title_card";

export const Part4PrecisionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 874.4506670000001;
  const durationSeconds = 96.912;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part4_precision/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part4_precision.mp4")} style={{ width: "100%", height: "100%" }} />
      <Sequence from={Math.round(25.38 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part4PrecisionSplitPromptDetailVsTests />
      </Sequence>
      <Sequence from={Math.round(26.32 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part4PrecisionStatCalloutPromptCompression />
      </Sequence>
      <Sequence from={Math.round(0 * fps)} durationInFrames={Math.ceil(5 * fps)}>
        <Part4PrecisionTitleCard />
      </Sequence>
    </Sequence>
  );
};

export default Part4PrecisionSection;
