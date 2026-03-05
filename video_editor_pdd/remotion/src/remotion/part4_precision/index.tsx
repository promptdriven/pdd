import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part4PrecisionSplitPromptDetailVsTests } from "../part4_precision_split_prompt_detail_vs_tests";
import { Part4PrecisionStatCalloutPromptCompression } from "../part4_precision_stat_callout_prompt_compression";
import { Part4PrecisionTitleCard } from "../part4_precision_title_card";

export const Part4PrecisionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 874.248;
  const durationSeconds = 96.912;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part4_precision/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part4_precision.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part4PrecisionSplitPromptDetailVsTests />
      <Part4PrecisionStatCalloutPromptCompression />
      <Part4PrecisionTitleCard />
    </Sequence>
  );
};

export default Part4PrecisionSection;
