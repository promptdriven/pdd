import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part4Precision01TitleCard } from "../Part4Precision01TitleCard";
import { Part4Precision03PrecisionCostUcurve } from "../Part4Precision03PrecisionCostUcurve";
import { Part4Precision04StatCalloutPromptCompression } from "../Part4Precision04StatCalloutPromptCompression";
import { Part4Precision05SplitPromptDetailVsTests } from "../Part4Precision05SplitPromptDetailVsTests";
import { Part4Precision07SpectrumSlider } from "../Part4Precision07SpectrumSlider";
import { Part4Precision10SubtitleTrack } from "../Part4Precision10SubtitleTrack";

export const Part4PrecisionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 874.578667;
  const durationSeconds = 96.912;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part4_precision/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part4_precision.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part4Precision01TitleCard />
      <Part4Precision03PrecisionCostUcurve />
      <Part4Precision04StatCalloutPromptCompression />
      <Part4Precision05SplitPromptDetailVsTests />
      <Part4Precision07SpectrumSlider />
      <Part4Precision10SubtitleTrack />
    </Sequence>
  );
};

export default Part4PrecisionSection;
