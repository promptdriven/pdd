import React from "react";
import { Sequence } from "remotion";

import { VeoSection01TitleCard } from "../veo_section_01_title_card";
import { VeoSection04WaveDataOverlay } from "../04_wave_data_overlay";
import { VeoSection05SplitNatureComparison } from "../05_split_nature_comparison";
import { VeoSection06VeoPipelineInfographic } from "../06_veo_pipeline_infographic";
import { VeoSection07NarrationOverlayIntro } from "../07_narration_overlay_intro";
import { VeoSection08SectionEndCard } from "../08_section_end_card";

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 7.722667;
  const durationSeconds = 7.744;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <VeoSection01TitleCard />
      <VeoSection04WaveDataOverlay />
      <VeoSection05SplitNatureComparison />
      <VeoSection06VeoPipelineInfographic />
      <VeoSection07NarrationOverlayIntro />
      <VeoSection08SectionEndCard />
    </Sequence>
  );
};

export default VeoSectionSection;
