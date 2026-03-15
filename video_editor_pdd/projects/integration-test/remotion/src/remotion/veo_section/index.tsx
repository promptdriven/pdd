import React from "react";
import { Sequence } from "remotion";

import { VeoSection01TitleCard } from "../veo_section_01_title_card";
import { VeoSection03WaveDataOverlay } from "../03_wave_data_overlay";
import { VeoSection04SplitNatureComparison } from "../04_split_nature_comparison";
import { VeoSection05VeoPipelineInfographic } from "../05_veo_pipeline_infographic";
import { VeoSection07NarrationOverlayIntro } from "../07_narration_overlay_intro";
import { VeoSection08SectionEndCard } from "../08_section_end_card";

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 7.914667;
  const durationSeconds = 7.957333;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <VeoSection01TitleCard />
      <VeoSection03WaveDataOverlay />
      <VeoSection04SplitNatureComparison />
      <VeoSection05VeoPipelineInfographic />
      <VeoSection07NarrationOverlayIntro />
      <VeoSection08SectionEndCard />
    </Sequence>
  );
};

export default VeoSectionSection;
