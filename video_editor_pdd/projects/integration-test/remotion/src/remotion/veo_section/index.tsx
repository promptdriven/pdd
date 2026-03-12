import React from "react";
import { Sequence } from "remotion";

import { VeoSection01TitleCard } from "../veo_section_01_title_card";
import { VeoSection03WaveDataOverlay } from "../03_wave_data_overlay";
import { VeoSection05SplitNatureComparison } from "../05_split_nature_comparison";
import { VeoSection06VeoPipelineInfographic } from "../06_veo_pipeline_infographic";

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 7.32;
  const durationSeconds = 7.344;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <VeoSection01TitleCard />
      <VeoSection03WaveDataOverlay />
      <VeoSection05SplitNatureComparison />
      <VeoSection06VeoPipelineInfographic />
    </Sequence>
  );
};

export default VeoSectionSection;
