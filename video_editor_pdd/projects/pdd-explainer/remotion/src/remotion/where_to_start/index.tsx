import React from "react";
import { Sequence } from "remotion";

import { WhereToStart01SectionTitleCard } from "../01_section_title_card";
import { WhereToStart02LegacyCodebaseReveal } from "../02_legacy_codebase_reveal";
import { WhereToStart03ModuleHighlightUpdate } from "../03_module_highlight_update";
import { WhereToStart04SourceOfTruthShift } from "../04_source_of_truth_shift";
import { WhereToStart05RegenerateCompareLoop } from "../05_regenerate_compare_loop";
import { WhereToStart06SpreadingGlowMigration } from "../06_spreading_glow_migration";
import { WhereToStart07NoBigBangCallout } from "../07_no_big_bang_callout";

export const WhereToStartSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 800.0708330000001;
  const durationSeconds = 32.569083;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <WhereToStart01SectionTitleCard />
      <WhereToStart02LegacyCodebaseReveal />
      <WhereToStart03ModuleHighlightUpdate />
      <WhereToStart04SourceOfTruthShift />
      <WhereToStart05RegenerateCompareLoop />
      <WhereToStart06SpreadingGlowMigration />
      <WhereToStart07NoBigBangCallout />
    </Sequence>
  );
};

export default WhereToStartSection;
