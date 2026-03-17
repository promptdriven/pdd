import React from "react";
import { Sequence } from "remotion";

import { Part2ParadigmShift01SectionTitleCard } from "../01_section_title_card";
import { Part2ParadigmShift04DefectFixTheMold } from "../04_defect_fix_the_mold";
import { Part2ParadigmShift05ValueMigrationSplit } from "../05_value_migration_split";
import { Part2ParadigmShift07VerilogSynthesisTriple } from "../07_verilog_synthesis_triple";
import { Part2ParadigmShift08SynopsysPddEquivalence } from "../08_synopsys_pdd_equivalence";
import { Part2ParadigmShift09AbstractionStaircase } from "../09_abstraction_staircase";
import { Part2ParadigmShift10NetlistZoomUnreviewable } from "../10_netlist_zoom_unreviewable";
import { Part2ParadigmShift11PromptReplacesReview } from "../11_prompt_replaces_review";

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0.362666;
  const durationSeconds = 228.053292;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Part2ParadigmShift01SectionTitleCard />
      <Part2ParadigmShift04DefectFixTheMold />
      <Part2ParadigmShift05ValueMigrationSplit />
      <Part2ParadigmShift07VerilogSynthesisTriple />
      <Part2ParadigmShift08SynopsysPddEquivalence />
      <Part2ParadigmShift09AbstractionStaircase />
      <Part2ParadigmShift10NetlistZoomUnreviewable />
      <Part2ParadigmShift11PromptReplacesReview />
    </Sequence>
  );
};

export default Part2ParadigmShiftSection;
