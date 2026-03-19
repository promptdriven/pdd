import React from "react";
import { Sequence } from "remotion";

import { Part3MoldThreeParts01SectionTitleCard } from "../01_section_title_card";
import { Part3MoldThreeParts02MoldCrossSection } from "../02_mold_cross_section";
import { Part3MoldThreeParts03TestWallsConstraint } from "../03_test_walls_constraint";
import { Part3MoldThreeParts04ResearchAnnotationsAiQuality } from "../04_research_annotations_ai_quality";
import { Part3MoldThreeParts06RatchetSplitComparison } from "../06_ratchet_split_comparison";
import { Part3MoldThreeParts07FiveGenerationsZ3 } from "../07_five_generations_z3";
import { Part3MoldThreeParts08PromptCapitalSpecification } from "../08_prompt_capital_specification";
import { Part3MoldThreeParts10ThreeComponentsTable } from "../10_three_components_table";

export const Part3MoldThreePartsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 246.165333;
  const durationSeconds = 344.16;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Part3MoldThreeParts01SectionTitleCard />
      <Part3MoldThreeParts02MoldCrossSection />
      <Part3MoldThreeParts03TestWallsConstraint />
      <Part3MoldThreeParts04ResearchAnnotationsAiQuality />
      <Part3MoldThreeParts06RatchetSplitComparison />
      <Part3MoldThreeParts07FiveGenerationsZ3 />
      <Part3MoldThreeParts08PromptCapitalSpecification />
      <Part3MoldThreeParts10ThreeComponentsTable />
    </Sequence>
  );
};

export default Part3MoldThreePartsSection;
