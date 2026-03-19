import React from "react";
import { Sequence } from "remotion";

import { Part1Economics01SectionTitleCard } from "../01_section_title_card";
import { Part1Economics02SockEconomicsChart } from "../02_sock_economics_chart";
import { Part1Economics03CodeCostTripleLine } from "../03_code_cost_triple_line";
import { Part1Economics04ResearchAnnotations } from "../04_research_annotations";
import { Part1Economics05ContextWindowShrink } from "../05_context_window_shrink";
import { Part1Economics06TwoByTwoGrid } from "../06_two_by_two_grid";
import { Part1Economics07SplitContextComparison } from "../07_split_context_comparison";
import { Part1Economics09CrossingLinesMoment } from "../09_crossing_lines_moment";
import { Part1Economics10DoubleMeterInsight } from "../10_double_meter_insight";

export const Part1EconomicsSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 17.621333;
  const durationSeconds = 455.44;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Part1Economics01SectionTitleCard />
      <Part1Economics02SockEconomicsChart />
      <Part1Economics03CodeCostTripleLine />
      <Part1Economics04ResearchAnnotations />
      <Part1Economics05ContextWindowShrink />
      <Part1Economics06TwoByTwoGrid />
      <Part1Economics07SplitContextComparison />
      <Part1Economics09CrossingLinesMoment />
      <Part1Economics10DoubleMeterInsight />
    </Sequence>
  );
};

export default Part1EconomicsSection;
