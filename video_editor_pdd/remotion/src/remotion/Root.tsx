import React from "react";
import { Composition } from "remotion";
import { VisualMediaProvider, VisualContractProvider } from "./_shared/visual-runtime";
import "./_shared/load-inter-font";

import { ColdOpenSection } from "./cold_open";
import { Part1EconomicsSection } from "./part1_economics";
import { Part2ParadigmShiftSection } from "./part2_paradigm_shift";
import { Part3MoldThreePartsSection } from "./part3_mold_three_parts";
import { Part4PrecisionTradeoffSection } from "./part4_precision_tradeoff";
import { Part5CompoundReturnsSection } from "./part5_compound_returns";
import { WhereToStartSection } from "./where_to_start";
import { ClosingSection } from "./closing";
import { ColdOpen01SplitScreenHook } from "./ColdOpen01SplitScreenHook";
import { ColdOpen02ZoomOutAccumulated } from "./ColdOpen02ZoomOutAccumulated";
import { ColdOpen05CodeBlink } from "./ColdOpen05CodeBlink";
import { ColdOpen06StillPatchingBeat } from "./ColdOpen06StillPatchingBeat";
import { ColdOpen07PddTitleCard } from "./ColdOpen07PddTitleCard";
import { Part1Economics01SectionTitleCard } from "./Part1Economics01SectionTitleCard";
import { Part1Economics02SockEconomicsChart } from "./Part1Economics02SockEconomicsChart";
import { Part1Economics03CodeCostTripleLine } from "./Part1Economics03CodeCostTripleLine";
import { Part1Economics04ResearchAnnotations } from "./Part1Economics04ResearchAnnotations";
import { Part1Economics05ContextWindowShrink } from "./Part1Economics05ContextWindowShrink";
import { Part1Economics06TwoByTwoGrid } from "./Part1Economics06TwoByTwoGrid";
import { Part1Economics07SplitContextComparison } from "./Part1Economics07SplitContextComparison";
import { Part1Economics09CrossingLinesMoment } from "./Part1Economics09CrossingLinesMoment";
import { Part1Economics10DoubleMeterInsight } from "./Part1Economics10DoubleMeterInsight";
import { Part2ParadigmShiftMain } from "./part2_paradigm_shift_main";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "cold_open:05_code_blink": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "cold_open:06_still_patching_beat": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "cold_open:07_pdd_title_card": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "part1_economics:09_crossing_lines_moment": { defaultSrc: "veo/developer_patching_montage.mp4", backgroundSrc: "veo/developer_patching_montage.mp4", outputSrc: "veo/developer_patching_montage.mp4", baseSrc: "veo/developer_patching_montage.mp4" },
  "part1_economics:10_double_meter_insight": { defaultSrc: "veo/developer_patching_montage.mp4", backgroundSrc: "veo/developer_patching_montage.mp4", outputSrc: "veo/developer_patching_montage.mp4", baseSrc: "veo/developer_patching_montage.mp4" },
  "part2_paradigm_shift:part2_paradigm_shift_main": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "cold_open:01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
  "cold_open:02_zoom_out_accumulated": {"specBaseName": "02_zoom_out_accumulated", "dataPoints": null, "overlayConfig": null},
  "cold_open:05_code_blink": {"specBaseName": "05_code_blink", "dataPoints": null, "overlayConfig": null},
  "cold_open:06_still_patching_beat": {"specBaseName": "06_still_patching_beat", "dataPoints": null, "overlayConfig": null},
  "cold_open:07_pdd_title_card": {"specBaseName": "07_pdd_title_card", "dataPoints": null, "overlayConfig": null},
  "part1_economics:01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "part1_economics:02_sock_economics_chart": {"specBaseName": "02_sock_economics_chart", "dataPoints": null, "overlayConfig": null},
  "part1_economics:03_code_cost_triple_line": {"specBaseName": "03_code_cost_triple_line", "dataPoints": null, "overlayConfig": null},
  "part1_economics:04_research_annotations": {"specBaseName": "04_research_annotations", "dataPoints": null, "overlayConfig": null},
  "part1_economics:05_context_window_shrink": {"specBaseName": "05_context_window_shrink", "dataPoints": null, "overlayConfig": null},
  "part1_economics:06_two_by_two_grid": {"specBaseName": "06_two_by_two_grid", "dataPoints": null, "overlayConfig": null},
  "part1_economics:07_split_context_comparison": {"specBaseName": "07_split_context_comparison", "dataPoints": null, "overlayConfig": null},
  "part1_economics:09_crossing_lines_moment": {"specBaseName": "09_crossing_lines_moment", "dataPoints": null, "overlayConfig": null},
  "part1_economics:10_double_meter_insight": {"specBaseName": "10_double_meter_insight", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift:part2_paradigm_shift_main": {"specBaseName": "main", "dataPoints": null, "overlayConfig": null},
};

const ColdOpen01SplitScreenHookPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:01_split_screen_hook"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:01_split_screen_hook"] ?? null}>
      <ColdOpen01SplitScreenHook />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen02ZoomOutAccumulatedPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:02_zoom_out_accumulated"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:02_zoom_out_accumulated"] ?? null}>
      <ColdOpen02ZoomOutAccumulated />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen05CodeBlinkPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:05_code_blink"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:05_code_blink"] ?? null}>
      <ColdOpen05CodeBlink />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen06StillPatchingBeatPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:06_still_patching_beat"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:06_still_patching_beat"] ?? null}>
      <ColdOpen06StillPatchingBeat />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const ColdOpen07PddTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["cold_open:07_pdd_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["cold_open:07_pdd_title_card"] ?? null}>
      <ColdOpen07PddTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics01SectionTitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:01_section_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:01_section_title_card"] ?? null}>
      <Part1Economics01SectionTitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics02SockEconomicsChartPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:02_sock_economics_chart"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:02_sock_economics_chart"] ?? null}>
      <Part1Economics02SockEconomicsChart />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics03CodeCostTripleLinePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:03_code_cost_triple_line"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:03_code_cost_triple_line"] ?? null}>
      <Part1Economics03CodeCostTripleLine />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics04ResearchAnnotationsPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:04_research_annotations"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:04_research_annotations"] ?? null}>
      <Part1Economics04ResearchAnnotations />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics05ContextWindowShrinkPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:05_context_window_shrink"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:05_context_window_shrink"] ?? null}>
      <Part1Economics05ContextWindowShrink />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics06TwoByTwoGridPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:06_two_by_two_grid"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:06_two_by_two_grid"] ?? null}>
      <Part1Economics06TwoByTwoGrid />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics07SplitContextComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:07_split_context_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:07_split_context_comparison"] ?? null}>
      <Part1Economics07SplitContextComparison />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics09CrossingLinesMomentPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:09_crossing_lines_moment"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:09_crossing_lines_moment"] ?? null}>
      <Part1Economics09CrossingLinesMoment />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part1Economics10DoubleMeterInsightPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part1_economics:10_double_meter_insight"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part1_economics:10_double_meter_insight"] ?? null}>
      <Part1Economics10DoubleMeterInsight />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const Part2ParadigmShiftMainPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["part2_paradigm_shift:part2_paradigm_shift_main"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["part2_paradigm_shift:part2_paradigm_shift_main"] ?? null}>
      <Part2ParadigmShiftMain />
    </VisualMediaProvider>
  </VisualContractProvider>
);

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="ColdOpenSection"
        component={ColdOpenSection}
        durationInFrames={5}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part1EconomicsSection"
        component={Part1EconomicsSection}
        durationInFrames={5}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part2ParadigmShiftSection"
        component={Part2ParadigmShiftSection}
        durationInFrames={6842}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part3MoldThreePartsSection"
        component={Part3MoldThreePartsSection}
        durationInFrames={10332}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part4PrecisionTradeoffSection"
        component={Part4PrecisionTradeoffSection}
        durationInFrames={3361}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part5CompoundReturnsSection"
        component={Part5CompoundReturnsSection}
        durationInFrames={3460}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="WhereToStartSection"
        component={WhereToStartSection}
        durationInFrames={978}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="ClosingSection"
        component={ClosingSection}
        durationInFrames={628}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open01-split-screen-hook"
        component={ColdOpen01SplitScreenHookPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open02-zoom-out-accumulated"
        component={ColdOpen02ZoomOutAccumulatedPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open05-code-blink"
        component={ColdOpen05CodeBlinkPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open06-still-patching-beat"
        component={ColdOpen06StillPatchingBeatPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open07-pdd-title-card"
        component={ColdOpen07PddTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics01-section-title-card"
        component={Part1Economics01SectionTitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics02-sock-economics-chart"
        component={Part1Economics02SockEconomicsChartPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics03-code-cost-triple-line"
        component={Part1Economics03CodeCostTripleLinePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics04-research-annotations"
        component={Part1Economics04ResearchAnnotationsPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics05-context-window-shrink"
        component={Part1Economics05ContextWindowShrinkPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics06-two-by-two-grid"
        component={Part1Economics06TwoByTwoGridPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics07-split-context-comparison"
        component={Part1Economics07SplitContextComparisonPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics09-crossing-lines-moment"
        component={Part1Economics09CrossingLinesMomentPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics10-double-meter-insight"
        component={Part1Economics10DoubleMeterInsightPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift-main"
        component={Part2ParadigmShiftMainPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
