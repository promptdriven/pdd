import React from "react";
import { Composition } from "remotion";

import { ColdOpenSection } from "./cold_open";
import { Part1EconomicsSection } from "./part1_economics";
import { Part2ParadigmShiftSection } from "./part2_paradigm_shift";
import { Part3MoldSection } from "./part3_mold";
import { Part4PrecisionSection } from "./part4_precision";
import { Part5CompoundSection } from "./part5_compound";
import { ClosingSection } from "./closing";
import { ColdOpenTitleCard } from "./cold_open_title_card";
import { ColdOpen01TitleCard } from "./ColdOpen01TitleCard";
import { Part1EconomicsSplitPerceptionVsReality } from "./part1_economics_split_perception_vs_reality";
import { Part1EconomicsStatCalloutGitclear } from "./part1_economics_stat_callout_gitclear";
import { Part1EconomicsStatCalloutGithub } from "./part1_economics_stat_callout_github";
import { Part1EconomicsStatCalloutUplevel } from "./part1_economics_stat_callout_uplevel";
import { Part2ParadigmShiftMain } from "./part2_paradigm_shift_main";
import { Part3MoldSplitPromptVsCode } from "./part3_mold_split_prompt_vs_code";
import { Part3MoldStatCalloutCoderabbit } from "./part3_mold_stat_callout_coderabbit";
import { Part3MoldStatCalloutDora } from "./part3_mold_stat_callout_dora";
import { Part3MoldStatCalloutNlContext } from "./part3_mold_stat_callout_nl_context";
import { Part3MoldTitleCard } from "./part3_mold_title_card";
import { Part4Precision05SplitPromptDetailVsTests } from "./Part4Precision05SplitPromptDetailVsTests";
import { Part4PrecisionStatCalloutPromptCompression } from "./part4_precision_stat_callout_prompt_compression";
import { Part4PrecisionTitleCard } from "./part4_precision_title_card";
import { Part5CompoundSplitPatchingVsPdd } from "./part5_compound_split_patching_vs_pdd";
import { Part5CompoundStatCalloutCisq } from "./part5_compound_stat_callout_cisq";
import { Part5CompoundStatCalloutMaintenance } from "./part5_compound_stat_callout_maintenance";
import { Part5CompoundTitleCard } from "./part5_compound_title_card";
import { ClosingSplitDarningVsMolding } from "./closing_split_darning_vs_molding";
import { ClosingStatCalloutRoi } from "./closing_stat_callout_roi";
import { ClosingTitleCard } from "./closing_title_card";
import { ColdOpen08ClosingQuestionCard } from "./ColdOpen08ClosingQuestionCard";
import { Part1Economics04StatCalloutGithub } from "./Part1Economics04StatCalloutGithub";
import { Part1Economics06StatCalloutUplevel } from "./Part1Economics06StatCalloutUplevel";
import { Part1Economics07StatCalloutGitclear } from "./Part1Economics07StatCalloutGitclear";
import { Part1Economics09ContextDegradationChart } from "./Part1Economics09ContextDegradationChart";
import { Part1Economics10SplitPerceptionReality } from "./Part1Economics10SplitPerceptionReality";
import { Part1Economics12RegenerationInfographic } from "./Part1Economics12RegenerationInfographic";
import { Part1Economics13CrossoverZoom } from "./Part1Economics13CrossoverZoom";
import { Part2ParadigmShift07HdlTimeline } from "./Part2ParadigmShift07HdlTimeline";
import { Part2ParadigmShift08SplitManualVsSpecification } from "./Part2ParadigmShift08SplitManualVsSpecification";
import { Part2ParadigmShift10PromptMoldVisualization } from "./Part2ParadigmShift10PromptMoldVisualization";
import { Part3Mold04StatCalloutDora } from "./Part3Mold04StatCalloutDora";
import { Part3Mold12ThreePillarsDiagram } from "./Part3Mold12ThreePillarsDiagram";
import { Part3Mold13SubtitleTrack } from "./Part3Mold13SubtitleTrack";
import { Part4Precision01TitleCard } from "./Part4Precision01TitleCard";
import { Part4Precision07SpectrumSlider } from "./Part4Precision07SpectrumSlider";
import { Part5Compound05StatCalloutCisq } from "./Part5Compound05StatCalloutCisq";
import { Part5Compound10QuoteCard } from "./Part5Compound10QuoteCard";
import { Closing07CtaCard } from "./Closing07CtaCard";

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="ColdOpenSection"
        component={ColdOpenSection}
        durationInFrames={471}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part1Economics"
        component={Part1EconomicsSection}
        durationInFrames={11466}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part2ParadigmShift"
        component={Part2ParadigmShiftSection}
        durationInFrames={5874}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part3MoldThreeParts"
        component={Part3MoldSection}
        durationInFrames={8422}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part4PrecisionTradeoff"
        component={Part4PrecisionSection}
        durationInFrames={2908}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part5CompoundReturns"
        component={Part5CompoundSection}
        durationInFrames={2953}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="ClosingSection"
        component={ClosingSection}
        durationInFrames={633}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open-01-title-card"
        component={ColdOpen01TitleCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open-title-card"
        component={ColdOpenTitleCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-split-perception-vs-reality"
        component={Part1EconomicsSplitPerceptionVsReality}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-stat-callout-gitclear"
        component={Part1EconomicsStatCalloutGitclear}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-stat-callout-github"
        component={Part1EconomicsStatCalloutGithub}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-stat-callout-uplevel"
        component={Part1EconomicsStatCalloutUplevel}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift-main"
        component={Part2ParadigmShiftMain}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-split-prompt-vs-code"
        component={Part3MoldSplitPromptVsCode}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-stat-callout-coderabbit"
        component={Part3MoldStatCalloutCoderabbit}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-stat-callout-dora"
        component={Part3MoldStatCalloutDora}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-stat-callout-nl-context"
        component={Part3MoldStatCalloutNlContext}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-title-card"
        component={Part3MoldTitleCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-05-split-prompt-detail-vs-tests"
        component={Part4Precision05SplitPromptDetailVsTests}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-stat-callout-prompt-compression"
        component={Part4PrecisionStatCalloutPromptCompression}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-title-card"
        component={Part4PrecisionTitleCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-split-patching-vs-pdd"
        component={Part5CompoundSplitPatchingVsPdd}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-stat-callout-cisq"
        component={Part5CompoundStatCalloutCisq}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-stat-callout-maintenance"
        component={Part5CompoundStatCalloutMaintenance}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-title-card"
        component={Part5CompoundTitleCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing-split-darning-vs-molding"
        component={ClosingSplitDarningVsMolding}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing-stat-callout-roi"
        component={ClosingStatCalloutRoi}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing-title-card"
        component={ClosingTitleCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="cold-open-08-closing-question-card"
        component={ColdOpen08ClosingQuestionCard}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-04-stat-callout-github"
        component={Part1Economics04StatCalloutGithub}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-06-stat-callout-uplevel"
        component={Part1Economics06StatCalloutUplevel}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-07-stat-callout-gitclear"
        component={Part1Economics07StatCalloutGitclear}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-09-context-degradation-chart"
        component={Part1Economics09ContextDegradationChart}
        durationInFrames={900}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-10-split-perception-reality"
        component={Part1Economics10SplitPerceptionReality}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-12-regeneration-infographic"
        component={Part1Economics12RegenerationInfographic}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part1-economics-13-crossover-zoom"
        component={Part1Economics13CrossoverZoom}
        durationInFrames={210}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift-07-hdl-timeline"
        component={Part2ParadigmShift07HdlTimeline}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift-08-split-manual-vs-specification"
        component={Part2ParadigmShift08SplitManualVsSpecification}
        durationInFrames={360}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part2-paradigm-shift-10-prompt-mold-visualization"
        component={Part2ParadigmShift10PromptMoldVisualization}
        durationInFrames={600}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-04-stat-callout-dora"
        component={Part3Mold04StatCalloutDora}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-12-three-pillars-diagram"
        component={Part3Mold12ThreePillarsDiagram}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part3-mold-13-subtitle-track"
        component={Part3Mold13SubtitleTrack}
        durationInFrames={8422}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-01-title-card"
        component={Part4Precision01TitleCard}
        durationInFrames={150}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part4-precision-07-spectrum-slider"
        component={Part4Precision07SpectrumSlider}
        durationInFrames={750}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-05-stat-callout-cisq"
        component={Part5Compound05StatCalloutCisq}
        durationInFrames={300}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="part5-compound-10-quote-card"
        component={Part5Compound10QuoteCard}
        durationInFrames={240}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="closing-07-cta-card"
        component={Closing07CtaCard}
        durationInFrames={180}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
