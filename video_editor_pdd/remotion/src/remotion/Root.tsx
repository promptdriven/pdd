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
import { Part4PrecisionSplitPromptDetailVsTests } from "./part4_precision_split_prompt_detail_vs_tests";
import { Part4PrecisionStatCalloutPromptCompression } from "./part4_precision_stat_callout_prompt_compression";
import { Part4PrecisionTitleCard } from "./part4_precision_title_card";
import { Part5CompoundSplitPatchingVsPdd } from "./part5_compound_split_patching_vs_pdd";
import { Part5CompoundStatCalloutCisq } from "./part5_compound_stat_callout_cisq";
import { Part5CompoundStatCalloutMaintenance } from "./part5_compound_stat_callout_maintenance";
import { Part5CompoundTitleCard } from "./part5_compound_title_card";
import { ClosingSplitDarningVsMolding } from "./closing_split_darning_vs_molding";
import { ClosingStatCalloutRoi } from "./closing_stat_callout_roi";
import { ClosingTitleCard } from "./closing_title_card";

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="ColdOpenSection"
        component={ColdOpenSection}
        durationInFrames={467}
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
        id="part4-precision-split-prompt-detail-vs-tests"
        component={Part4PrecisionSplitPromptDetailVsTests}
        durationInFrames={PREVIEW_DURATION}
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
    </>
  );
};
