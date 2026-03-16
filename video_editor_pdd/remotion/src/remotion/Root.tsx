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
import { Part2ParadigmShiftMain } from "./part2_paradigm_shift_main";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "part2_paradigm_shift:part2_paradigm_shift_main": {"specBaseName": "main", "dataPoints": null, "overlayConfig": null},
};

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
        durationInFrames={3}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Part1EconomicsSection"
        component={Part1EconomicsSection}
        durationInFrames={3}
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
