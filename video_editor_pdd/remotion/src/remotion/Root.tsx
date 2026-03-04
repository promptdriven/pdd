import React from "react";
import { Composition } from "remotion";

import { ColdOpenSection } from "./ColdOpenSection";
import { Part1Economics } from "./Part1Economics";
import { ColdOpenSection } from "./cold_open";
import { Part1EconomicsSection } from "./part1_economics";
import { Part2ParadigmShiftSection } from "./part2_paradigm_shift";
import { Part3MoldSection } from "./part3_mold";
import { Part4PrecisionSection } from "./part4_precision";
import { Part5CompoundSection } from "./part5_compound";
import { ClosingSection } from "./closing";

const FPS = 30;

export const RemotionRoot: React.FC = () => {
  return (
    <>      <Composition
        id="ColdOpenSection"
        component={ColdOpenSection}
        durationInFrames={459}
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

</>
  );
};
