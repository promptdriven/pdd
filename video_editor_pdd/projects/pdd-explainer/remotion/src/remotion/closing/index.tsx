import React from "react";
import { Sequence } from "remotion";

import { Closing01SockCallbackSplit } from "../01_sock_callback_split";
import { Closing03CodeRegenerateWorkflow } from "../03_code_regenerate_workflow";
import { Closing04PddTriangle } from "../04_pdd_triangle";
import { Closing05DissolveRegenerateLoop } from "../05_dissolve_regenerate_loop";
import { Closing06MoldGlowFinale } from "../06_mold_glow_finale";
import { Closing07TheBeat } from "../07_the_beat";
import { Closing08MoldIsWhatMatters } from "../08_mold_is_what_matters";
import { Closing09FinalTitleCard } from "../09_final_title_card";

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 832.6399160000001;
  const durationSeconds = 20.903208;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Closing01SockCallbackSplit />
      <Closing03CodeRegenerateWorkflow />
      <Closing04PddTriangle />
      <Closing05DissolveRegenerateLoop />
      <Closing06MoldGlowFinale />
      <Closing07TheBeat />
      <Closing08MoldIsWhatMatters />
      <Closing09FinalTitleCard />
    </Sequence>
  );
};

export default ClosingSection;
