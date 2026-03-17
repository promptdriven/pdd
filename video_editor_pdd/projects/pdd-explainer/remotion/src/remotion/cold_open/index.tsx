import React from "react";
import { Sequence } from "remotion";

import { ColdOpen01SplitScreenHook } from "../01_split_screen_hook";
import { ColdOpen02ZoomOutAccumulated } from "../02_zoom_out_accumulated";
import { ColdOpen05CodeBlink } from "../05_code_blink";
import { ColdOpen06StillPatchingBeat } from "../06_still_patching_beat";
import { ColdOpen07PddTitleCard } from "../07_pdd_title_card";

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 0;
  const durationSeconds = 0.149333;

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <ColdOpen01SplitScreenHook />
      <ColdOpen02ZoomOutAccumulated />
      <ColdOpen05CodeBlink />
      <ColdOpen06StillPatchingBeat />
      <ColdOpen07PddTitleCard />
    </Sequence>
  );
};

export default ColdOpenSection;
