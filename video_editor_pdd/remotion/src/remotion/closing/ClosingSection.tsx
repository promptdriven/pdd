import React from "react";
import {
  AbsoluteFill,
  Audio,
  Loop,
  OffthreadVideo,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";

import { BEATS, VISUAL_SEQUENCE, ClosingSectionPropsType } from "./constants";
import { Closing05SplitDarningVsMolding, defaultClosing05SplitDarningVsMoldingProps } from "../Closing05SplitDarningVsMolding/Closing05SplitDarningVsMolding";
import { Closing03StatCalloutRoi, defaultClosing03StatCalloutRoiProps } from "../Closing03StatCalloutRoi/Closing03StatCalloutRoi";
import { Closing01TitleCard, defaultClosing01TitleCardProps } from "../Closing01TitleCard/Closing01TitleCard";

export const ClosingSection: React.FC<ClosingSectionPropsType> = () => {
  const frame = useCurrentFrame();

  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      <Audio src={staticFile("closing_narration.wav")} />

      {/* Visual 0: closing_split_darning_vs_molding */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <Closing05SplitDarningVsMolding {...defaultClosing05SplitDarningVsMoldingProps} />
        </Sequence>
      )}

      {/* Visual 1: closing_stat_callout_roi */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <Closing03StatCalloutRoi {...defaultClosing03StatCalloutRoiProps} />
        </Sequence>
      )}

      {/* Visual 2: closing_title_card */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <Closing01TitleCard {...defaultClosing01TitleCardProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
