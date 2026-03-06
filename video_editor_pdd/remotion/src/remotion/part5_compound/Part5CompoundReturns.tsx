import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";

import { BEATS, VISUAL_SEQUENCE, Part5CompoundReturnsPropsType } from "./constants";
import { Part5Compound08SplitPatchingVsPdd, defaultPart5Compound08SplitPatchingVsPddProps } from "../Part5Compound08SplitPatchingVsPdd/Part5Compound08SplitPatchingVsPdd";
import { Part5Compound05StatCalloutCisq, defaultPart5Compound05StatCalloutCisqProps } from "../Part5Compound05StatCalloutCisq/Part5Compound05StatCalloutCisq";
import { Part5Compound03StatCalloutMaintenance, defaultPart5Compound03StatCalloutMaintenanceProps } from "../Part5Compound03StatCalloutMaintenance/Part5Compound03StatCalloutMaintenance";
import { Part5Compound01TitleCard, defaultPart5Compound01TitleCardProps } from "../Part5Compound01TitleCard/Part5Compound01TitleCard";

export const Part5CompoundReturns: React.FC<Part5CompoundReturnsPropsType> = () => {
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
      <Audio src={staticFile("part5_compound_narration.wav")} />

      {/* Visual 0: part5_compound_split_patching_vs_pdd */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <Part5Compound08SplitPatchingVsPdd {...defaultPart5Compound08SplitPatchingVsPddProps} />
        </Sequence>
      )}

      {/* Visual 1: part5_compound_stat_callout_cisq */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <Part5Compound05StatCalloutCisq {...defaultPart5Compound05StatCalloutCisqProps} />
        </Sequence>
      )}

      {/* Visual 2: part5_compound_stat_callout_maintenance */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <Part5Compound03StatCalloutMaintenance {...defaultPart5Compound03StatCalloutMaintenanceProps} />
        </Sequence>
      )}

      {/* Visual 3: part5_compound_title_card */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <Part5Compound01TitleCard {...defaultPart5Compound01TitleCardProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
