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

import { BEATS, VISUAL_SEQUENCE, Part5CompoundReturnsPropsType } from "./constants";
import {
  TitleCard,
  defaultTitleCardProps,
} from "../01-TitleCard";
import {
  StatCalloutMaintenance,
  defaultStatCalloutMaintenanceProps,
} from "../03-StatCalloutMaintenance";
import {
  StatCalloutCisq,
  defaultStatCalloutCisqProps,
} from "../05-StatCalloutCisq";
import {
  CompoundDebtChart,
  defaultCompoundDebtChartProps,
} from "../06-CompoundDebtChart";
import {
  SplitPatchingVsPdd,
  defaultSplitPatchingVsPddProps,
} from "../08-SplitPatchingVsPdd";
import {
  QuoteCard,
  defaultQuoteCardProps,
} from "../10-QuoteCard";
import {
  SubtitleTrack,
  defaultSubtitleTrackProps,
} from "../11-SubtitleTrack";

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

      {/* Visual 0: 01_title_card */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <TitleCard {...defaultTitleCardProps} />
        </Sequence>
      )}

      {/* Visual 1: 03_stat_callout_maintenance */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <StatCalloutMaintenance {...defaultStatCalloutMaintenanceProps} />
        </Sequence>
      )}

      {/* Visual 2: 05_stat_callout_cisq */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <StatCalloutCisq {...defaultStatCalloutCisqProps} />
        </Sequence>
      )}

      {/* Visual 3: 06_compound_debt_chart */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <CompoundDebtChart {...defaultCompoundDebtChartProps} />
        </Sequence>
      )}

      {/* Visual 4: 08_split_patching_vs_pdd */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <SplitPatchingVsPdd {...defaultSplitPatchingVsPddProps} />
        </Sequence>
      )}

      {/* Visual 5: 10_quote_card */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <QuoteCard {...defaultQuoteCardProps} />
        </Sequence>
      )}

      {/* Visual 6: 11_subtitle_track (spans full section) */}
      <Sequence from={BEATS.VISUAL_06_START}>
        <SubtitleTrack {...defaultSubtitleTrackProps} />
      </Sequence>
    </AbsoluteFill>
  );
};
