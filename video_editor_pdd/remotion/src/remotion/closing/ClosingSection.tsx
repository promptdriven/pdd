import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";

import { BEATS, VISUAL_SEQUENCE, ClosingSectionPropsType } from "./constants";
import {
  Closing01TitleCard,
  defaultClosing01TitleCardProps,
} from "../01-TitleCard";
import {
  Closing03StatCalloutRoi,
  defaultClosing03StatCalloutRoiProps,
} from "../03-StatCalloutRoi";
import {
  Closing05SplitDarningVsMolding,
  defaultClosing05SplitDarningVsMoldingProps,
} from "../05-SplitDarningVsMolding";
import {
  Closing07CtaCard,
  defaultClosing07CtaCardProps,
} from "../07-CtaCard";
import {
  Closing08SubtitleTrack,
  defaultClosing08SubtitleTrackProps,
} from "../08-SubtitleTrack";

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

      {/* Visual 0: 01_title_card */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <Closing01TitleCard {...defaultClosing01TitleCardProps} />
        </Sequence>
      )}

      {/* Visual 1: 03_stat_callout_roi */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <Closing03StatCalloutRoi {...defaultClosing03StatCalloutRoiProps} />
        </Sequence>
      )}

      {/* Visual 2: 05_split_darning_vs_molding */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <Closing05SplitDarningVsMolding
            {...defaultClosing05SplitDarningVsMoldingProps}
          />
        </Sequence>
      )}

      {/* Visual 3: 07_cta_card */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <Closing07CtaCard {...defaultClosing07CtaCardProps} />
        </Sequence>
      )}

      {/* Visual 4: 08_subtitle_track */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <Closing08SubtitleTrack {...defaultClosing08SubtitleTrackProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
