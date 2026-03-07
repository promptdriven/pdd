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

import { BEATS, VISUAL_SEQUENCE, Part3MoldThreePartsPropsType } from "./constants";
import { TitleCard, defaultTitleCardProps } from "../01-TitleCard";
import {
  StatCalloutCoderabbit,
  defaultStatCalloutCoderabbitProps,
} from "../03-StatCalloutCoderabbit";
import {
  StatCalloutDora,
  defaultStatCalloutDoraProps,
} from "../04-StatCalloutDora";
import {
  SplitPromptVsCode,
  defaultSplitPromptVsCodeProps,
} from "../06-SplitPromptVsCode";
import {
  StatCalloutNlContext,
  defaultStatCalloutNlContextProps,
} from "../08-StatCalloutNlContext";
import {
  RatchetInfographic,
  defaultRatchetInfographicProps,
} from "../10-RatchetInfographic";
import {
  ThreePillarsDiagram,
  defaultThreePillarsDiagramProps,
} from "../12-ThreePillarsDiagram";
import {
  SubtitleTrack,
  defaultSubtitleTrackProps,
} from "../13-SubtitleTrack";

export const Part3MoldThreeParts: React.FC<Part3MoldThreePartsPropsType> = () => {
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
      <Audio src={staticFile("part3_mold_narration.wav")} />

      {/* Visual 0: 01_title_card */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <TitleCard {...defaultTitleCardProps} />
        </Sequence>
      )}

      {/* Visual 1: 03_stat_callout_coderabbit */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <StatCalloutCoderabbit {...defaultStatCalloutCoderabbitProps} />
        </Sequence>
      )}

      {/* Visual 2: 04_stat_callout_dora */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <StatCalloutDora {...defaultStatCalloutDoraProps} />
        </Sequence>
      )}

      {/* Visual 3: 06_split_prompt_vs_code */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <SplitPromptVsCode {...defaultSplitPromptVsCodeProps} />
        </Sequence>
      )}

      {/* Visual 4: 08_stat_callout_nl_context */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <StatCalloutNlContext {...defaultStatCalloutNlContextProps} />
        </Sequence>
      )}

      {/* Visual 5: 10_ratchet_infographic */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <RatchetInfographic {...defaultRatchetInfographicProps} />
        </Sequence>
      )}

      {/* Visual 6: 12_three_pillars_diagram */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START}>
          <ThreePillarsDiagram {...defaultThreePillarsDiagramProps} />
        </Sequence>
      )}

      {/* Visual 7: 13_subtitle_track (spans full section) */}
      <Sequence from={BEATS.VISUAL_07_START}>
        <SubtitleTrack {...defaultSubtitleTrackProps} />
      </Sequence>
    </AbsoluteFill>
  );
};
