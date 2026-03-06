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
import { Part3MoldSplitPromptVsCode, defaultPart3MoldSplitPromptVsCodeProps } from "../Part3MoldSplitPromptVsCode";
import { Part3MoldStatCalloutCoderabbit, defaultPart3MoldStatCalloutCoderabbitProps } from "../Part3MoldStatCalloutCoderabbit";
import { Part3MoldStatCalloutDora, defaultPart3MoldStatCalloutDoraProps } from "../Part3MoldStatCalloutDora";
import { Part3MoldStatCalloutNlContext, defaultPart3MoldStatCalloutNlContextProps } from "../Part3MoldStatCalloutNlContext";
import { Part3MoldTitleCard, defaultPart3MoldTitleCardProps } from "../Part3MoldTitleCard";

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

      {/* Visual 0: part3_mold_split_prompt_vs_code */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <Part3MoldSplitPromptVsCode {...defaultPart3MoldSplitPromptVsCodeProps} />
        </Sequence>
      )}

      {/* Visual 1: part3_mold_stat_callout_coderabbit */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <Part3MoldStatCalloutCoderabbit {...defaultPart3MoldStatCalloutCoderabbitProps} />
        </Sequence>
      )}

      {/* Visual 2: part3_mold_stat_callout_dora */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <Part3MoldStatCalloutDora {...defaultPart3MoldStatCalloutDoraProps} />
        </Sequence>
      )}

      {/* Visual 3: part3_mold_stat_callout_nl_context */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <Part3MoldStatCalloutNlContext {...defaultPart3MoldStatCalloutNlContextProps} />
        </Sequence>
      )}

      {/* Visual 4: part3_mold_title_card */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <Part3MoldTitleCard {...defaultPart3MoldTitleCardProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
