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

import { BEATS, VISUAL_SEQUENCE, Part4PrecisionTradeoffPropsType } from "./constants";
import { Part4Precision05SplitPromptDetailVsTests, defaultPart4Precision05SplitPromptDetailVsTestsProps } from "../Part4Precision05SplitPromptDetailVsTests";
import { Part4Precision04StatCalloutPromptCompression, defaultPart4Precision04StatCalloutPromptCompressionProps } from "../Part4Precision04StatCalloutPromptCompression";
import { Part4Precision01TitleCard, defaultPart4Precision01TitleCardProps } from "../Part4Precision01TitleCard";

export const Part4PrecisionTradeoff: React.FC<Part4PrecisionTradeoffPropsType> = () => {
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
      <Audio src={staticFile("part4_precision_narration.wav")} />

      {/* Visual 0: part4_precision_split_prompt_detail_vs_tests */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <Part4Precision05SplitPromptDetailVsTests {...defaultPart4Precision05SplitPromptDetailVsTestsProps} />
        </Sequence>
      )}

      {/* Visual 1: part4_precision_stat_callout_prompt_compression */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <Part4Precision04StatCalloutPromptCompression {...defaultPart4Precision04StatCalloutPromptCompressionProps} />
        </Sequence>
      )}

      {/* Visual 2: part4_precision_title_card */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <Part4Precision01TitleCard {...defaultPart4Precision01TitleCardProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
