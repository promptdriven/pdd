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
import { TitleCard, defaultTitleCardProps } from "../01-TitleCard";
import {
  PrecisionCostUcurve,
  defaultPrecisionCostUcurveProps,
} from "../03-PrecisionCostUcurve";
import {
  StatCalloutPromptCompression,
  defaultStatCalloutPromptCompressionProps,
} from "../04-StatCalloutPromptCompression";
import {
  SplitPromptDetailVsTests,
  defaultSplitPromptDetailVsTestsProps,
} from "../05-SplitPromptDetailVsTests";
import {
  SpectrumSlider,
  defaultSpectrumSliderProps,
} from "../07-SpectrumSlider";
import {
  SubtitleTrack,
  defaultSubtitleTrackProps,
} from "../10-SubtitleTrack";

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

      {/* Visual 0: 01_title_card */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <TitleCard {...defaultTitleCardProps} />
        </Sequence>
      )}

      {/* Visual 1: 03_precision_cost_ucurve */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <PrecisionCostUcurve {...defaultPrecisionCostUcurveProps} />
        </Sequence>
      )}

      {/* Visual 2: 04_stat_callout_prompt_compression */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <StatCalloutPromptCompression {...defaultStatCalloutPromptCompressionProps} />
        </Sequence>
      )}

      {/* Visual 3: 05_split_prompt_detail_vs_tests */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <SplitPromptDetailVsTests {...defaultSplitPromptDetailVsTestsProps} />
        </Sequence>
      )}

      {/* Visual 4: 07_spectrum_slider */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <SpectrumSlider {...defaultSpectrumSliderProps} />
        </Sequence>
      )}

      {/* Visual 5: 10_subtitle_track */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <SubtitleTrack {...defaultSubtitleTrackProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
