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

import { BEATS, VISUAL_SEQUENCE, Part1EconomicsPropsType } from "./constants";
import {
  Part1Economics01TitleCard as TitleCard,
  defaultPart1Economics01TitleCardProps as defaultTitleCardProps,
} from "../01-TitleCard";
import {
  Part1Economics03CostCrossoverChart as CostCrossoverChart,
  defaultPart1Economics03CostCrossoverChartProps as defaultCostCrossoverChartProps,
} from "../03-CostCrossoverChart";
import {
  Part1Economics04StatCalloutGithub as StatCalloutGithub,
  defaultPart1Economics04StatCalloutGithubProps as defaultStatCalloutGithubProps,
} from "../04-StatCalloutGithub";
import {
  Part1Economics06StatCalloutUplevel as StatCalloutUplevel,
  defaultPart1Economics06StatCalloutUplevelProps as defaultStatCalloutUplevelProps,
} from "../Part1Economics06StatCalloutUplevel";
import {
  Part1Economics07StatCalloutGitclear as StatCalloutGitclear,
  defaultPart1Economics07StatCalloutGitclearProps as defaultStatCalloutGitclearProps,
} from "../07-StatCalloutGitclear";
import {
  Part1Economics09ContextDegradationChart as ContextDegradationChart,
  defaultPart1Economics09ContextDegradationChartProps as defaultContextDegradationChartProps,
} from "../09-ContextDegradationChart";
import {
  Part1Economics10SplitPerceptionReality as SplitPerceptionReality,
  defaultPart1Economics10SplitPerceptionRealityProps as defaultSplitPerceptionRealityProps,
} from "../10-SplitPerceptionReality";
import {
  Part1Economics12RegenerationInfographic as RegenerationInfographic,
  defaultPart1Economics12RegenerationInfographicProps as defaultRegenerationInfographicProps,
} from "../12-RegenerationInfographic";
import {
  Part1Economics13CrossoverZoom as CrossoverZoom,
  defaultPart1Economics13CrossoverZoomProps as defaultCrossoverZoomProps,
} from "../13-CrossoverZoom";
import {
  Part1Economics14SubtitleTrack as SubtitleTrack,
  defaultPart1Economics14SubtitleTrackProps as defaultSubtitleTrackProps,
} from "../14-SubtitleTrack";

export const Part1Economics: React.FC<Part1EconomicsPropsType> = () => {
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
      <Audio src={staticFile("part1_economics_narration.wav")} />

      {/* Visual 0: 01_title_card */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <TitleCard {...defaultTitleCardProps} />
        </Sequence>
      )}

      {/* Visual 1: 03_cost_crossover_chart */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <CostCrossoverChart {...defaultCostCrossoverChartProps} />
        </Sequence>
      )}

      {/* Visual 2: 04_stat_callout_github */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <StatCalloutGithub {...defaultStatCalloutGithubProps} />
        </Sequence>
      )}

      {/* Visual 3: 06_stat_callout_uplevel */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <StatCalloutUplevel {...defaultStatCalloutUplevelProps} />
        </Sequence>
      )}

      {/* Visual 4: 07_stat_callout_gitclear */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <StatCalloutGitclear {...defaultStatCalloutGitclearProps} />
        </Sequence>
      )}

      {/* Visual 5: 09_context_degradation_chart */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <ContextDegradationChart {...defaultContextDegradationChartProps} />
        </Sequence>
      )}

      {/* Visual 6: 10_split_perception_reality */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START}>
          <SplitPerceptionReality {...defaultSplitPerceptionRealityProps} />
        </Sequence>
      )}

      {/* Visual 7: 12_regeneration_infographic */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START}>
          <RegenerationInfographic {...defaultRegenerationInfographicProps} />
        </Sequence>
      )}

      {/* Visual 8: 13_crossover_zoom */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START}>
          <CrossoverZoom {...defaultCrossoverZoomProps} />
        </Sequence>
      )}

      {/* Visual 9: 14_subtitle_track */}
      {activeVisual === 9 && (
        <Sequence from={BEATS.VISUAL_09_START}>
          <SubtitleTrack {...defaultSubtitleTrackProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
