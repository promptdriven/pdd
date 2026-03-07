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

import { BEATS, VISUAL_SEQUENCE, Part2ParadigmShiftPropsType } from "./constants";
import {
  Part2ParadigmShift01TitleCard as TitleCard,
  defaultPart2ParadigmShift01TitleCardProps as defaultTitleCardProps,
} from "../01-TitleCard";
import {
  Part2ParadigmShift03MoldProductionInfographic as MoldProductionInfographic,
  defaultPart2ParadigmShift03MoldProductionInfographicProps as defaultMoldProductionInfographicProps,
} from "../03-MoldProductionInfographic";
import {
  Part2ParadigmShift05ValueMigrationDiagram as ValueMigrationDiagram,
  defaultPart2ParadigmShift05ValueMigrationDiagramProps as defaultValueMigrationDiagramProps,
} from "../05-ValueMigrationDiagram";
import {
  Part2ParadigmShift07HdlTimeline as HdlTimeline,
  defaultPart2ParadigmShift07HdlTimelineProps as defaultHdlTimelineProps,
} from "../Part2ParadigmShift07HdlTimeline";
import {
  Part2ParadigmShift08SplitManualVsSpecification as SplitManualVsSpecification,
  defaultPart2ParadigmShift08SplitManualVsSpecificationProps as defaultSplitManualVsSpecificationProps,
} from "../08-SplitManualVsSpecification";
import {
  Part2ParadigmShift10PromptMoldVisualization as PromptMoldVisualization,
  defaultPart2ParadigmShift10PromptMoldVisualizationProps as defaultPromptMoldVisualizationProps,
} from "../10-PromptMoldVisualization";
import {
  Part2ParadigmShift11SubtitleTrack as SubtitleTrack,
  defaultPart2ParadigmShift11SubtitleTrackProps as defaultSubtitleTrackProps,
} from "../11-SubtitleTrack";

export const Part2ParadigmShift: React.FC<Part2ParadigmShiftPropsType> = () => {
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
      <Audio src={staticFile("part2_paradigm_shift_narration.wav")} />

      {/* Visual 0: 01_title_card */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <TitleCard {...defaultTitleCardProps} />
        </Sequence>
      )}

      {/* Visual 1: 03_mold_production_infographic */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <MoldProductionInfographic {...defaultMoldProductionInfographicProps} />
        </Sequence>
      )}

      {/* Visual 2: 05_value_migration_diagram */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <ValueMigrationDiagram {...defaultValueMigrationDiagramProps} />
        </Sequence>
      )}

      {/* Visual 3: 07_hdl_timeline */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <HdlTimeline {...defaultHdlTimelineProps} />
        </Sequence>
      )}

      {/* Visual 4: 08_split_manual_vs_specification */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <SplitManualVsSpecification {...defaultSplitManualVsSpecificationProps} />
        </Sequence>
      )}

      {/* Visual 5: 10_prompt_mold_visualization */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <PromptMoldVisualization {...defaultPromptMoldVisualizationProps} />
        </Sequence>
      )}

      {/* Visual 6: 11_subtitle_track */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START}>
          <SubtitleTrack {...defaultSubtitleTrackProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
