import React from "react";
import { Sequence, Audio, OffthreadVideo, staticFile } from "remotion";

import { Part2ParadigmShift01TitleCard } from "../Part2ParadigmShift01TitleCard";
import { Part2ParadigmShift03MoldProductionInfographic } from "../Part2ParadigmShift03MoldProductionInfographic";
import { Part2ParadigmShift05ValueMigrationDiagram } from "../Part2ParadigmShift05ValueMigrationDiagram";
import { Part2ParadigmShift07HdlTimeline } from "../Part2ParadigmShift07HdlTimeline";
import { Part2ParadigmShift08SplitManualVsSpecification } from "../Part2ParadigmShift08SplitManualVsSpecification";
import { Part2ParadigmShift10PromptMoldVisualization } from "../Part2ParadigmShift10PromptMoldVisualization";
import { Part2ParadigmShift11SubtitleTrack } from "../Part2ParadigmShift11SubtitleTrack";

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const offsetSeconds = 398.058667;
  const durationSeconds = 195.792;

  return (
    <Sequence from={0} durationInFrames={Math.ceil(durationSeconds * fps)}>
      <Audio src={staticFile("part2_paradigm_shift/narration.wav")} />
      <OffthreadVideo src={staticFile("veo/part2_paradigm_shift.mp4")} style={{ width: "100%", height: "100%" }} />
      <Part2ParadigmShift01TitleCard />
      <Part2ParadigmShift03MoldProductionInfographic />
      <Part2ParadigmShift05ValueMigrationDiagram />
      <Part2ParadigmShift07HdlTimeline />
      <Part2ParadigmShift08SplitManualVsSpecification />
      <Part2ParadigmShift10PromptMoldVisualization />
      <Part2ParadigmShift11SubtitleTrack />
    </Sequence>
  );
};

export default Part2ParadigmShiftSection;
