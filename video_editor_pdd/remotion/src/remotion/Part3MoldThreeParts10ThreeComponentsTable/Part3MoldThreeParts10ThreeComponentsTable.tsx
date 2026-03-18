import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";
import { EngineeringGrid } from "./EngineeringGrid";
import { MoldDiagram } from "./MoldDiagram";
import { SummaryTable } from "./SummaryTable";
import { ConflictLine } from "./ConflictLine";
import { CodeOutput } from "./CodeOutput";

/**
 * Section 3.10: Three Components Table
 *
 * The culminating visual for Part 3. A summary table materializes showing
 * all three components of the PDD mold (Prompt, Grounding, Tests).
 *
 * Animation sequence (480 frames @ 30fps = 16s):
 *   0-60    Full mold diagram with animated flow
 *   60-100  Mold slides left + shrinks; table bg fades in
 *   120-180 Table header types in
 *   180-310 Table rows slide in one by one
 *   310-370 Conflict line: "tests win. Always."
 *   370-420 Code output glows
 *   420-450 Code dims, mold stays bright
 *   450-480 Final caption
 */

export const defaultPart3MoldThreeParts10ThreeComponentsTableProps = {};

export const Part3MoldThreeParts10ThreeComponentsTable: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Engineering grid background */}
      <EngineeringGrid />

      {/* Mold diagram — visible from frame 0, animates position */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <MoldDiagram />
      </Sequence>

      {/* Summary table — container starts fading in at frame 60 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <SummaryTable />
      </Sequence>

      {/* Conflict resolution line */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ConflictLine />
      </Sequence>

      {/* Code output + final caption */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <CodeOutput />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts10ThreeComponentsTable;
