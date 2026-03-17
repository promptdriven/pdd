import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";
import { ChartBase } from "./ChartBase";
import { ForkedLine } from "./ForkedLine";
import { Annotations } from "./Annotations";
import { AccumulationArrow } from "./AccumulationArrow";
import { CrossingPoint } from "./CrossingPoint";
import { TerminalBreadcrumb } from "./TerminalBreadcrumb";

export const defaultPart1Economics09CrossingLinesMomentProps = {};

/**
 * Part1Economics09CrossingLinesMoment
 *
 * "Crossing Lines Moment" — The blue generation cost line crosses below
 * both the dashed total-cost line and the solid patch-cost line.
 * Features forked patch lines (small vs large codebase), METR annotations,
 * an accumulation arrow, and the "We are here." moment.
 *
 * Duration: 750 frames @ 30fps (25s)
 */
export const Part1Economics09CrossingLinesMoment: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Layer 1: Chart axes, grid, milestones, and original 3 lines */}
        <ChartBase />

        {/* Layer 2: Forked patch line at 2020 */}
        <ForkedLine />

        {/* Layer 3: "Same tools" annotation + METR data */}
        <Annotations />

        {/* Layer 4: Curved accumulation arrow */}
        <AccumulationArrow />

        {/* Layer 5: Blue crossing line pulse + "We are here." */}
        <CrossingPoint />

        {/* Layer 6: Terminal breadcrumb */}
        <TerminalBreadcrumb />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics09CrossingLinesMoment;
