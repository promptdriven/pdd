import React from "react";
import { AbsoluteFill } from "remotion";
import { CANVAS, STEP_POSITIONS, STEPS } from "./constants";
import { StepCircle } from "./StepCircle";
import { StepLabel } from "./StepLabel";
import { PipelineArrows } from "./PipelineArrows";
import { PromptDocIcon } from "./PromptDocIcon";
import { WallIcons } from "./WallIcons";
import { TerminalIcon } from "./TerminalIcon";
import { DiffViewIcon } from "./DiffViewIcon";
import { LoopArrow } from "./LoopArrow";
import { ProgressBar } from "./ProgressBar";

export const defaultWhereToStart05RegenerateCompareLoopProps = {};

/**
 * Section 6.5: Regenerate & Compare Loop — Validating the Migration
 * 180 frames @ 30fps (6s)
 *
 * A horizontal pipeline of 4 steps: Generate prompt → Add tests → Regenerate → Compare.
 * Steps light up in sequence, then a loop arrow arcs back from step 4 to step 2.
 */
export const WhereToStart05RegenerateCompareLoop: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.background,
        overflow: "hidden",
      }}
    >
      {/* Step position placeholder circles (visible from frame 0) */}
      {STEP_POSITIONS.map((pos, i) => (
        <StepCircle
          key={`circle-${i}`}
          x={pos.x}
          y={pos.y}
          startFrame={STEPS[i].startFrame}
        />
      ))}

      {/* Connecting arrows between steps */}
      <PipelineArrows />

      {/* Step 1: Generate prompt (frame 20+) */}
      <div
        style={{
          position: "absolute",
          left: STEP_POSITIONS[0].x - 25,
          top: STEP_POSITIONS[0].y - 32,
        }}
      >
        <PromptDocIcon startFrame={STEPS[0].startFrame} />
      </div>
      <StepLabel
        label={STEPS[0].label}
        sublabel={STEPS[0].sublabel}
        x={STEP_POSITIONS[0].x}
        y={STEP_POSITIONS[0].y}
        startFrame={STEPS[0].startFrame}
      />

      {/* Step 2: Add tests (frame 50+) */}
      <div
        style={{
          position: "absolute",
          left: STEP_POSITIONS[1].x - 22,
          top: STEP_POSITIONS[1].y - 20,
        }}
      >
        <WallIcons startFrame={STEPS[1].startFrame} />
      </div>
      <StepLabel
        label={STEPS[1].label}
        sublabel={STEPS[1].sublabel}
        x={STEP_POSITIONS[1].x}
        y={STEP_POSITIONS[1].y}
        startFrame={STEPS[1].startFrame}
      />

      {/* Step 3: Regenerate (frame 80+) */}
      <div
        style={{
          position: "absolute",
          left: STEP_POSITIONS[2].x - 27,
          top: STEP_POSITIONS[2].y - 32,
        }}
      >
        <TerminalIcon startFrame={STEPS[2].startFrame} />
      </div>
      <StepLabel
        label={STEPS[2].label}
        sublabel={STEPS[2].sublabel}
        x={STEP_POSITIONS[2].x}
        y={STEP_POSITIONS[2].y}
        startFrame={STEPS[2].startFrame}
      />

      {/* Step 4: Compare (frame 110+) */}
      <div
        style={{
          position: "absolute",
          left: STEP_POSITIONS[3].x - 30,
          top: STEP_POSITIONS[3].y - 32,
        }}
      >
        <DiffViewIcon startFrame={STEPS[3].startFrame} />
      </div>
      <StepLabel
        label={STEPS[3].label}
        sublabel={STEPS[3].sublabel}
        x={STEP_POSITIONS[3].x}
        y={STEP_POSITIONS[3].y}
        startFrame={STEPS[3].startFrame}
      />

      {/* Loop arrow from step 4 back to step 2 (frame 140+) */}
      <LoopArrow />

      {/* Progress bar */}
      <ProgressBar />
    </AbsoluteFill>
  );
};

export default WhereToStart05RegenerateCompareLoop;
