import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { BackingPanel } from "./BackingPanel";
import { TriadBox } from "./TriadBox";
import { ArrowConnector } from "./ArrowConnector";
import { SynthesisLine } from "./SynthesisLine";
import {
  BG_COLOR,
  BOX1_X,
  BOX2_X,
  BOX3_X,
  BOX_Y,
  PROMPT_BORDER,
  PROMPT_FILL,
  PROMPT_ICON,
  PROMPT_GLOW,
  CODE_BORDER,
  CODE_FILL,
  CODE_ICON,
  CODE_GLOW,
  TESTS_BORDER,
  TESTS_FILL,
  TESTS_ICON,
  TESTS_GLOW,
  ARROW1_X1,
  ARROW1_X2,
  ARROW2_X1,
  ARROW2_X2,
  ARROW_Y,
  BOX1_ENTER,
  BOX2_ENTER,
  BOX3_ENTER,
  ARROW1_START,
  ARROW1_END,
  ARROW2_START,
  ARROW2_END,
  SYNTH_PHRASE1_START,
  SYNTH_PHRASE2_START,
  SYNTH_PHRASE3_START,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const defaultPart2ParadigmShift10PromptMoldVisualizationProps = {};

export const Part2ParadigmShift10PromptMoldVisualization: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall fade-out envelope
  const overallOpacity = interpolate(
    frame,
    [0, 1, FADEOUT_START, FADEOUT_END],
    [1, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part2_paradigm_shift.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Overlay content */}
      <AbsoluteFill style={{ opacity: overallOpacity }}>
        {/* Backing panel */}
        <BackingPanel />

        {/* Box 1 — PROMPT */}
        <TriadBox
          centerX={BOX1_X}
          centerY={BOX_Y}
          label="PROMPT"
          subtitle="your mold"
          borderColor={PROMPT_BORDER}
          fillColor={PROMPT_FILL}
          iconColor={PROMPT_ICON}
          glowColor={PROMPT_GLOW}
          icon="document"
          enterFrame={BOX1_ENTER}
          pulseHighlightFrame={SYNTH_PHRASE1_START}
        />

        {/* Arrow: PROMPT → CODE */}
        <ArrowConnector
          fromX={ARROW1_X1}
          toX={ARROW1_X2}
          y={ARROW_Y}
          label="generates"
          drawStartFrame={ARROW1_START}
          drawEndFrame={ARROW1_END}
        />

        {/* Box 2 — CODE */}
        <TriadBox
          centerX={BOX2_X}
          centerY={BOX_Y}
          label="CODE"
          subtitle="is plastic"
          borderColor={CODE_BORDER}
          fillColor={CODE_FILL}
          iconColor={CODE_ICON}
          glowColor={CODE_GLOW}
          icon="code"
          enterFrame={BOX2_ENTER}
          pulseHighlightFrame={SYNTH_PHRASE2_START}
        />

        {/* Arrow: CODE ↔ TESTS */}
        <ArrowConnector
          fromX={ARROW2_X1}
          toX={ARROW2_X2}
          y={ARROW_Y}
          label="validates"
          bidirectional
          drawStartFrame={ARROW2_START}
          drawEndFrame={ARROW2_END}
        />

        {/* Box 3 — TESTS */}
        <TriadBox
          centerX={BOX3_X}
          centerY={BOX_Y}
          label="TESTS"
          subtitle="lock behavior"
          borderColor={TESTS_BORDER}
          fillColor={TESTS_FILL}
          iconColor={TESTS_ICON}
          glowColor={TESTS_GLOW}
          icon="shield"
          enterFrame={BOX3_ENTER}
          pulseHighlightFrame={SYNTH_PHRASE3_START}
        />

        {/* Synthesis line */}
        <SynthesisLine />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift10PromptMoldVisualization;
